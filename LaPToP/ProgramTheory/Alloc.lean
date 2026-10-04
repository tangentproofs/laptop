import LaPToP.ProgramTheory.CompileB4
import B4.MM

/-!
# A memory allocator, in the language, proved

The allocator of `b4a/mm.b4a.org` (`B4.MM` in the b4 repository) rewritten in
the programming language: the heap is an array `M` of cells, a list of blocks,
each a three-cell header — `M p` the next block (`-1` at the last), `M (p+1)`
the size of its data, `M (p+2)` whether it is used (`1`) or free (`0`) —
followed by its data.

```
p:= 0. r:= -1.
while p ≥ 0 do
  if M (p+2) = 0 then
    q:= M p. g:= ⊤.
    while g do
      if q < 0 then g:= ⊥
      else if M (q+2) = 0 then
        M (p+1):= M (p+1) + 3 + M (q+1). M p:= M q. q:= M q
      else g:= ⊥ fi fi
    od.
    if M (p+1) ≥ n then
      if M (p+1) ≥ n + 4 then
        q:= p + 3 + n. M q:= M p. M (q+1):= M (p+1) - n - 3. M (q+2):= 0.
        M p:= q. M (p+1):= n
      else ok fi.
      M (p+2):= 1. r:= p + 3. p:= -1
    else p:= M p fi
  else p:= M p fi
od
```

asks for `n` cells: it takes the first free block big enough, merging each free
block it meets with the free blocks after it, and splitting off what is left
when that is at least four cells. It answers in `r` where the data starts, or
`-1` when no block is big enough. `M (r-1):= 0` frees it again.

`Alloc.alloc` is the same algorithm on a list of blocks: `B4.Heap.alloc 3 4`,
the one model of the allocator in the b4 repository, counted in cells (a header
of 3, a split at 4), of which `B4.MM.alloc` is the instance in bytes (12, 16);
`alloc_bytes` says the two agree, bytes being four times cells. **`alloc_sEval`** proves that the program, run on a
heap that holds blocks `bs`, leaves a heap that holds `(alloc n bs).2` and answers
`(alloc n bs).1` — in 32 bits, so that `CompileB4.load_correct` carries it to the
b4 machine (`alloc_on_b4`), and `CompileB4.eval_of_sEval` to the language's
semantics.
-/

namespace LaPToP.ProgramTheory.Alloc

open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Lang
open LaPToP.ProgramTheory.CompileB4

/-! ### The model -/

/-- A block: the size of its data, in cells, and whether it is used. -/
abbrev Blk := B4.Heap.Blk

/-- Absorb the free blocks at the front of `bs` into a free block of `size`
(headers of 3 cells). -/
abbrev absorb (size : ℕ) (bs : List Blk) : ℕ × List Blk := B4.Heap.absorb 3 size bs

theorem absorb_length (size : ℕ) (bs : List Blk) : (absorb size bs).2.length ≤ bs.length :=
  B4.Heap.absorb_length 3 size bs

/-- Take a free block of `size` for `n`, splitting off the rest when it is at
least four cells. -/
abbrev claim (n size : ℕ) : List Blk := B4.Heap.claim 3 4 n size

/-- **Allocation, on the blocks**: `B4.Heap.alloc` in cells, a header of 3 and a
split at 4 — the offset of the block taken, if one is big enough, and the
blocks after, merged as far as the search went. -/
abbrev alloc (n : ℕ) (bs : List Blk) : Option ℕ × List Blk := B4.Heap.alloc 3 4 n bs

/-- **Freeing, on the blocks**: the block at offset `o` is free. -/
abbrev free (o : ℕ) (bs : List Blk) : List Blk := B4.Heap.free 3 o bs

/-- **Cells are four bytes**: `B4.MM.alloc`, the model of `mm.b4a` in bytes, on
the blocks four times the size, does what this model does, with offsets four
times. -/
theorem alloc_bytes (n : ℕ) (bs : List Blk) :
    B4.MM.alloc (4 * n) (bs.map (B4.Heap.Blk.scale 4)) =
      ((alloc n bs).1.map (4 * ·), (alloc n bs).2.map (B4.Heap.Blk.scale 4)) :=
  B4.MM.alloc_cells n bs

/-- The cells blocks take. -/
def span (bs : List Blk) : ℕ := (bs.map fun b => 3 + b.size).sum

/-! ### The program -/

/-- Cell `j` of the heap, `0` outside it. -/
def rd (ms : List ℤ) (j : ℤ) : ℤ := if 0 ≤ j then ms.getD j.toNat 0 else 0

/-- **The heap holds blocks**: from `p`, a chain of headers, each block right after
the one before, the last one's next `-1`. -/
def Chain (ms : List ℤ) : ℤ → List Blk → Prop
  | p, [] => p = -1
  | p, b :: bs => 0 ≤ p ∧ p + 3 + b.size ≤ ms.length ∧ rd ms (p + 1) = b.size ∧
      rd ms (p + 2) = (if b.used then 1 else 0) ∧
      rd ms p = (if bs = [] then -1 else p + 3 + b.size) ∧ Chain ms (rd ms p) bs

/-- The variables: `n`, the heap `M`, `p`, `r`, `q`, `g`. -/
abbrev vn : ℕ := 0
abbrev vM : ℕ := 1
abbrev vp : ℕ := 2
abbrev vr : ℕ := 3
abbrev vq : ℕ := 4
abbrev vg : ℕ := 5

/-- Integer literal. -/
abbrev lit (k : ℤ) : Exp := .lit (.int k)
/-- `a + b`. -/
abbrev add (a b : Exp) : Exp := .bin .add a b
/-- `a - b`. -/
abbrev sub (a b : Exp) : Exp := .bin .sub a b
/-- `M e`. -/
abbrev cell (e : Exp) : Exp := .index (.var vM) e
/-- `a ≥ b`, as the compiler takes it. -/
abbrev ge (a b : Exp) : Exp := .un .not (.bin .lt a b)

/-- The merging loop's body. -/
def mergeBody : Stmt :=
  .cond (.bin .lt (.var vq) (lit 0)) (.assign vg (.lit (.bool false)))
    (.cond (.bin .eq (cell (add (.var vq) (lit 2))) (lit 0))
      (.seq (.store vM (add (.var vp) (lit 1))
          (add (add (cell (add (.var vp) (lit 1))) (lit 3)) (cell (add (.var vq) (lit 1)))))
        (.seq (.store vM (.var vp) (cell (.var vq))) (.assign vq (cell (.var vq)))))
      (.assign vg (.lit (.bool false))))

/-- `while g do ... od`: merge the free blocks after `p` into it. -/
def mergeLoop : Stmt := .loop (.var vg) mergeBody

/-- Split off what `n` leaves, when it is at least four cells. -/
def split : Stmt :=
  .seq (.assign vq (add (add (.var vp) (lit 3)) (.var vn)))
  (.seq (.store vM (.var vq) (cell (.var vp)))
  (.seq (.store vM (add (.var vq) (lit 1)) (sub (sub (cell (add (.var vp) (lit 1))) (.var vn)) (lit 3)))
  (.seq (.store vM (add (.var vq) (lit 2)) (lit 0))
  (.seq (.store vM (.var vp) (.var vq))
    (.store vM (add (.var vp) (lit 1)) (.var vn))))))

/-- Take block `p`: split it if it is big enough, mark it used, answer it, stop. -/
def take : Stmt :=
  .seq (.cond (ge (cell (add (.var vp) (lit 1))) (add (.var vn) (lit 4))) split .ok)
  (.seq (.store vM (add (.var vp) (lit 2)) (lit 1))
  (.seq (.assign vr (add (.var vp) (lit 3))) (.assign vp (lit (-1)))))

/-- The search loop's body. -/
def searchBody : Stmt :=
  .cond (.bin .eq (cell (add (.var vp) (lit 2))) (lit 0))
    (.seq (.assign vq (cell (.var vp)))
    (.seq (.assign vg (.lit (.bool true)))
    (.seq mergeLoop
      (.cond (ge (cell (add (.var vp) (lit 1))) (.var vn)) take (.assign vp (cell (.var vp)))))))
    (.assign vp (cell (.var vp)))

/-- The search. -/
def searchLoop : Stmt := .loop (ge (.var vp) (lit 0)) searchBody

/-- The allocator as source text: read by the language's parser for b4
(`parseB4`), it is `allocStmt` (checked by `interp --selftest`). -/
def allocSrc : String := "\n".intercalate
  ["p:= 0. r:= -1.",
   "while p ≥ 0 do",
   "  if M (p+2) = 0 then",
   "    q:= M p. g:= ⊤.",
   "    while g do",
   "      if q < 0 then g:= ⊥",
   "      else if M (q+2) = 0 then",
   "        M (p+1):= M (p+1) + 3 + M (q+1). M p:= M q. q:= M q",
   "      else g:= ⊥ fi fi",
   "    od.",
   "    if M (p+1) ≥ n then",
   "      if M (p+1) ≥ n + 4 then",
   "        q:= p + 3 + n. M q:= M p. M (q+1):= M (p+1) - n - 3. M (q+2):= 0.",
   "        M p:= q. M (p+1):= n",
   "      else ok fi.",
   "      M (p+2):= 1. r:= p + 3. p:= -1",
   "    else p:= M p fi",
   "  else p:= M p fi",
   "od"]

/-- **The allocator.** -/
def allocStmt : Stmt := .seq (.assign vp (lit 0)) (.seq (.assign vr (lit (-1))) searchLoop)

/-- **Freeing** the block whose data starts at `r`. -/
def freeStmt : Stmt := .store vM (sub (.var vr) (lit 1)) (lit 0)

/-! ### States -/

/-- A state of the program's variables, the rest as they are. -/
structure HS where
  /-- `n`, the cells asked for. -/
  n : ℤ
  /-- The heap `M`. -/
  ms : List ℤ
  /-- `p`, the block in hand. -/
  p : ℤ
  /-- `r`, the answer. -/
  r : ℤ
  /-- `q`, the block after. -/
  q : ℤ
  /-- `g`, whether merging goes on. -/
  g : Bool
  /-- The other variables. -/
  rest : St

/-- The state. -/
def HS.st (h : HS) : St
  | 0 => .int h.n
  | 1 => .list (h.ms.map .int)
  | 2 => .int h.p
  | 3 => .int h.r
  | 4 => .int h.q
  | 5 => .bool h.g
  | x + 6 => h.rest (x + 6)

/-- What the proofs ask of the layout: six variables, and `M` the one array, of
`cap` cells. -/
structure Ctx (L : Layout) (cap : ℕ) : Prop where
  ok : L.Ok
  n : L.n = 6
  arrays : L.arrays = [(vM, cap)]

theorem Ctx.arrayAt_M {L : Layout} {cap : ℕ} (c : Ctx L cap) :
    L.arrayAt vM = some (L.base + 4 * L.n, cap) := by
  simp [Layout.arrayAt, c.arrays, arrFrom]

theorem Ctx.arrayAt_ne {L : Layout} {cap : ℕ} (c : Ctx L cap) {x : ℕ} (hx : x ≠ vM) :
    L.arrayAt x = none := by
  simp [Layout.arrayAt, c.arrays, arrFrom, Ne.symm hx]

theorem Ctx.cap_lt {L : Layout} {cap : ℕ} (c : Ctx L cap) : cap < 16384 := by
  have := c.ok.2; rw [c.arrays, c.n] at this; simp [cellsOf, B4.MAXBYTE] at this; omega

@[simp] theorem st_n (h : HS) : h.st vn = .int h.n := rfl
@[simp] theorem st_M (h : HS) : h.st vM = .list (h.ms.map .int) := rfl
@[simp] theorem st_p (h : HS) : h.st vp = .int h.p := rfl
@[simp] theorem st_r (h : HS) : h.st vr = .int h.r := rfl
@[simp] theorem st_q (h : HS) : h.st vq = .int h.q := rfl
@[simp] theorem st_g (h : HS) : h.st vg = .bool h.g := rfl

@[simp] theorem eval_cell (h : HS) (e : Exp) :
    (cell e).eval h.st = .int (rd h.ms (e.eval h.st).toInt) := by
  simp only [Exp.eval, st_M, Value.index, Value.toList_list, rd]
  split
  · rw [show (default : Value) = .int 0 from rfl, List.getD_map]
  · rfl

theorem fits_cell {L : Layout} {cap : ℕ} (c : Ctx L cap) (h : HS) (e : Exp) :
    Fits L h.st (cell e) ↔ Fits L h.st e ∧ ∃ j, e.eval h.st = .int j ∧ 0 ≤ j ∧
      j.toNat < cap ∧ j.toNat < h.ms.length := by
  simp only [Fits, c.arrayAt_M, st_M, Option.some.injEq, Prod.mk.injEq, Value.list.injEq]
  constructor
  · rintro ⟨hf, _, _, _, j, ⟨-, rfl⟩, rfl, hj, h0, hc, hl⟩
    exact ⟨hf, j, hj, h0, hc, by simpa using hl⟩
  · rintro ⟨hf, j, hj, h0, hc, hl⟩
    exact ⟨hf, _, _, _, j, ⟨rfl, rfl⟩, rfl, hj, h0, hc, by simpa using hl⟩

@[simp] theorem upd_p (h : HS) (k : ℤ) : Function.update h.st vp (.int k) = { h with p := k }.st := by
  funext x; rcases x with _ | _ | _ | _ | _ | _ | x <;> rfl
@[simp] theorem upd_r (h : HS) (k : ℤ) : Function.update h.st vr (.int k) = { h with r := k }.st := by
  funext x; rcases x with _ | _ | _ | _ | _ | _ | x <;> rfl
@[simp] theorem upd_q (h : HS) (k : ℤ) : Function.update h.st vq (.int k) = { h with q := k }.st := by
  funext x; rcases x with _ | _ | _ | _ | _ | _ | x <;> rfl
@[simp] theorem upd_g (h : HS) (b : Bool) : Function.update h.st vg (.bool b) = { h with g := b }.st := by
  funext x; rcases x with _ | _ | _ | _ | _ | _ | x <;> rfl

theorem upd_M (h : HS) {j k : ℤ} (h0 : 0 ≤ j) (hj : j < h.ms.length) :
    Function.update h.st vM ((h.st vM).update [j] (.int k)) =
      { h with ms := h.ms.set j.toNat k }.st := by
  rw [st_M, Value.update_single ⟨h0, by simp; omega⟩, ← List.map_set]
  funext x; rcases x with _ | _ | _ | _ | _ | _ | x <;> rfl

theorem rd_set {ms : List ℤ} {j k : ℤ} (h0 : 0 ≤ j) (hj : j < ms.length) (i : ℤ) :
    rd (ms.set j.toNat k) i = if i = j then k else rd ms i := by
  unfold rd
  split_ifs with hi hij hij
  · subst hij; rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
  · omega
  · rfl

/-- What does not look at a cell is not changed by writing it. -/
theorem chain_frame {ms ms' : List ℤ} (hl : ms'.length = ms.length) :
    ∀ (bs : List Blk) (a : ℤ), (∀ j, a ≤ j → rd ms' j = rd ms j) → Chain ms a bs → Chain ms' a bs
  | [], _, _, h => h
  | b :: bs, a, hm, ⟨h0, h1, h2, h3, h4, h5⟩ => by
    refine ⟨h0, by rw [hl]; exact h1, by rw [hm _ (by omega)]; exact h2,
      by rw [hm _ (by omega)]; exact h3, by rw [hm _ le_rfl]; exact h4, ?_⟩
    rw [hm _ le_rfl]
    by_cases hb : bs = []
    · subst hb; exact h5
    · rw [ite_eq_right hb] at h4
      exact chain_frame hl bs _ (fun j hj => hm j (by omega)) h5

/-- **What comes before `p`**: blocks `pre`, from `0` to `p`, so that the heap
holds `pre` and then whatever chain starts at `p` — in any memory that agrees
below `p`. -/
def Pre (ms : List ℤ) (pre : List Blk) (p : ℤ) : Prop :=
  p = span pre ∧ ∀ ms' : List ℤ, ms'.length = ms.length → (∀ j, j < p → rd ms' j = rd ms j) →
    ∀ X, X ≠ [] → Chain ms' p X → Chain ms' 0 (pre ++ X)

theorem pre_nil (ms : List ℤ) : Pre ms [] 0 := ⟨by simp [span], fun _ _ _ _ _ h => h⟩

theorem Pre.mono {ms ms₁ : List ℤ} {pre : List Blk} {p : ℤ} (h : Pre ms pre p)
    (hl : ms₁.length = ms.length) (hm : ∀ j, j < p → rd ms₁ j = rd ms j) : Pre ms₁ pre p :=
  ⟨h.1, fun ms' hl' hm' X hX hc =>
    h.2 ms' (hl'.trans hl) (fun j hj => (hm' j hj).trans (hm j hj)) X hX hc⟩

/-- Past one more block. -/
theorem Pre.snoc {ms : List ℤ} {pre : List Blk} {p : ℤ} {b : Blk} (h : Pre ms pre p)
    (h0 : 0 ≤ p) (h1 : p + 3 + b.size ≤ ms.length) (h2 : rd ms (p + 1) = b.size)
    (h3 : rd ms (p + 2) = (if b.used then 1 else 0)) (h4 : rd ms p = p + 3 + b.size) :
    Pre ms (pre ++ [b]) (p + 3 + b.size) := by
  have hs : span (pre ++ [b]) = span pre + (3 + b.size) := by simp [span]
  refine ⟨by rw [h.1, hs]; push_cast; omega, fun ms' hl hm X hX hc => ?_⟩
  have := h.2 ms' hl (fun j hj => hm j (by omega)) (b :: X) (by simp)
    ⟨h0, by rw [hl]; exact h1, by rw [hm _ (by omega)]; exact h2, by rw [hm _ (by omega)]; exact h3,
      by rw [hm _ (by omega), ite_eq_right hX]; exact h4, by rw [hm _ (by omega), h4]; exact hc⟩
  simpa using this

/-- The last block. -/
theorem Pre.last {ms : List ℤ} {pre : List Blk} {p : ℤ} {b : Blk} (h : Pre ms pre p)
    (h0 : 0 ≤ p) (h1 : p + 3 + b.size ≤ ms.length) (h2 : rd ms (p + 1) = b.size)
    (h3 : rd ms (p + 2) = (if b.used then 1 else 0)) (h4 : rd ms p = -1) :
    Chain ms 0 (pre ++ [b]) :=
  h.2 ms rfl (fun _ _ => rfl) [b] (by simp) ⟨h0, h1, h2, h3, by simpa using h4, by rw [h4]; rfl⟩

/-! ### Running it, in 32 bits -/

theorem fits_lit {L : Layout} {h : HS} {k : ℤ} (hk : InRange k) : Fits L h.st (lit k) :=
  Or.inl ⟨k, rfl, hk⟩

theorem fits_bool {L : Layout} {h : HS} {b : Bool} : Fits L h.st (.lit (.bool b)) := Or.inr ⟨b, rfl⟩

section
variable {L : Layout} {cap : ℕ} (c : Ctx L cap) {d : ℕ}
include c

theorem sev_assign {x : ℕ} {e : Exp} {h h' : HS} (hx : x ≠ vM) (hxn : x < 6) (fe : Fits L h.st e)
    (ht : Function.update h.st x (e.eval h.st) = h'.st) : SEval L d (.assign x e) h.st h'.st :=
  ht ▸ .assign (by rw [c.n]; exact hxn) (c.arrayAt_ne hx) fe

theorem sev_store {i e : Exp} {h : HS} {j k : ℤ} (fi : Fits L h.st i) (fe : Fits L h.st e)
    (hi : i.eval h.st = .int j) (he : e.eval h.st = .int k) (h0 : 0 ≤ j) (hc : j.toNat < cap)
    (hj : j < h.ms.length) :
    SEval L d (.store vM i e) h.st { h with ms := h.ms.set j.toNat k }.st := by
  have := SEval.store (L := L) (d := d) (x := vM) (i := i) (e := e) (s := h.st)
    ((fits_cell c h i).2 ⟨fi, j, hi, h0, hc, by omega⟩) fe
  rwa [hi, he, Value.toInt_int, upd_M h h0 hj] at this

theorem fits_var {h : HS} {x : ℕ} (hx : x < 6) : Fits L h.st (.var x) := by
  simp only [Fits, c.n]; exact hx

end

section
variable {L : Layout} {st : St} {a b : Exp} {x y : ℤ}

theorem fits_lt (fa : Fits L st a) (fb : Fits L st b) (ea : a.eval st = .int x) (eb : b.eval st = .int y)
    (rx : InRange x) (ry : InRange y) : Fits L st (.bin .lt a b) := ⟨fa, fb, ⟨x, ea, rx⟩, ⟨y, eb, ry⟩⟩

theorem fits_eq (fa : Fits L st a) (fb : Fits L st b) (ea : a.eval st = .int x) (eb : b.eval st = .int y)
    (rx : InRange x) (ry : InRange y) : Fits L st (.bin .eq a b) := ⟨fa, fb, .inl ⟨⟨x, ea, rx⟩, ⟨y, eb, ry⟩⟩⟩

theorem fits_add (fa : Fits L st a) (fb : Fits L st b) (ea : a.eval st = .int x) (eb : b.eval st = .int y)
    (rx : InRange x) (ry : InRange y) (r : InRange (x + y)) : Fits L st (add a b) :=
  ⟨fa, fb, ⟨x, ea, rx⟩, ⟨y, eb, ry⟩, by rw [ea, eb]; exact r⟩

theorem fits_sub (fa : Fits L st a) (fb : Fits L st b) (ea : a.eval st = .int x) (eb : b.eval st = .int y)
    (rx : InRange x) (ry : InRange y) (r : InRange (x - y)) : Fits L st (sub a b) :=
  ⟨fa, fb, ⟨x, ea, rx⟩, ⟨y, eb, ry⟩, by rw [ea, eb]; exact r⟩

theorem fits_ge (fa : Fits L st a) (fb : Fits L st b) (ea : a.eval st = .int x) (eb : b.eval st = .int y)
    (rx : InRange x) (ry : InRange y) : Fits L st (ge a b) :=
  ⟨fits_lt fa fb ea eb rx ry, decide (x < y), by simp [Exp.eval, ea, eb, BinOp.apply]⟩

end

@[simp] theorem eval_var {st : St} {x : ℕ} : (Exp.var x).eval st = st x := rfl
@[simp] theorem eval_blit {st : St} {b : Bool} : (Exp.lit (.bool b)).eval st = .bool b := rfl
@[simp] theorem eval_lt {st : St} {a b : Exp} : (Exp.bin .lt a b).eval st =
    BinOp.apply .lt (a.eval st) (b.eval st) := rfl
@[simp] theorem eval_eq {st : St} {a b : Exp} : (Exp.bin .eq a b).eval st =
    BinOp.apply .eq (a.eval st) (b.eval st) := rfl
@[simp] theorem eval_add {st : St} {a b : Exp} : (add a b).eval st =
    BinOp.apply .add (a.eval st) (b.eval st) := rfl
@[simp] theorem eval_sub {st : St} {a b : Exp} : (sub a b).eval st =
    BinOp.apply .sub (a.eval st) (b.eval st) := rfl
@[simp] theorem eval_lit {st : St} {k : ℤ} : (lit k).eval st = .int k := rfl
@[simp] theorem eval_ge {st : St} {a b : Exp} : (ge a b).eval st =
    UnOp.apply .not (BinOp.apply .lt (a.eval st) (b.eval st)) := rfl

theorem fits_cell' {L : Layout} {cap : ℕ} (c : Ctx L cap) {h : HS} {e : Exp} {j : ℤ}
    (fe : Fits L h.st e) (he : e.eval h.st = .int j) (h0 : 0 ≤ j) (hj : j < h.ms.length)
    (hl : h.ms.length = cap) : Fits L h.st (cell e) :=
  (fits_cell c h e).2 ⟨fe, j, he, h0, by omega, by omega⟩

/-- In 32 bits. -/
theorem inR {k : ℤ} (h1 : -2 ^ 31 ≤ k) (h2 : k < 2 ^ 31) : InRange k := ⟨h1, h2⟩

/-! ### Merging -/

/-- **The merging loop** absorbs the free blocks after `p` into it, as `absorb`
does, writing only `p`'s header. -/
theorem merge_runs {L : Layout} {cap : ℕ} (c : Ctx L cap) {d : ℕ} : ∀ (bs : List Blk) (h : HS) (S : ℕ),
    h.ms.length = cap → h.g = true → 0 ≤ h.p → h.p + 3 + S ≤ h.ms.length →
    rd h.ms (h.p + 1) = S → rd h.ms h.p = h.q → (bs ≠ [] → h.q = h.p + 3 + S) →
    Chain h.ms h.q bs →
    ∃ ms' : List ℤ, SEval L d mergeLoop h.st { h with ms := ms', g := false, q := rd ms' h.p }.st ∧
      ms'.length = h.ms.length ∧ (∀ j, j ≠ h.p → j ≠ h.p + 1 → rd ms' j = rd h.ms j) ∧
      rd ms' (h.p + 1) = (absorb S bs).1 ∧ h.p + 3 + (absorb S bs).1 ≤ h.ms.length ∧
      rd ms' h.p = (if (absorb S bs).2 = [] then -1 else h.p + 3 + (absorb S bs).1) ∧
      Chain ms' (rd ms' h.p) (absorb S bs).2
  | [], h, S, hl, hg, hp, h1, hS, hpq, _, hch => by
    have hcap := c.cap_lt
    simp only [Chain] at hch
    refine ⟨h.ms, ?_, rfl, fun _ _ _ => rfl, by simpa [absorb, B4.Heap.absorb] using hS, by simpa [absorb, B4.Heap.absorb] using h1,
      by simp [absorb, B4.Heap.absorb, hpq, hch], by simp [absorb, B4.Heap.absorb, hpq, hch, Chain]⟩
    have e : ({ h with ms := h.ms, g := false, q := rd h.ms h.p } : HS) = { h with g := false } := by
      rw [hpq]
    rw [e]
    refine .loopT (fits_var c (by decide)) (by simp [hg]) ?_
      (.loopF (fits_var c (by decide)) (by simp))
    refine .condT (fits_lt (fits_var c (by decide)) (fits_lit (inR (by norm_num) (by norm_num))) rfl rfl
      (inR (by omega) (by omega)) (inR (by norm_num) (by norm_num))) (by simp [BinOp.apply, hch]) ?_
    exact sev_assign c (by decide) (by decide) fits_bool (by simp)
  | b :: bs, h, S, hl, hg, hp, h1, hS, hpq, hq, hch => by
    have hcap := c.cap_lt
    obtain ⟨q0, qlen, qs, qu, qn, qch⟩ := hch
    have hq' := hq (by simp)
    have fq : Fits L h.st (.var vq) := fits_var c (by decide)
    have fp : Fits L h.st (.var vp) := fits_var c (by decide)
    have hlt : Fits L h.st (.bin .lt (.var vq) (lit 0)) :=
      fits_lt fq (fits_lit (inR (by norm_num) (by norm_num))) rfl rfl (inR (by omega) (by omega))
        (inR (by norm_num) (by norm_num))
    have fq2 : Fits L h.st (add (.var vq) (lit 2)) :=
      fits_add fq (fits_lit (inR (by norm_num) (by norm_num))) rfl rfl (inR (by omega) (by omega))
        (inR (by norm_num) (by norm_num)) (inR (by omega) (by omega))
    have heq : Fits L h.st (.bin .eq (cell (add (.var vq) (lit 2))) (lit 0)) :=
      fits_eq (x := rd h.ms (h.q + 2)) (fits_cell' c (j := h.q + 2) fq2 (by simp [BinOp.apply]) (by omega) (by omega) hl)
        (fits_lit (inR (by norm_num) (by norm_num))) (by simp [BinOp.apply]) rfl
        (inR (by split at qu <;> omega) (by split at qu <;> omega)) (inR (by norm_num) (by norm_num))
    by_cases hu : b.used
    · -- a used block: stop
      rw [ite_eq_left hu] at qu
      refine ⟨h.ms, ?_, rfl, fun _ _ _ => rfl, by simp [absorb, B4.Heap.absorb, hu, hS], by simp [absorb, B4.Heap.absorb, hu]; omega,
        by simp [absorb, B4.Heap.absorb, hu, hpq, hq'], by
          simp only [absorb, B4.Heap.absorb, B4.Heap.absorb, hu, ite_true, hpq]; exact ⟨q0, qlen, qs, by simp [hu, qu], qn, qch⟩⟩
      have e : ({ h with ms := h.ms, g := false, q := rd h.ms h.p } : HS) = { h with g := false } := by
        rw [hpq]
      rw [e]
      refine .loopT (fits_var c (by decide)) (by simp [hg]) ?_
        (.loopF (fits_var c (by decide)) (by simp))
      refine .condF hlt (by simp [BinOp.apply]; exact decide_eq_false (by omega)) ?_
      refine .condF heq (by simp [BinOp.apply, qu]) ?_
      exact sev_assign c (by decide) (by decide) fits_bool (by simp)
    · -- a free block: absorb it
      rw [ite_eq_right hu] at qu
      have hl1 : h.p + 1 < h.ms.length := by omega
      have hqp : h.q ≠ h.p + 1 := by omega
      let ms₁ := h.ms.set (h.p + 1).toNat ((S : ℤ) + 3 + b.size)
      have r₁ := rd_set (ms := h.ms) (k := (S : ℤ) + 3 + b.size) (by omega) hl1
      have l₁ : ms₁.length = h.ms.length := by simp [ms₁]
      let nq := rd h.ms h.q
      let ms₂ := ms₁.set h.p.toNat nq
      have r₂ := rd_set (ms := ms₁) (k := nq) hp (by rw [l₁]; omega)
      have l₂ : ms₂.length = h.ms.length := by simp [ms₂, l₁]
      have frame : ∀ j, j ≠ h.p → j ≠ h.p + 1 → rd ms₂ j = rd h.ms j := fun j h1 h2 => by
        rw [r₂, ite_eq_right h1, r₁, ite_eq_right h2]
      have m2p : rd ms₂ h.p = nq := by rw [r₂, ite_eq_left rfl]
      have m2p1 : rd ms₂ (h.p + 1) = (S : ℤ) + 3 + b.size := by rw [r₂, ite_eq_right (by omega), r₁, ite_eq_left rfl]
      have hnext : bs ≠ [] → nq = h.p + 3 + ((S + 3 + b.size : ℕ) : ℤ) := fun hb => by
        simp only [nq, qn, ite_eq_right hb]; push_cast; omega
      have hch₂ : Chain ms₂ nq bs := by
        by_cases hb : bs = []
        · subst hb; exact qch
        · refine chain_frame l₂ bs nq (fun j hj => frame j ?_ ?_) qch
          · have := hnext hb; push_cast at this; omega
          · have := hnext hb; push_cast at this; omega
      let h₂ : HS := { h with ms := ms₂, q := nq }
      obtain ⟨ms', run', hl', hfr', hS', hb', hp', hch'⟩ := merge_runs c bs h₂ (S + 3 + b.size)
        (by simp [h₂, l₂, hl]) hg hp (by simp only [h₂, l₂]; push_cast; omega)
        (by simp only [h₂]; rw [m2p1]; push_cast; omega) m2p hnext hch₂
      have ha : absorb S (b :: bs) = absorb (S + 3 + b.size) bs := by simp [absorb, B4.Heap.absorb, hu]
      refine ⟨ms', ?_, by rw [hl', l₂], fun j h1 h2 => (hfr' j h1 h2).trans (frame j h1 h2),
        by rw [ha]; exact hS', by rw [ha, ← l₂]; exact hb', by rw [ha]; exact hp',
        by rw [ha]; exact hch'⟩
      refine .loopT (fits_var c (by decide)) (by simp [hg]) ?_ run'
      refine .condF hlt (by simp [BinOp.apply]; exact decide_eq_false (by omega)) ?_
      refine .condT heq (by simp [BinOp.apply, qu]) ?_
      have lit1 : Fits L h.st (lit 1) := fits_lit (inR (by norm_num) (by norm_num))
      have fp1 : Fits L h.st (add (.var vp) (lit 1)) := fits_add fp lit1 rfl rfl
        (inR (by omega) (by omega)) (inR (by norm_num) (by norm_num)) (inR (by omega) (by omega))
      have fq1 : Fits L h.st (add (.var vq) (lit 1)) := fits_add fq lit1 rfl rfl
        (inR (by omega) (by omega)) (inR (by norm_num) (by norm_num)) (inR (by omega) (by omega))
      have fc1 : Fits L h.st (cell (add (.var vp) (lit 1))) :=
        fits_cell' c (j := h.p + 1) fp1 (by simp [BinOp.apply]) (by omega) hl1 hl
      have fc2 : Fits L h.st (cell (add (.var vq) (lit 1))) :=
        fits_cell' c (j := h.q + 1) fq1 (by simp [BinOp.apply]) (by omega) (by omega) hl
      have fs : Fits L h.st (add (cell (add (.var vp) (lit 1))) (lit 3)) :=
        fits_add (x := S) fc1 (fits_lit (inR (by norm_num) (by norm_num))) (by simp [BinOp.apply, hS]) rfl
          (inR (by omega) (by omega)) (inR (by norm_num) (by norm_num)) (inR (by omega) (by omega))
      have fe : Fits L h.st (add (add (cell (add (.var vp) (lit 1))) (lit 3)) (cell (add (.var vq) (lit 1)))) :=
        fits_add (x := S + 3) (y := b.size) fs fc2 (by simp [BinOp.apply, hS]) (by simp [BinOp.apply, qs])
          (inR (by omega) (by omega)) (inR (by omega) (by omega)) (inR (by omega) (by omega))
      refine .seq (sev_store c (j := h.p + 1) (k := (S : ℤ) + 3 + b.size) fp1 fe (by simp [BinOp.apply])
        (by simp [BinOp.apply, hS, qs]) (by omega) (by omega) hl1) ?_
      let h₁ : HS := { h with ms := ms₁ }
      have hl₁ : h₁.ms.length = cap := by simp [h₁, l₁, hl]
      refine .seq (sev_store (h := h₁) c (j := h.p) (k := nq) (fits_var c (by decide))
        (fits_cell' c (j := h.q) (fits_var c (by decide)) rfl (by omega) (by simp [h₁, l₁]; omega) hl₁)
        rfl (by simp [h₁]; rw [r₁, ite_eq_right hqp]) hp (by omega) (by simp [h₁, l₁]; omega)) ?_
      let h₁' : HS := { h with ms := ms₂ }
      exact sev_assign (h := h₁') c (by decide) (by decide)
        (fits_cell' c (j := h.q) (fits_var c (by decide)) rfl (by omega) (by simp [h₁', l₂]; omega)
          (by simp [h₁', l₂, hl]))
        (by simp [h₁']; rw [frame _ (by omega) hqp])

/-! ### Taking a block -/

/-- A value that fits in 32 bits, by arithmetic. -/
macro "rng" : term => `(inR (by (try dsimp only); omega) (by (try dsimp only); omega))

/-- **Taking block `p`**, free and big enough: the heap from `p` holds what `claim`
makes of it, and nothing below `p` changes. -/
theorem take_runs {L : Layout} {cap : ℕ} (c : Ctx L cap) {d : ℕ} {h : HS} {S : ℕ} {rest : List Blk}
    (hl : h.ms.length = cap) (p0 : 0 ≤ h.p) (hpS : h.p + 3 + S ≤ h.ms.length)
    (hS : rd h.ms (h.p + 1) = S) (hnx : rd h.ms h.p = if rest = [] then -1 else h.p + 3 + S)
    (hch : Chain h.ms (rd h.ms h.p) rest) (hn : 0 ≤ h.n) (hnS : h.n ≤ S) :
    ∃ (ms' : List ℤ) (q' : ℤ), SEval L d take h.st { h with ms := ms', r := h.p + 3, p := -1, q := q' }.st ∧
      ms'.length = h.ms.length ∧ (∀ j, j < h.p → rd ms' j = rd h.ms j) ∧
      Chain ms' h.p (claim h.n.toNat S ++ rest) := by
  have hcap := c.cap_lt
  have lit1 : Fits L h.st (lit 1) := fits_lit (inR (by norm_num) (by norm_num))
  have fp : Fits L h.st (.var vp) := fits_var c (by decide)
  have fn : Fits L h.st (.var vn) := fits_var c (by decide)
  have fp1 : Fits L h.st (add (.var vp) (lit 1)) := fits_add fp lit1 rfl rfl
    (inR (by omega) (by omega)) (inR (by norm_num) (by norm_num)) (inR (by omega) (by omega))
  have fc1 : Fits L h.st (cell (add (.var vp) (lit 1))) :=
    fits_cell' c (j := h.p + 1) fp1 (by simp [BinOp.apply]) (by omega) (by omega) hl
  have fn4 : Fits L h.st (add (.var vn) (lit 4)) := fits_add fn (fits_lit (inR (by norm_num) (by norm_num)))
    rfl rfl (inR (by omega) (by omega)) (inR (by norm_num) (by norm_num)) (inR (by omega) (by omega))
  have fge : Fits L h.st (ge (cell (add (.var vp) (lit 1))) (add (.var vn) (lit 4))) :=
    fits_ge (x := S) (y := h.n + 4) fc1 fn4 (by simp [BinOp.apply, hS]) (by simp [BinOp.apply])
      (inR (by omega) (by omega)) (inR (by omega) (by omega))
  -- after the split, or not: mark used, answer, stop
  have finish : ∀ (h₁ : HS) (S₁ : ℕ) (X : List Blk), h₁.n = h.n → h₁.p = h.p → h₁.r = h.r →
      h₁.rest = h.rest → h₁.g = h.g → h₁.ms.length = h.ms.length → (∀ j, j < h.p → rd h₁.ms j = rd h.ms j) →
      h.p + 3 + S₁ ≤ h.ms.length → rd h₁.ms (h.p + 1) = S₁ →
      rd h₁.ms h.p = (if X = [] then -1 else h.p + 3 + S₁) → Chain h₁.ms (rd h₁.ms h.p) X →
      ∃ ms' : List ℤ, SEval L d (.seq (.store vM (add (.var vp) (lit 2)) (lit 1))
          (.seq (.assign vr (add (.var vp) (lit 3))) (.assign vp (lit (-1)))))
          h₁.st { h with ms := ms', r := h.p + 3, p := -1, q := h₁.q }.st ∧
        ms'.length = h.ms.length ∧ (∀ j, j < h.p → rd ms' j = rd h.ms j) ∧
        Chain ms' h.p (⟨S₁, true⟩ :: X) := by
    intro h₁ S₁ X en ep er erest eg elen ebelow hS₁ m1 m0 mch
    have hl₁ : h₁.ms.length = cap := by rw [elen, hl]
    have fp' : Fits L h₁.st (.var vp) := fits_var c (by decide)
    have fp2 : Fits L h₁.st (add (.var vp) (lit 2)) := fits_add fp' (fits_lit (inR (by norm_num) (by norm_num)))
      rfl rfl (inR (by omega) (by omega)) (inR (by norm_num) (by norm_num)) (inR (by omega) (by omega))
    have r₁ := rd_set (ms := h₁.ms) (k := 1) (j := h.p + 2) (by omega) (by omega)
    refine ⟨h₁.ms.set (h.p + 2).toNat 1, ?_, by simp [elen], fun j hj => by
      rw [r₁, ite_eq_right (by omega), ebelow j hj], ?_⟩
    · refine .seq (sev_store c (j := h.p + 2) (k := 1) fp2 (fits_lit (inR (by norm_num) (by norm_num)))
        (by simp [BinOp.apply, ep]) rfl (by omega) (by omega) (by omega)) ?_
      refine .seq (sev_assign (h := { h₁ with ms := h₁.ms.set (h.p + 2).toNat 1 })
        (h' := { h₁ with ms := h₁.ms.set (h.p + 2).toNat 1, r := h.p + 3 }) c (by decide) (by decide)
        (fits_add (fits_var c (by decide))
        (fits_lit (inR (by norm_num) (by norm_num))) rfl rfl (inR (by dsimp only; omega) (by dsimp only; omega))
        (inR (by norm_num) (by norm_num)) (inR (by dsimp only; omega) (by dsimp only; omega)))
        (by simp [BinOp.apply, ep])) ?_
      refine sev_assign c (by decide) (by decide) (fits_lit (inR (by norm_num) (by norm_num))) ?_
      simp only [eval_lit, upd_p]
      cases h₁; cases h; simp_all
    · refine ⟨p0, by simp; omega, by rw [r₁, ite_eq_right (by omega), m1], by rw [r₁, ite_eq_left rfl]; rfl,
        by rw [r₁, ite_eq_right (by omega), m0], ?_⟩
      rw [r₁, ite_eq_right (by omega)]
      by_cases hX : X = []
      · subst hX; rw [m0] at mch ⊢; exact mch
      · rw [m0, ite_eq_right hX] at mch ⊢
        exact chain_frame (by simp) X _ (fun j hj => by rw [r₁, ite_eq_right (by omega)]) mch
  have hclaim : claim h.n.toNat S = if h.n + 4 ≤ S then [⟨h.n.toNat, true⟩, ⟨S - h.n.toNat - 3, false⟩]
      else [⟨S, true⟩] := by
    unfold claim B4.Heap.claim; congr 1; apply propext; omega
  by_cases hsp : h.n + 4 ≤ S
  · -- split off the rest
    rw [hclaim, ite_eq_left hsp]
    obtain ⟨q, hq⟩ : ∃ q, q = h.p + 3 + h.n := ⟨_, rfl⟩
    let ms₂ := h.ms.set q.toNat (rd h.ms h.p)
    let ms₃ := ms₂.set (q + 1).toNat (S - h.n - 3)
    let ms₄ := ms₃.set (q + 2).toNat 0
    let ms₅ := ms₄.set h.p.toNat q
    let ms₆ := ms₅.set (h.p + 1).toNat h.n
    have l₂ : ms₂.length = h.ms.length := by simp [ms₂]
    have l₃ : ms₃.length = h.ms.length := by simp [ms₃, l₂]
    have l₄ : ms₄.length = h.ms.length := by simp [ms₄, l₃]
    have l₅ : ms₅.length = h.ms.length := by simp [ms₅, l₄]
    have l₆ : ms₆.length = h.ms.length := by simp [ms₆, l₅]
    have r₂ := rd_set (ms := h.ms) (k := rd h.ms h.p) (j := q) (by omega) (by omega)
    have r₃ := rd_set (ms := ms₂) (k := S - h.n - 3) (j := q + 1) (by omega) (by omega)
    have r₄ := rd_set (ms := ms₃) (k := 0) (j := q + 2) (by omega) (by omega)
    have r₅ := rd_set (ms := ms₄) (k := q) (j := h.p) (by omega) (by omega)
    have r₆ := rd_set (ms := ms₅) (k := h.n) (j := h.p + 1) (by omega) (by omega)
    have rd₆ : ∀ i, rd ms₆ i = if i = h.p + 1 then h.n else if i = h.p then q else if i = q + 2 then 0
        else if i = q + 1 then S - h.n - 3 else if i = q then rd h.ms h.p else rd h.ms i := fun i => by
      rw [r₆, r₅, r₄, r₃, r₂]
    let h₆ : HS := { h with ms := ms₆, q := q }
    obtain ⟨ms', run', l', below', ch'⟩ := finish h₆ h.n.toNat (⟨S - h.n.toNat - 3, false⟩ :: rest)
      rfl rfl rfl rfl rfl (by simp [h₆, l₆])
      (fun j hj => by simp only [h₆]; rw [rd₆]; split_ifs <;> first | rfl | omega)
      (by omega) (by simp only [h₆]; rw [rd₆, ite_eq_left rfl]; omega)
      (by simp only [h₆]; rw [rd₆, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by simp)]; omega)
      (by
        simp only [h₆]
        rw [rd₆, ite_eq_right (by omega), ite_eq_left rfl]
        refine ⟨by omega, by rw [l₆]; push_cast; omega, ?_, ?_, ?_, ?_⟩
        · rw [rd₆, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_left rfl]; push_cast; omega
        · rw [rd₆, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]; rfl
        · rw [rd₆, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_left rfl, hnx]
          dsimp only; split_ifs <;> omega
        · rw [rd₆, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_left rfl]
          by_cases hr : rest = []
          · subst hr; rw [hnx] at hch ⊢; exact hch
          · rw [hnx, ite_eq_right hr] at hch ⊢
            exact chain_frame l₆ rest _ (fun j hj => by rw [rd₆]; split_ifs <;> first | rfl | omega) hch)
    refine ⟨ms', q, ?_, l', fun j hj => below' j hj, by simpa using ch'⟩
    refine .seq (.condT fge (by simp [BinOp.apply, UnOp.apply, hS]; omega) ?_) run'
    have fv : ∀ {h' : HS} {x : ℕ}, x < 6 → Fits L h'.st (.var x) := fun hx => fits_var c hx
    refine .seq (sev_assign c (h' := { h with q := q }) (by decide) (by decide)
      (fits_add (x := h.p + 3) (fits_add fp (fits_lit rng) rfl rfl rng rng rng) fn (by simp [BinOp.apply]) rfl rng rng rng)
      (by simp [BinOp.apply, hq])) ?_
    refine .seq (sev_store (h := { h with q := q }) c (j := q) (k := rd h.ms h.p) (fv (by decide))
      (fits_cell' c (j := h.p) (fv (by decide)) rfl p0 (by dsimp only; omega) (by dsimp only; exact hl))
      rfl (by simp) (by omega) (by omega) (by dsimp only; omega)) ?_
    refine .seq (sev_store (h := { h with q := q, ms := ms₂ }) c (j := q + 1) (k := S - h.n - 3)
      (fits_add (fv (by decide)) (fits_lit rng) rfl rfl rng rng rng)
      (fits_sub (x := S - h.n) (fits_sub (x := S) (fits_cell' c (j := h.p + 1)
        (fits_add (fv (by decide)) (fits_lit rng) rfl rfl rng rng rng) (by simp [BinOp.apply])
        (by omega) (by simp [l₂]; omega) (by simp [l₂, hl]))
        (fv (by decide)) (by simp [BinOp.apply]; rw [r₂, ite_eq_right (by omega), hS]) rfl rng rng rng)
        (fits_lit rng) (by simp [BinOp.apply]; rw [r₂, ite_eq_right (by omega), hS]) rfl rng rng rng)
      (by simp [BinOp.apply]) (by simp [BinOp.apply]; rw [r₂, ite_eq_right (by omega), hS])
      (by omega) (by omega) (by simp [l₂]; omega)) ?_
    refine .seq (sev_store (h := { h with q := q, ms := ms₃ }) c (j := q + 2) (k := 0)
      (fits_add (fv (by decide)) (fits_lit rng) rfl rfl rng rng rng) (fits_lit rng)
      (by simp [BinOp.apply]) rfl (by omega) (by omega) (by simp [l₃]; omega)) ?_
    refine .seq (sev_store (h := { h with q := q, ms := ms₄ }) c (j := h.p) (k := q)
      (fv (by decide)) (fv (by decide)) rfl rfl p0 (by omega) (by simp [l₄]; omega)) ?_
    exact sev_store (h := { h with q := q, ms := ms₅ }) c (j := h.p + 1) (k := h.n)
      (fits_add (fv (by decide)) (fits_lit rng) rfl rfl rng rng rng) (fv (by decide))
      (by simp [BinOp.apply]) rfl (by omega) (by omega) (by simp [l₅]; omega)
  · -- take it whole
    rw [hclaim, ite_eq_right hsp]
    obtain ⟨ms', run', l', below', ch'⟩ := finish h S rest rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
      hpS hS hnx hch
    refine ⟨ms', h.q, .seq (.condF fge (by simp [BinOp.apply, UnOp.apply, hS]; omega) .ok) run', l', below', ch'⟩

/-! ### The search -/

theorem alloc_used {n : ℕ} {b : Blk} {bs : List Blk} (hu : b.used) :
    alloc n (b :: bs) = ((alloc n bs).1.map (· + 3 + b.size), b :: (alloc n bs).2) := by
  rw [alloc, B4.Heap.alloc]; simp [hu]

theorem alloc_free {n : ℕ} {b : Blk} {bs : List Blk} (hu : ¬b.used) :
    alloc n (b :: bs) = if n ≤ (absorb b.size bs).1 then
      (some 0, claim n (absorb b.size bs).1 ++ (absorb b.size bs).2)
    else ((alloc n (absorb b.size bs).2).1.map (· + 3 + (absorb b.size bs).1),
      ⟨(absorb b.size bs).1, false⟩ :: (alloc n (absorb b.size bs).2).2) := by
  rw [alloc, B4.Heap.alloc]; simp [hu]

section
variable {L : Layout} {cap : ℕ} (c : Ctx L cap) {h : HS}
include c

theorem fit_pge : -1 ≤ h.p → h.p < 2 ^ 20 → Fits L h.st (ge (.var vp) (lit 0)) := fun h1 h2 =>
  fits_ge (fits_var c (by decide)) (fits_lit rng) rfl rfl rng rng

theorem fit_cellp (hl : h.ms.length = cap) (h0 : 0 ≤ h.p) (h1 : h.p < h.ms.length) :
    Fits L h.st (cell (.var vp)) :=
  fits_cell' c (j := h.p) (fits_var c (by decide)) rfl h0 h1 hl

theorem fit_used (hl : h.ms.length = cap) (h0 : 0 ≤ h.p) (h1 : h.p + 2 < h.ms.length)
    (hu : 0 ≤ rd h.ms (h.p + 2) ∧ rd h.ms (h.p + 2) ≤ 1) :
    Fits L h.st (.bin .eq (cell (add (.var vp) (lit 2))) (lit 0)) := by
  have := c.cap_lt
  exact fits_eq (x := rd h.ms (h.p + 2)) (fits_cell' c (j := h.p + 2)
    (fits_add (fits_var c (by decide)) (fits_lit rng) rfl rfl rng rng rng) (by simp [BinOp.apply])
    (by omega) h1 hl) (fits_lit rng) (by simp [BinOp.apply]) rfl rng rng

theorem fit_size (hl : h.ms.length = cap) (h0 : 0 ≤ h.p) (h1 : h.p + 1 < h.ms.length)
    (hs : 0 ≤ rd h.ms (h.p + 1) ∧ rd h.ms (h.p + 1) < 2 ^ 20) (hn : 0 ≤ h.n ∧ h.n < 2 ^ 20) :
    Fits L h.st (ge (cell (add (.var vp) (lit 1))) (.var vn)) := by
  have := c.cap_lt
  exact fits_ge (x := rd h.ms (h.p + 1)) (fits_cell' c (j := h.p + 1)
    (fits_add (fits_var c (by decide)) (fits_lit rng) rfl rfl rng rng rng) (by simp [BinOp.apply])
    (by omega) h1 hl) (fits_var c (by decide)) (by simp [BinOp.apply]) rfl rng rng

end

theorem search_nil {L : Layout} {cap : ℕ} (c : Ctx L cap) {d : ℕ} {h : HS} {pre : List Blk}
    (hp : h.p = -1) (hr : h.r = -1) (hch : Chain h.ms 0 pre) :
    ∃ h' : HS, SEval L d searchLoop h.st h'.st ∧ h'.n = h.n ∧ h'.rest = h.rest ∧
      h'.ms.length = h.ms.length ∧ Chain h'.ms 0 (pre ++ (alloc h.n.toNat []).2) ∧
      h'.r = ((alloc h.n.toNat []).1.map fun o : ℕ => (span pre : ℤ) + (o : ℤ) + 3).getD (-1) :=
  ⟨h, .loopF (fit_pge c (by omega) (by omega)) (by simp [BinOp.apply, UnOp.apply, hp]), rfl, rfl, rfl,
    by simpa [alloc, B4.Heap.alloc] using hch, by simp [alloc, B4.Heap.alloc, hr]⟩

/-- **The search loop** does what `alloc` does, from the blocks at `p`, after
blocks `pre`. -/
theorem search_runs {L : Layout} {cap : ℕ} (c : Ctx L cap) {d : ℕ} :
    ∀ (k : ℕ) (bs : List Blk) (h : HS) (pre : List Blk),
    bs.length ≤ k → h.ms.length = cap → h.r = -1 → 0 ≤ h.n → h.n < 2 ^ 20 →
    Chain h.ms h.p bs → (bs = [] → Chain h.ms 0 pre) → (bs ≠ [] → Pre h.ms pre h.p) →
    ∃ h' : HS, SEval L d searchLoop h.st h'.st ∧ h'.n = h.n ∧ h'.rest = h.rest ∧
      h'.ms.length = h.ms.length ∧ Chain h'.ms 0 (pre ++ (alloc h.n.toNat bs).2) ∧
      h'.r = ((alloc h.n.toNat bs).1.map fun o : ℕ => (span pre : ℤ) + (o : ℤ) + 3).getD (-1) := by
  intro k
  induction k with
  | zero =>
    intro bs h pre hk hl hr hn0 hn1 hch hnil _
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact search_nil c hch hr (hnil rfl)
  | succ k ih =>
    intro bs h pre hk hl hr hn0 hn1 hch hnil hcons
    cases bs with
    | nil => exact search_nil c hch hr (hnil rfl)
    | cons b bs =>
    have hcap := c.cap_lt
    obtain ⟨p0, plen, ps, pu, pn, pch⟩ := hch
    have hpre := hcons (by simp)
    simp only [List.length_cons] at hk
    have fge := fit_pge c (h := h) (by omega) (by omega)
    have hfu := fit_used c (h := h) hl p0 (by omega) (by rw [pu]; split <;> omega)
    by_cases hu : b.used
    · rw [ite_eq_left hu] at pu
      obtain ⟨h', run', en, erest, elen, ech, er⟩ := ih bs { h with p := rd h.ms h.p } (pre ++ [b])
        (by omega) hl hr hn0 hn1 pch
        (fun hb => hpre.last p0 (by omega) ps (by rw [pu, ite_eq_left hu]) (by rw [pn, ite_eq_left hb]))
        (fun hb => by
          rw [pn, ite_eq_right hb]
          exact hpre.snoc p0 (by omega) ps (by rw [pu, ite_eq_left hu]) (by rw [pn, ite_eq_right hb]))
      refine ⟨h', .loopT fge (by simp [BinOp.apply, UnOp.apply]; first | omega | exact decide_eq_false (by omega))
        (.condF hfu (by simp [BinOp.apply, pu]) (sev_assign c (by decide) (by decide)
          (fit_cellp c hl p0 (by omega)) (by simp))) run', en, erest, elen, ?_, ?_⟩
      · rw [alloc_used hu]; simpa using ech
      · rw [er, alloc_used hu]
        have hs : span (pre ++ [b]) = span pre + (3 + b.size) := by simp [span]
        rcases (alloc h.n.toNat bs).1 with _ | o <;> simp [hs]
        omega
    · rw [ite_eq_right hu] at pu
      let h₁ : HS := { h with q := rd h.ms h.p }
      let h₂ : HS := { h with q := rd h.ms h.p, g := true }
      have hAl := absorb_length b.size bs
      obtain ⟨ms₁, mrun, ml, mfr, mS, mb, mnx, mch⟩ := merge_runs c (d := d) bs h₂ b.size hl rfl p0
        (by omega) ps rfl (fun hb => by simp only [h₂]; rw [pn, ite_eq_right hb]) pch
      rw [alloc_free hu]
      obtain ⟨A, hA⟩ : ∃ A, absorb b.size bs = A := ⟨_, rfl⟩
      rw [hA] at mS mb mnx mch hAl ⊢
      simp only [h₂] at mS mb mnx mch ml mfr
      let h₃ : HS := { h with ms := ms₁, q := rd ms₁ h.p, g := false }
      have hpre₁ : Pre ms₁ pre h.p := hpre.mono ml (fun j hj => mfr j (by omega) (by omega))
      have hu₁ : rd ms₁ (h.p + 2) = 0 := by rw [mfr _ (by omega) (by omega), pu]
      have hl₃ : h₃.ms.length = cap := by simp [h₃, ml, hl]
      have hb₃ : h.p + 3 + (A.1 : ℤ) ≤ (ms₁.length : ℤ) := by rw [ml]; exact mb
      have s₁ : SEval L d (.assign vq (cell (.var vp))) h.st h₁.st :=
        sev_assign c (h' := h₁) (by decide) (by decide) (fit_cellp c hl p0 (by omega)) (by simp [h₁])
      have s₂ : SEval L d (.assign vg (.lit (.bool true))) h₁.st h₂.st :=
        sev_assign c (h := h₁) (h' := h₂) (by decide) (by decide) fits_bool (by simp [h₁, h₂])
      have fsz := fit_size c (h := h₃) hl₃ p0 (by simp only [h₃]; omega)
        (by simp only [h₃]; rw [mS]; omega) ⟨hn0, hn1⟩
      by_cases hfit : h.n.toNat ≤ A.1
      · rw [ite_eq_left hfit]
        obtain ⟨ms₂, q', trun, tl, tbelow, tch⟩ := take_runs c (d := d) (h := h₃) (S := A.1) (rest := A.2)
          hl₃ p0 hb₃ mS mnx mch hn0 (by simp only [h₃]; omega)
        let h₄ : HS := { h₃ with ms := ms₂, r := h.p + 3, p := -1, q := q' }
        refine ⟨h₄, .loopT fge (by simp [BinOp.apply, UnOp.apply]; first | omega | exact decide_eq_false (by omega))
          (.condT hfu (by simp [BinOp.apply, pu]) ?_)
          (.loopF (fit_pge c (h := h₄) (by simp [h₄]) (by simp [h₄])) (by simp [h₄, BinOp.apply, UnOp.apply])),
          rfl, rfl, by simp [h₄, tl, h₃, ml], ?_, by simp [h₄, hpre.1]⟩
        · exact .seq s₁ (.seq s₂ (.seq mrun (.condT fsz
            (by simp [BinOp.apply, UnOp.apply]; simp only [h₂]; rw [mS]; omega) trun)))
        · exact hpre₁.2 ms₂ tl tbelow _ (by unfold claim B4.Heap.claim; split <;> simp) tch
      · rw [ite_eq_right hfit]
        have hu₁' : rd ms₁ (h.p + 2) = (if (false : Bool) = true then 1 else 0) := hu₁
        let h₄ : HS := { h with ms := ms₁, q := rd ms₁ h.p, g := false, p := rd ms₁ h.p }
        obtain ⟨h', run', en, erest, elen, ech, er⟩ := ih A.2 h₄ (pre ++ [⟨A.1, false⟩]) (by omega) hl₃ hr
          hn0 hn1 mch
          (fun hb => hpre₁.last p0 hb₃ mS hu₁' (by rw [mnx, ite_eq_left hb]))
          (fun hb => by
            simp only [h₄]; rw [mnx, ite_eq_right hb]
            exact hpre₁.snoc p0 hb₃ mS hu₁' (by rw [mnx, ite_eq_right hb]))
        refine ⟨h', .loopT fge (by simp [BinOp.apply, UnOp.apply]; first | omega | exact decide_eq_false (by omega))
          (.condT hfu (by simp [BinOp.apply, pu]) (.seq s₁ (.seq s₂ (.seq mrun (.condF fsz
            (by simp [BinOp.apply, UnOp.apply]; simp only [h₂]; rw [mS]; omega)
            (sev_assign c (h := h₃) (h' := h₄) (by decide) (by decide)
              (fit_cellp c hl₃ p0 (by simp only [h₃]; omega)) (by simp [h₃, h₄]))))))) run',
          en, erest, elen.trans ml, by simpa using ech, ?_⟩
        rw [er]
        have hs : span (pre ++ [⟨A.1, false⟩]) = span pre + (3 + A.1) := by simp [span]
        rcases (alloc h.n.toNat A.2).1 with _ | o <;> simp [hs]
        omega

/-! ### The allocator, and freeing -/

/-- **The allocator, proved**: on a heap holding blocks `bs`, asked for `n` cells,
it runs in 32 bits (`SEval`), leaving the heap holding `(alloc n bs).2` and
answering in `r` the start of the data of block `(alloc n bs).1`, or `-1`. -/
theorem alloc_sEval {L : Layout} {cap : ℕ} (c : Ctx L cap) {d : ℕ} (h : HS) (bs : List Blk)
    (hl : h.ms.length = cap) (hn0 : 0 ≤ h.n) (hn1 : h.n < 2 ^ 20) (hch : Chain h.ms 0 bs) :
    ∃ h' : HS, SEval L d allocStmt h.st h'.st ∧ h'.n = h.n ∧ h'.rest = h.rest ∧
      h'.ms.length = h.ms.length ∧ Chain h'.ms 0 (alloc h.n.toNat bs).2 ∧
      h'.r = ((alloc h.n.toNat bs).1.map fun o : ℕ => (o : ℤ) + 3).getD (-1) := by
  have hne : bs ≠ [] := by rintro rfl; simp [Chain] at hch
  obtain ⟨h', run, en, erest, elen, ech, er⟩ := search_runs c (d := d) bs.length bs
    { h with p := 0, r := -1 } [] le_rfl hl rfl hn0 hn1 hch (fun hb => (hne hb).elim)
    (fun _ => pre_nil _)
  refine ⟨h', .seq (sev_assign c (h' := { h with p := 0 }) (by decide) (by decide)
    (fits_lit rng) (by simp)) (.seq (sev_assign c (h := { h with p := 0 })
    (h' := { h with p := 0, r := -1 }) (by decide) (by decide) (fits_lit rng) (by simp)) run),
    en, erest, elen, by simpa using ech, by simpa [span] using er⟩

@[simp] theorem span_nil : span [] = 0 := rfl
@[simp] theorem span_cons (b : Blk) (bs : List Blk) : span (b :: bs) = 3 + b.size + span bs := by
  simp [span]
@[simp] theorem span_append (l₁ l₂ : List Blk) : span (l₁ ++ l₂) = span l₁ + span l₂ := by
  simp [span]

/-- A chain lies within the heap. -/
theorem chain_len {ms : List ℤ} : ∀ (bs : List Blk) (a : ℤ), Chain ms a bs → bs ≠ [] →
    a + span bs ≤ ms.length
  | [], _, _, h => (h rfl).elim
  | b :: bs, a, ⟨_, h1, _, _, h4, h5⟩, _ => by
    by_cases hb : bs = []
    · subst hb; simp; omega
    · rw [ite_eq_right hb] at h4; rw [h4] at h5
      have := chain_len bs _ h5 hb
      simp; omega

/-- Block `b` sits at offset `o`: after blocks that take `o` cells. -/
def At (bs : List Blk) (o : ℕ) : Prop := ∃ pre b post, bs = pre ++ b :: post ∧ o = span pre

theorem free_at : ∀ (pre : List Blk) (b : Blk) (post : List Blk),
    free (span pre) (pre ++ b :: post) = pre ++ { b with used := false } :: post
  | [], b, post => by simp [free, B4.Heap.free, span]
  | x :: pre, b, post => by
    rw [List.cons_append, free, B4.Heap.free, ite_eq_right (by simp), span_cons,
      show 3 + x.size + span pre - 3 - x.size = span pre by omega]
    have := free_at pre b post
    simp only [free] at this
    rw [this]; rfl

theorem chain_free {ms : List ℤ} : ∀ (pre : List Blk) (b : Blk) (post : List Blk) (a : ℤ),
    Chain ms a (pre ++ b :: post) →
    Chain (ms.set (a + span pre + 2).toNat 0) a (pre ++ { b with used := false } :: post)
  | [], b, post, a, ⟨h0, h1, h2, h3, h4, h5⟩ => by
    have r := rd_set (ms := ms) (k := 0) (j := a + 2) (by omega) (by omega)
    simp only [span, List.map_nil, List.sum_nil, Nat.cast_zero, add_zero, List.nil_append] at r ⊢
    refine ⟨h0, by simp; omega, by rw [r, ite_eq_right (by omega)]; exact h2,
      by rw [r, ite_eq_left rfl]; rfl, by rw [r, ite_eq_right (by omega)]; exact h4, ?_⟩
    rw [r, ite_eq_right (by omega)]
    by_cases hp : post = []
    · subst hp; rw [h4] at h5 ⊢; exact h5
    · rw [h4, ite_eq_right hp] at h5 ⊢
      exact chain_frame (by simp) post _ (fun j hj => by rw [r, ite_eq_right (by omega)]) h5
  | x :: pre, b, post, a, hch => by
    rw [List.cons_append] at hch ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hch
    have hs : span (x :: pre) = 3 + x.size + span pre := span_cons _ _
    have hne : pre ++ b :: post ≠ [] := by simp
    rw [ite_eq_right hne] at h4
    rw [h4] at h5
    have hb := chain_free pre b post _ h5
    have hlen : a + 3 + x.size + span pre + 2 < ms.length := by
      have := chain_len _ _ h5 hne; simp at this; omega
    have r := rd_set (ms := ms) (k := 0) (j := a + (span (x :: pre) : ℤ) + 2) (by omega)
      (by rw [hs]; push_cast; omega)
    refine ⟨h0, by simp; omega, by rw [r, ite_eq_right (by rw [hs]; push_cast; omega)]; exact h2,
      by rw [r, ite_eq_right (by rw [hs]; push_cast; omega)]; exact h3,
      by rw [r, ite_eq_right (by rw [hs]; push_cast; omega), h4, ite_eq_right (by simp)], ?_⟩
    rw [r, ite_eq_right (by rw [hs]; push_cast; omega), h4]
    rw [hs]; push_cast
    convert hb using 2; omega

/-- **Freeing, proved**: `M (r-1):= 0`, for `r` the start of the data of the
block at offset `o`, leaves the heap holding `free o bs`. -/
theorem free_sEval {L : Layout} {cap : ℕ} (c : Ctx L cap) {d : ℕ} (h : HS) (bs : List Blk) (o : ℕ)
    (hl : h.ms.length = cap) (hch : Chain h.ms 0 bs) (hat : At bs o) (hr : h.r = o + 3) :
    SEval L d freeStmt h.st { h with ms := h.ms.set (o + 2) 0 }.st ∧
      Chain (h.ms.set (o + 2) 0) 0 (free o bs) := by
  have hcap := c.cap_lt
  obtain ⟨pre, b, post, rfl, rfl⟩ := hat
  have hc := chain_free pre b post 0 hch
  have hlen := chain_len _ _ hch (by simp)
  simp at hlen
  simp only [zero_add] at hc
  have e : ((span pre : ℤ) + 2).toNat = span pre + 2 := by omega
  rw [e] at hc
  refine ⟨?_, by rw [free_at]; exact hc⟩
  have := sev_store c (d := d) (h := h) (i := sub (.var vr) (lit 1)) (e := lit 0) (j := span pre + 2) (k := 0)
    (fits_sub (fits_var c (by decide)) (fits_lit rng) rfl rfl (by rw [hr]; exact rng) rng
      (by rw [hr]; exact rng)) (fits_lit rng) (by simp [BinOp.apply, hr]; omega) rfl (by omega)
    (by omega) (by omega)
  rwa [e] at this

/-! ### On the language, and on b4 -/

/-- **In the language**: the allocator's execution is one the language's
semantics allows (`Eval`), with the heap as `alloc` says. -/
theorem alloc_eval {L : Layout} {cap : ℕ} (c : Ctx L cap) (h : HS) (bs : List Blk)
    (hl : h.ms.length = cap) (hn0 : 0 ≤ h.n) (hn1 : h.n < 2 ^ 20) (hch : Chain h.ms 0 bs) :
    ∃ h' : HS, @Eval ℕ Value L.env _ allocStmt.toProg h.st h'.st ∧
      Chain h'.ms 0 (alloc h.n.toNat bs).2 ∧
      h'.r = ((alloc h.n.toNat bs).1.map fun o : ℕ => (o : ℤ) + 3).getD (-1) := by
  obtain ⟨h', run, -, -, -, ech, er⟩ := alloc_sEval c (d := 0) h bs hl hn0 hn1 hch
  exact ⟨h', eval_of_sEval run, ech, er⟩

/-- **On b4**: the allocator compiled and loaded halts with the variables' and
the heap's cells holding what `alloc` says. -/
theorem alloc_on_b4 {L : Layout} {cap : ℕ} (c : Ctx L cap) (hF : L.Fit allocStmt) (h : HS)
    (bs : List Blk) (hl : h.ms.length = cap) (hn0 : 0 ≤ h.n) (hn1 : h.n < 2 ^ 20)
    (hch : Chain h.ms 0 bs) :
    ∃ h' : HS, Chain h'.ms 0 (alloc h.n.toNat bs).2 ∧
      h'.r = ((alloc h.n.toNat bs).1.map fun o : ℕ => (o : ℤ) + 3).getD (-1) ∧
      ∃ k, B4.getRST (B4.runN k (load L allocStmt h.st)) = 0 ∧
        VarsOk L (B4.high (B4.runN k (load L allocStmt h.st))) h'.st := by
  obtain ⟨h', run, -, -, -, ech, er⟩ := alloc_sEval c (d := 0) h bs hl hn0 hn1 hch
  exact ⟨h', ech, er, load_correct L c.ok run hF⟩

/-- A layout for the allocator: its code from `0x100`, the variables at `0x500`,
then the heap, `cap` cells. -/
def mmLayout (cap : ℕ) : Layout := Layout.build 0x500 6 [] [(vM, cap)]

theorem mmLayout_ctx {cap : ℕ} (h : cap ≤ 16000) : Ctx (mmLayout cap) cap :=
  ⟨⟨by simp [mmLayout, Layout.build, Layout.named],
    by simp [mmLayout, Layout.build, Layout.named, cellsOf, B4.MAXBYTE]; omega⟩, rfl, rfl⟩

theorem slen_mmLayout (cap : ℕ) : slen (mmLayout cap) allocStmt = 802 := by
  rw [slen_congr _ (mmLayout 0) (fun x => by
    simp only [Layout.arrayAt, mmLayout, Layout.build, Layout.named, arrFrom]; split <;> rfl)]
  rfl

theorem mmLayout_fit (cap : ℕ) : (mmLayout cap).Fit allocStmt :=
  ⟨trivial, by rw [slen_mmLayout]; simp [mmLayout, Layout.build, Layout.named, Layout.start,
    Layout.blocks, Layout.place], by decide, fun _ h => by simp [mmLayout, Layout.build,
    Layout.named] at h⟩

/-- **The allocator on b4**, with a heap of up to 16000 cells. -/
theorem alloc_on_b4' {cap : ℕ} (hcap : cap ≤ 16000) (h : HS) (bs : List Blk)
    (hl : h.ms.length = cap) (hn0 : 0 ≤ h.n) (hn1 : h.n < 2 ^ 20) (hch : Chain h.ms 0 bs) :
    ∃ h' : HS, Chain h'.ms 0 (alloc h.n.toNat bs).2 ∧
      h'.r = ((alloc h.n.toNat bs).1.map fun o : ℕ => (o : ℤ) + 3).getD (-1) ∧
      ∃ k, B4.getRST (B4.runN k (load (mmLayout cap) allocStmt h.st)) = 0 ∧
        VarsOk (mmLayout cap) (B4.high (B4.runN k (load (mmLayout cap) allocStmt h.st))) h'.st :=
  alloc_on_b4 (mmLayout_ctx hcap) (mmLayout_fit cap) h bs hl hn0 hn1 hch

end LaPToP.ProgramTheory.Alloc
