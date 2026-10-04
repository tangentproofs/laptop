import B4.Swarm
import LaPToP.ProgramTheory.InterpreterStmt
import Mathlib.Logic.Relation
import Mathlib.Data.List.GetD

/-!
# Compiling Hehner's language to the b4 machine

The integer fragment of the interpreter's language compiled to bytecode for the
b4 virtual machine (`B4.Basic`, formalized in `B4.Theory`), and the theorem that
the machine runs the compiled code as the language's semantics says, as long as
no value leaves 32 bits and the stack fits.

Variables live in 32-bit cells of memory above the code, one per variable;
integers are stored as two's complement words and the binaries `⊤`, `⊥` as `-1`
and `0`, as b4's comparisons produce them. An expression is computed on the data
stack; an assignment stores the top of the stack; `if` and `while` test the top
of the stack with `h0` and jump with `jm`.
-/

namespace LaPToP.ProgramTheory.CompileB4

open B4 Relation
open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Lang

/-! ### Words -/

/-- An integer that fits in 32 bits. -/
def InRange (k : ℤ) : Prop := -2 ^ 31 ≤ k ∧ k < 2 ^ 31

theorem toInt32_fromInt32 {k : ℤ} (h : InRange k) : toInt32 (fromInt32 k) = k := by
  obtain ⟨h1, h2⟩ := h
  unfold toInt32 fromInt32
  simp only [UInt32.toNat_ofNat']
  split_ifs <;> omega

theorem fromInt32_inj {a b : ℤ} (ha : InRange a) (hb : InRange b)
    (h : fromInt32 a = fromInt32 b) : a = b := by
  rw [← toInt32_fromInt32 ha, ← toInt32_fromInt32 hb, h]

/-- How a value is kept in a word: an integer as itself, a binary as `-1` or `0`. -/
def enc : Value → UInt32
  | .int k => fromInt32 k
  | .bool b => if b then 0xFFFFFFFF else 0
  | .list _ => 0

/-- The little-endian bytes of a word, as b4 lays it out. -/
def le4 (v : UInt32) : List UInt8 :=
  [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

@[simp] theorem length_le4 (v : UInt32) : (le4 v).length = 4 := rfl

/-- Bytes `bs` sit in memory `m` from address `a`. -/
def CodeAt (m : ℕ → UInt8) (a : ℕ) (bs : List UInt8) : Prop :=
  ∀ i, i < bs.length → m (a + i) = bs.getD i 0

theorem CodeAt.append {m : ℕ → UInt8} {a : ℕ} {b₁ b₂ : List UInt8} :
    CodeAt m a (b₁ ++ b₂) ↔ CodeAt m a b₁ ∧ CodeAt m (a + b₁.length) b₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by simp; omega)
      rwa [List.getD_append _ _ _ _ hi] at this
    · have := h (b₁.length + i) (by simp; omega)
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left] at this
      rwa [Nat.add_assoc]
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hlt : i < b₁.length
    · rw [h₁ i hlt, List.getD_append _ _ _ _ hlt]
    · have := h₂ (i - b₁.length) (by simp at hi; omega)
      rw [List.getD_append_right _ _ _ _ (by omega)]
      rw [← this]; congr 1; omega

theorem CodeAt.cast {m : ℕ → UInt8} {a b : ℕ} {bs : List UInt8} (h : CodeAt m a bs) (e : a = b) :
    CodeAt m b bs := e ▸ h

theorem word_le4 {m : ℕ → UInt8} {a : ℕ} {v : UInt32} (h : CodeAt m a (le4 v)) :
    word m a = v := by
  have h0 := h 0 (by simp [le4]); have h1 := h 1 (by simp [le4])
  have h2 := h 2 (by simp [le4]); have h3 := h 3 (by simp [le4])
  simp [le4] at h0 h1 h2 h3
  unfold word
  rw [h0, h1, h2, h3]
  exact bytes_word v

/-! ### Running -/

/-- The next instruction is not `io`: the machine's own step, which a swarm
lets it take as it is. -/
def NotIo (s : State) : Prop := s.mem.get! (getIP s) ≠ 0xFD

theorem notIo_of_hop {s : State} {op : UInt8} (hlo : 256 ≤ getIP s) (hop : high s (getIP s) = op)
    (hne : op ≠ 0xFD := by decide) : NotIo s := by
  unfold NotIo; rw [get!_ip s hlo, hop]; exact hne

/-- The machine goes from `s` to `s'`, running all the way, and never at an `io`. -/
def Steps (s s' : State) : Prop := ReflTransGen (fun a b => Running a ∧ NotIo a ∧ b = step a) s s'

theorem Steps.one {s : State} (h : Running s) (hn : NotIo s) : Steps s (step s) :=
  .single ⟨h, hn, rfl⟩

theorem _root_.B4.Same.running {s s' : State} (h : Same s s') (hr : Running s) : Running s' :=
  ⟨h.st.trans hr.1, h.db.trans hr.2⟩

/-- Where the variables are: cell `x` at `base + 4x`, for `x < n`. -/
structure Layout where
  /-- The first cell. -/
  base : ℕ
  /-- How many variables. -/
  n : ℕ
  /-- The named statements a program calls. -/
  defs : ℕ → Stmt := fun _ => .ok
  /-- Where each named statement's code starts. -/
  entry : ℕ → ℕ := fun _ => 0
  /-- The names that are defined. -/
  keys : List ℕ := []
  /-- The array variables, each with how many cells it has: their cells follow the
  variables', one array after another. -/
  arrays : List (ℕ × ℕ) := []
  /-- How many choices backtracking keeps at once. -/
  choices : ℕ := 0

/-- The address of variable `x`. -/
def Layout.addr (L : Layout) (x : ℕ) : ℕ := L.base + 4 * x

/-- Where array `x`'s cells start, and how many, the arrays `l` laid out from `a`. -/
def arrFrom : ℕ → List (ℕ × ℕ) → ℕ → Option (ℕ × ℕ)
  | _, [], _ => none
  | a, (y, cap) :: rest, x => if y = x then some (a, cap) else arrFrom (a + 4 * cap) rest x

/-- How many cells the arrays `l` take. -/
def cellsOf (l : List (ℕ × ℕ)) : ℕ := (l.map (·.2)).sum

/-- Where array variable `x`'s cells start, and how many there are. -/
def Layout.arrayAt (L : Layout) (x : ℕ) : Option (ℕ × ℕ) := arrFrom (L.base + 4 * L.n) L.arrays x

/-- Where the cells end: everything from here up is no variable's. -/
def Layout.top (L : Layout) : ℕ := L.base + 4 * L.n + 4 * cellsOf L.arrays

/-! ### Backtracking's runtime

Backtracking keeps choice points above the cells: a count, three cells a copy
uses, a failure flag, and the choice points, each the address of the code that
is the other choice and a copy of every cell. The code that keeps them is itself
written in the language, over one array `MEM` of the words from the first cell
up (`Layout.rt`): cell `k` is word `k`, the count is word `W`, and so on. -/

/-- How many words the cells take. -/
def Layout.W (L : Layout) : ℕ := L.n + cellsOf L.arrays

/-- The layout backtracking's runtime sees: one array, variable `0`, of every word
from the first cell up to the last choice point. -/
def Layout.rt (L : Layout) : Layout :=
  { base := L.base, n := 0, arrays := [(0, L.W + 5 + L.choices * (L.W + 1))] }

namespace RT

/-- Word `e` of memory. -/
abbrev mem (e : Exp) : Exp := .index (.var 0) e
/-- An integer literal. -/
abbrev lit (k : ℤ) : Exp := .lit (.int k)
/-- `a + b`. -/
abbrev add (a b : Exp) : Exp := .bin .add a b
/-- `a - b`. -/
abbrev sub (a b : Exp) : Exp := .bin .sub a b

/-- Where the last choice point would start (`w` the words the cells take), with
`k` choice points kept: word `w + 5 + k (w + 1)`. -/
def recAt (w : ℕ) : Exp := add (lit (w + 5)) (.bin .mul (mem (lit w)) (lit (w + 1)))

/-- Copy `MEM (w+3)` words from `MEM (w+1)` on to `MEM (w+2)` on. -/
def copy (w : ℕ) : Stmt :=
  .loop (.bin .lt (lit 0) (mem (lit (w + 3))))
    (.seq (.store 0 (mem (lit (w + 2))) (mem (mem (lit (w + 1)))))
    (.seq (.store 0 (lit (w + 1)) (add (mem (lit (w + 1))) (lit 1)))
    (.seq (.store 0 (lit (w + 2)) (add (mem (lit (w + 2))) (lit 1)))
      (.store 0 (lit (w + 3)) (sub (mem (lit (w + 3))) (lit 1))))))

/-- Keep a choice point: the other choice at `alt`, and a copy of the cells. -/
def save (w alt : ℕ) : Stmt :=
  .seq (.store 0 (recAt w) (lit alt))
  (.seq (.store 0 (lit (w + 1)) (lit 0))
  (.seq (.store 0 (lit (w + 2)) (add (recAt w) (lit 1)))
  (.seq (.store 0 (lit (w + 3)) (lit w))
  (.seq (copy w)
    (.store 0 (lit w) (add (mem (lit w)) (lit 1)))))))

/-- Take the last choice point back: its copy into the cells. -/
def pop (w : ℕ) : Stmt :=
  .seq (.store 0 (lit w) (sub (mem (lit w)) (lit 1)))
  (.seq (.store 0 (lit (w + 1)) (add (recAt w) (lit 1)))
  (.seq (.store 0 (lit (w + 2)) (lit 0))
  (.seq (.store 0 (lit (w + 3)) (lit w))
    (copy w))))

/-- No choice is left: say so. -/
def halt (w : ℕ) : Stmt := .store 0 (lit (w + 4)) (lit (-1))

end RT

/-- The cells lie in high memory. -/
def Layout.Ok (L : Layout) : Prop :=
  256 ≤ L.base ∧ L.base + 4 * L.n + 4 * cellsOf L.arrays + 16 ≤ MAXBYTE

theorem arrFrom_bounds : ∀ (l : List (ℕ × ℕ)) (a x a₀ cap : ℕ), arrFrom a l x = some (a₀, cap) →
    a ≤ a₀ ∧ a₀ + 4 * cap ≤ a + 4 * cellsOf l
  | [], _, _, _, _, h => by simp [arrFrom] at h
  | (y, c) :: rest, a, x, a₀, cap, h => by
    simp only [arrFrom] at h
    simp only [cellsOf, List.map_cons, List.sum_cons] at *
    split_ifs at h with hy
    · cases h; constructor <;> omega
    · have := arrFrom_bounds rest _ x a₀ cap h
      simp only [cellsOf] at this
      constructor <;> omega

theorem arrFrom_disjoint : ∀ (l : List (ℕ × ℕ)) (a x y a₀ c₀ a₁ c₁ : ℕ), x ≠ y →
    arrFrom a l x = some (a₀, c₀) → arrFrom a l y = some (a₁, c₁) →
    a₀ + 4 * c₀ ≤ a₁ ∨ a₁ + 4 * c₁ ≤ a₀
  | [], _, _, _, _, _, _, _, _, h, _ => by simp [arrFrom] at h
  | (z, c) :: rest, a, x, y, a₀, c₀, a₁, c₁, hxy, h₀, h₁ => by
    simp only [arrFrom] at h₀ h₁
    split_ifs at h₀ h₁ with hx hy hy
    · exact (hxy (hx.symm.trans hy)).elim
    · cases h₀; left; exact (arrFrom_bounds rest _ y a₁ c₁ h₁).1
    · cases h₁; right; exact (arrFrom_bounds rest _ x a₀ c₀ h₀).1
    · exact arrFrom_disjoint rest _ x y a₀ c₀ a₁ c₁ hxy h₀ h₁

/-- Where an array's cells are: after the variables', within the layout. -/
theorem Layout.arrayAt_bounds {L : Layout} {x a₀ cap : ℕ} (h : L.arrayAt x = some (a₀, cap)) :
    L.base + 4 * L.n ≤ a₀ ∧ a₀ + 4 * cap ≤ L.base + 4 * L.n + 4 * cellsOf L.arrays :=
  arrFrom_bounds _ _ _ _ _ h

/-- The arrays' cells hold their lists — as far as both go. -/
def ArrOk (L : Layout) (m : ℕ → UInt8) (st : St) : Prop :=
  ∀ x a₀ cap, L.arrayAt x = some (a₀, cap) → ∀ vs, st x = .list vs → ∀ j, j < cap →
    j < vs.length → word m (a₀ + 4 * j) = enc (vs.getD j default)

/-- The cells hold the values of the state: each variable's, and each array's. -/
def VarsOk (L : Layout) (m : ℕ → UInt8) (st : St) : Prop :=
  (∀ x < L.n, word m (L.addr x) = enc (st x)) ∧ ArrOk L m st

/-! ### Expressions -/

/-- An integer that fits. -/
def IsInt (v : Value) : Prop := ∃ k, v = .int k ∧ InRange k

/-- A value that has a word. -/
def Rep (v : Value) : Prop := IsInt v ∨ ∃ b, v = .bool b

/-- The opcode of a binary operator the compiler handles. -/
def binByte : BinOp → UInt8
  | .add => 0x80 | .sub => 0x81 | .mul => 0x82 | .div => 0x83 | .mod => 0x84 | .eq => 0x8A
  | .lt => 0x8B | .and => 0x86 | .or => 0x87 | _ => 0

/-- From an index on the stack to the address of its cell in an array at `a₀`:
`li 4 ml li a₀ ad`. -/
def addrCode (a₀ : ℕ) : List UInt8 :=
  ((0x97 :: le4 4) ++ [0x82]) ++ ((0x97 :: le4 (UInt32.ofNat a₀)) ++ [0x80])

@[simp] theorem length_addrCode (a₀ : ℕ) : (addrCode a₀).length = 12 := rfl

/-- The code of an expression: it pushes the expression's value. -/
def ecode (L : Layout) : Exp → List UInt8
  | .lit v => 0x97 :: le4 (enc v)
  | .var x => (0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x93]
  | .bin op a b => ecode L a ++ ecode L b ++ [binByte op]
  | .un .neg a => (0x97 :: le4 0) ++ ecode L a ++ [0x81]
  | .un .not a => ecode L a ++ [0x89]
  | .un .len (.var x) =>
    -- an array keeps its length: as many items as it has cells
    match L.arrayAt x with
    | some (_, cap) => 0x97 :: le4 (UInt32.ofNat cap)
    | none => []
  | .index (.var x) i =>
    match L.arrayAt x with
    | some (a₀, _) => ecode L i ++ addrCode a₀ ++ [0x93]
    | none => []
  | .cond c a b =>
    -- `c h0 → b; a; li 0 h0 → end; b`: hops are relative, so the code of an
    -- expression stays the same wherever it is put
    ecode L c ++ ([0x9C, UInt8.ofNat ((ecode L a).length + 9)] ++ (ecode L a ++
      ((0x97 :: le4 0) ++ ([0x9C, UInt8.ofNat ((ecode L b).length + 2)] ++ ecode L b))))
  | _ => []

/-- How deep the stack gets. -/
def depth : Exp → ℕ
  | .bin _ a b => max (depth a) (depth b + 1)
  | .un .neg a => depth a + 1
  | .un _ a => depth a
  | .index _ i => max (depth i) 2
  | .cond c a b => max (depth c) (max (depth a + 1) (depth b))
  | _ => 1

theorem depth_pos : ∀ e : Exp, 0 < depth e
  | .bin _ a b => by simp [depth]
  | .un .neg a => by simp [depth]
  | .un .not a => by simp only [depth]; exact depth_pos a
  | .un .len a => by simp only [depth]; exact depth_pos a
  | .index _ _ => by simp [depth]
  | .cond c _ _ => by simp only [depth]; have := depth_pos c; omega
  | .lit _ | .var _ | .nil | .cons _ _ => by simp [depth]

/-- **The expression can be computed in 32 bits**: it uses only the operators the
compiler handles, on integers and binaries as they expect, every variable has a
cell, and no value leaves 32 bits. -/
def Fits (L : Layout) (st : St) : Exp → Prop
  | .lit v => Rep v
  | .var x => x < L.n
  | .bin .add a b => Fits L st a ∧ Fits L st b ∧ IsInt (a.eval st) ∧ IsInt (b.eval st) ∧
      InRange ((a.eval st).toInt + (b.eval st).toInt)
  | .bin .sub a b => Fits L st a ∧ Fits L st b ∧ IsInt (a.eval st) ∧ IsInt (b.eval st) ∧
      InRange ((a.eval st).toInt - (b.eval st).toInt)
  | .bin .mul a b => Fits L st a ∧ Fits L st b ∧ IsInt (a.eval st) ∧ IsInt (b.eval st) ∧
      InRange ((a.eval st).toInt * (b.eval st).toInt)
  | .bin .div a b => Fits L st a ∧ Fits L st b ∧ IsInt (a.eval st) ∧ IsInt (b.eval st) ∧
      0 < (b.eval st).toInt ∧ InRange ((a.eval st).toInt.fdiv (b.eval st).toInt)
  | .bin .mod a b => Fits L st a ∧ Fits L st b ∧ IsInt (a.eval st) ∧ IsInt (b.eval st) ∧
      0 < (b.eval st).toInt ∧ InRange ((a.eval st).toInt.fmod (b.eval st).toInt)
  | .bin .eq a b => Fits L st a ∧ Fits L st b ∧ (IsInt (a.eval st) ∧ IsInt (b.eval st) ∨
      (∃ x, a.eval st = .bool x) ∧ ∃ y, b.eval st = .bool y)
  | .bin .lt a b => Fits L st a ∧ Fits L st b ∧ IsInt (a.eval st) ∧ IsInt (b.eval st)
  | .bin .and a b => Fits L st a ∧ Fits L st b ∧ (∃ x, a.eval st = .bool x) ∧
      ∃ y, b.eval st = .bool y
  | .bin .or a b => Fits L st a ∧ Fits L st b ∧ (∃ x, a.eval st = .bool x) ∧
      ∃ y, b.eval st = .bool y
  | .un .neg a => Fits L st a ∧ IsInt (a.eval st) ∧ InRange (-(a.eval st).toInt)
  | .un .not a => Fits L st a ∧ ∃ b, a.eval st = .bool b
  | .un .len (.var x) => ∃ a₀ cap vs, L.arrayAt x = some (a₀, cap) ∧ st x = .list vs ∧
      vs.length = cap ∧ cap < 2 ^ 31
  | .index (.var x) i => Fits L st i ∧ ∃ a₀ cap vs j, L.arrayAt x = some (a₀, cap) ∧
      st x = .list vs ∧ i.eval st = .int j ∧ 0 ≤ j ∧ j.toNat < cap ∧ j.toNat < vs.length
  | .cond c a b => Fits L st c ∧ (∃ x, c.eval st = .bool x) ∧ (ecode L a).length + 9 < 128 ∧
      (ecode L b).length + 2 < 128 ∧ (if (c.eval st).toBool then Fits L st a else Fits L st b)
  | _ => False

theorem enc_int (k : ℤ) : enc (.int k) = fromInt32 k := rfl

theorem toNat_ofNat_addr {a : ℕ} (h : a < MAXBYTE) : (UInt32.ofNat a).toNat = a := by
  rw [UInt32.toNat_ofNat']; unfold MAXBYTE at h; omega

/-- The machine computes what an operator does, on words that fit. -/
theorem enc_add {a b : ℤ} (ha : InRange a) (hb : InRange b) :
    fromInt32 (toInt32 (fromInt32 a) + toInt32 (fromInt32 b)) =
      enc (BinOp.apply .add (.int a) (.int b)) := by
  rw [toInt32_fromInt32 ha, toInt32_fromInt32 hb]; rfl

theorem enc_sub {a b : ℤ} (ha : InRange a) (hb : InRange b) :
    fromInt32 (toInt32 (fromInt32 a) - toInt32 (fromInt32 b)) =
      enc (BinOp.apply .sub (.int a) (.int b)) := by
  rw [toInt32_fromInt32 ha, toInt32_fromInt32 hb]; rfl

theorem enc_mul {a b : ℤ} (ha : InRange a) (hb : InRange b) :
    fromInt32 (toInt32 (fromInt32 a) * toInt32 (fromInt32 b)) =
      enc (BinOp.apply .mul (.int a) (.int b)) := by
  rw [toInt32_fromInt32 ha, toInt32_fromInt32 hb]; rfl

theorem enc_div {a b : ℤ} (ha : InRange a) (hb : InRange b) (hpos : 0 < b) :
    fromInt32 (toInt32 (fromInt32 a) / toInt32 (fromInt32 b)) =
      enc (BinOp.apply .div (.int a) (.int b)) := by
  rw [toInt32_fromInt32 ha, toInt32_fromInt32 hb]
  simp only [BinOp.apply, enc, Value.toInt_int, Int.fdiv_eq_ediv]
  rw [ite_eq_left (Or.inl hpos.le), sub_zero]

theorem enc_mod {a b : ℤ} (ha : InRange a) (hb : InRange b) (hpos : 0 < b) :
    fromInt32 (toInt32 (fromInt32 a) % toInt32 (fromInt32 b)) =
      enc (BinOp.apply .mod (.int a) (.int b)) := by
  rw [toInt32_fromInt32 ha, toInt32_fromInt32 hb]
  simp only [BinOp.apply, enc, Value.toInt_int, Int.fmod_eq_emod]
  rw [ite_eq_left (Or.inl hpos.le), add_zero]

/-- A word that is a nonzero integer is not `0`. -/
theorem fromInt32_ne_zero {b : ℤ} (hb : InRange b) (h : b ≠ 0) : fromInt32 b ≠ 0 := by
  intro e
  have : fromInt32 b = fromInt32 0 := by rw [e]; rfl
  exact h (fromInt32_inj hb ⟨by norm_num, by norm_num⟩ this)

theorem runOp_dv (s : State) (h : (dpop s).1 ≠ 0) : runOp s 0x83 =
    (let (y, s) := dpop s; let (x, s) := dpop s; dpush s (fromInt32 (toInt32 x / toInt32 y))) := by
  simp [runOp, h]

theorem runOp_md (s : State) (h : (dpop s).1 ≠ 0) : runOp s 0x84 =
    (let (y, s) := dpop s; let (x, s) := dpop s; dpush s (fromInt32 (toInt32 x % toInt32 y))) := by
  simp [runOp, h]

theorem enc_eq {a b : ℤ} (ha : InRange a) (hb : InRange b) :
    (if fromInt32 a == fromInt32 b then (0xFFFFFFFF : UInt32) else 0) =
      enc (BinOp.apply .eq (.int a) (.int b)) := by
  simp only [BinOp.apply, enc]
  by_cases h : a = b
  · subst h; simp
  · have : fromInt32 a ≠ fromInt32 b := fun e => h (fromInt32_inj ha hb e)
    simp [this, h]

theorem enc_lt {a b : ℤ} (ha : InRange a) (hb : InRange b) :
    (if toInt32 (fromInt32 a) < toInt32 (fromInt32 b) then (0xFFFFFFFF : UInt32) else 0) =
      enc (BinOp.apply .lt (.int a) (.int b)) := by
  rw [toInt32_fromInt32 ha, toInt32_fromInt32 hb]
  simp only [BinOp.apply, enc, Value.toInt_int]
  by_cases h : a < b <;> simp [h]

theorem enc_neg {a : ℤ} (ha : InRange a) :
    fromInt32 (toInt32 0 - toInt32 (fromInt32 a)) = enc (UnOp.apply .neg (.int a)) := by
  rw [toInt32_fromInt32 ha]
  simp [UnOp.apply, enc, toInt32]

theorem enc_not (b : Bool) : enc (.bool b) ^^^ 0xFFFFFFFF = enc (UnOp.apply .not (.bool b)) := by
  cases b <;> decide

/-- What every expression lemma assumes of the machine. -/
structure At (L : Layout) (st : St) (s : State) (bs : List UInt8) (d : ℕ) : Prop where
  wf : WF s
  run : Running s
  lo : 256 ≤ getIP s
  hi : getIP s + bs.length + 8 < MAXBYTE
  code : CodeAt (high s) (getIP s) bs
  vars : VarsOk L (high s) st
  stack : (dstack s).length + d ≤ STACKSZ

/-- What an expression's code does. -/
def ERuns (L : Layout) (st : St) (e : Exp) : Prop :=
  ∀ s, Fits L st e → At L st s (ecode L e) (depth e) →
    ∃ s', Steps s s' ∧ WF s' ∧ getIP s' = getIP s + (ecode L e).length ∧
      dstack s' = dstack s ++ [enc (e.eval st)] ∧ Same s s'

/-- Run two pieces of code one after the other, the first an expression's. -/
theorem At.after {L : Layout} {st : St} {s s₁ : State} {bs₁ bs₂ : List UInt8} {d₁ d₂ : ℕ} {v : UInt32}
    (h : At L st s (bs₁ ++ bs₂) d₁) (hd : d₂ + 1 ≤ d₁) (w : WF s₁) (i : getIP s₁ = getIP s + bs₁.length)
    (ds : dstack s₁ = dstack s ++ [v]) (sm : Same s s₁) : At L st s₁ bs₂ d₂ := by
  have hc := CodeAt.append.mp h.code
  refine ⟨w, sm.running h.run, by rw [i]; exact Nat.le_add_right_of_le h.lo, ?_, ?_, ?_, ?_⟩
  · have := h.hi; simp at this; rw [i]; omega
  · rw [sm.high, i]; exact hc.2
  · rw [sm.high]; exact h.vars
  · have := h.stack; rw [ds]; simp; omega

theorem At.left {L : Layout} {st : St} {s : State} {bs₁ bs₂ : List UInt8} {d₁ d₂ : ℕ}
    (h : At L st s (bs₁ ++ bs₂) d₁) (hd : d₂ ≤ d₁) : At L st s bs₁ d₂ :=
  ⟨h.wf, h.run, h.lo, by have := h.hi; simp at this; omega, (CodeAt.append.mp h.code).1, h.vars,
    by have := h.stack; omega⟩

theorem run_bin (L : Layout) (st : St) (op : BinOp) (a b : Exp) (byte : UInt8)
    (f : UInt32 → UInt32 → UInt32)
    (hr : ∀ s, (dpop s).1 = enc (b.eval st) →
      runOp s byte = (let (y, s) := dpop s; let (x, s) := dpop s; dpush s (f x y)))
    (hb : binByte op = byte) (hne : byte ≠ 0xFD)
    (hval : f (enc (a.eval st)) (enc (b.eval st)) = enc ((Exp.bin op a b).eval st))
    (iha : ERuns L st a) (ihb : ERuns L st b) (fa : Fits L st a) (fb : Fits L st b)
    (s : State) (h : At L st s (ecode L (.bin op a b)) (depth (.bin op a b))) :
    ∃ s', Steps s s' ∧ WF s' ∧ getIP s' = getIP s + (ecode L (.bin op a b)).length ∧
      dstack s' = dstack s ++ [enc ((Exp.bin op a b).eval st)] ∧ Same s s' := by
  simp only [ecode, depth] at h ⊢
  rw [List.append_assoc] at h
  obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := iha s fa (h.left (le_max_left _ _))
  have h₁ := h.after (d₂ := depth b) (by have := le_max_right (depth a) (depth b + 1); omega) w₁ i₁ d₁ sm₁
  obtain ⟨s₂, r₂, w₂, i₂, d₂, sm₂⟩ := ihb s₁ fb (h₁.left le_rfl)
  have h₂ := h₁.after (d₂ := 0) (depth_pos b) w₂ i₂ d₂ sm₂
  have hop : high s₂ (getIP s₂) = byte := by
    have := h₂.code 0 (by simp); simpa [hb] using this
  have hd₂ : dstack s₂ = dstack s ++ [enc (a.eval st), enc (b.eval st)] := by rw [d₂, d₁]; simp
  obtain ⟨e₂, -⟩ := dpop_same s₂ (dstack s ++ [enc (a.eval st)]) (enc (b.eval st)) w₂
    (by rw [hd₂]; simp)
  obtain ⟨w₃, i₃, d₃, sm₃⟩ := step_binop s₂ byte f (dstack s) (enc (a.eval st)) (enc (b.eval st))
    w₂ h₂.lo (by have := h₂.hi; simp at this; unfold MAXBYTE at this; omega) hop hd₂ (hr s₂ e₂)
  refine ⟨step s₂, r₁.trans (r₂.trans (Steps.one h₂.run (notIo_of_hop h₂.lo hop hne))), w₃, ?_, by rw [d₃, hval],
    sm₁.trans (sm₂.trans sm₃)⟩
  rw [i₃, i₂, i₁]; simp; omega

/-- `li v` at the pointer: it pushes `v`. -/
theorem run_li {L : Layout} {st : St} {s : State} {v : UInt32} {rest : List UInt8} {d : ℕ}
    (h : At L st s ((0x97 :: le4 v) ++ rest) d) (hd : 1 ≤ d) :
    WF (step s) ∧ getIP (step s) = getIP s + 5 ∧ dstack (step s) = dstack s ++ [v] ∧
      Same s (step s) := by
  have hc := CodeAt.append.mp h.code
  rw [show 0x97 :: le4 v = [0x97] ++ le4 v from rfl, CodeAt.append] at hc
  have hop : high s (getIP s) = 0x97 := by simpa using hc.1.1 0 (by simp)
  have hw : word (high s) (getIP s + 1) = v := word_le4 (by simpa using hc.1.2)
  obtain ⟨w, i, d', sm⟩ := step_li s (dstack s) h.wf h.lo
    (by have := h.hi; simp at this; omega) hop rfl (by have := h.stack; omega)
  exact ⟨w, i, by rw [d', hw], sm⟩

theorem notIo_li {L : Layout} {st : St} {s : State} {v : UInt32} {rest : List UInt8} {d : ℕ}
    (h : At L st s ((0x97 :: le4 v) ++ rest) d) : NotIo s :=
  notIo_of_hop (op := 0x97) h.lo (by simpa using h.code 0 (by simp)) (by decide)

theorem toInt32_ofNat {a : ℕ} (h : a < 2 ^ 31) : toInt32 (UInt32.ofNat a) = a := by
  unfold toInt32; simp only [UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega)]; split_ifs <;> omega

theorem fromInt32_natCast {n : ℕ} (h : n < 2 ^ 32) : fromInt32 (n : ℤ) = UInt32.ofNat n := by
  unfold fromInt32; congr 1; omega

/-- **An index to an address**: `addrCode a₀` turns index `j` on the stack into the
address of cell `j` of the array at `a₀`. -/
theorem run_addr {L : Layout} {st : St} {s : State} {a₀ : ℕ} {rest : List UInt8} {d : ℕ}
    {ds : List UInt32} {j : ℤ} (h : At L st s (addrCode a₀ ++ rest) d) (hd : 1 ≤ d)
    (hds : dstack s = ds ++ [fromInt32 j]) (hj : 0 ≤ j) (ha : a₀ + 4 * j.toNat < MAXBYTE) :
    ∃ s', Steps s s' ∧ WF s' ∧ getIP s' = getIP s + 12 ∧
      dstack s' = ds ++ [UInt32.ofNat (a₀ + 4 * j.toNat)] ∧ Same s s' := by
  unfold MAXBYTE at ha
  have hj' : InRange j := ⟨by omega, by omega⟩
  simp only [addrCode, List.append_assoc] at h
  have hc := h.code
  have hhi := h.hi
  simp at hhi
  -- li 4
  obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_li h hd
  -- ml
  have hop₂ : high (step s) (getIP (step s)) = 0x82 := by
    rw [sm₁.high, i₁]; simpa [le4] using hc 5 (by simp; omega)
  have hlo₁ : 256 ≤ getIP (step s) := by rw [i₁]; have := h.lo; omega
  obtain ⟨w₂, i₂, d₂, sm₂⟩ := step_binop' (step s) 0x82 (fun x y => fromInt32 (toInt32 x * toInt32 y))
    ds (fromInt32 j) 4 w₁ hlo₁ (by rw [i₁]; unfold MAXBYTE at hhi; omega) hop₂
    (by rw [d₁, hds]; simp) runOp_ml
  set s₂ := step (step s)
  have e₂ : fromInt32 (toInt32 (fromInt32 j) * toInt32 4) = fromInt32 (4 * j) := by
    rw [toInt32_fromInt32 hj', show toInt32 4 = 4 from rfl, mul_comm]
  rw [e₂] at d₂
  -- li a₀
  have h₂ : At L st s₂ ((0x97 :: le4 (UInt32.ofNat a₀)) ++ [0x80] ++ rest) d := by
    refine ⟨w₂, (sm₁.trans sm₂).running h.run, by rw [i₂, i₁]; have := h.lo; omega,
      by rw [i₂, i₁]; simp; omega, ?_, by rw [(sm₁.trans sm₂).high]; exact h.vars,
      by rw [d₂]; have := h.stack; rw [hds] at this; simp at this ⊢; omega⟩
    rw [(sm₁.trans sm₂).high, i₂, i₁]
    have := (CodeAt.append.mp (CodeAt.append.mp hc).2).2
    rw [List.append_assoc]; exact this.cast (by simp)
  obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_li h₂ (by have := h.stack; omega)
  -- ad
  have hop₄ : high (step s₂) (getIP (step s₂)) = 0x80 := by
    rw [sm₃.high, i₃]; simpa [le4] using h₂.code 5 (by simp; omega)
  obtain ⟨w₄, i₄, d₄, sm₄⟩ := step_binop' (step s₂) 0x80 (fun x y => fromInt32 (toInt32 x + toInt32 y))
    ds (fromInt32 (4 * j)) (UInt32.ofNat a₀) w₃ (by rw [i₃]; have := h₂.lo; omega)
    (by rw [i₃]; have := h₂.hi; simp at this; unfold MAXBYTE at this; omega) hop₄
    (by rw [d₃, d₂]; simp) runOp_ad
  refine ⟨step (step s₂), ?_, w₄, by rw [i₄, i₃, i₂, i₁], ?_, sm₁.trans (sm₂.trans (sm₃.trans sm₄))⟩
  · exact ((((Steps.one h.run (notIo_li h)).tail ⟨sm₁.running h.run, notIo_of_hop hlo₁ hop₂, rfl⟩).tail
      ⟨h₂.run, notIo_li h₂, rfl⟩).tail ⟨sm₃.running h₂.run,
      notIo_of_hop (by rw [i₃]; have := h₂.lo; omega) hop₄, rfl⟩)
  · rw [d₄, toInt32_fromInt32 ⟨by omega, by omega⟩, toInt32_ofNat (by omega)]
    have e : 4 * j + (a₀ : ℤ) = ((a₀ + 4 * j.toNat : ℕ) : ℤ) := by push_cast; omega
    rw [e, fromInt32_natCast (by omega)]

theorem sbyte_small {k : ℕ} (h : k < 128) : sbyte (UInt8.ofNat k) = k := by
  have : (UInt8.ofNat k).toNat = k := by simp; omega
  have hn : ¬ (UInt8.ofNat k ≥ 128) := by rw [GE.ge, UInt8.le_iff_toNat_le, this]; simp; omega
  simp only [sbyte, hn, if_false, this]

/-- **Expressions**: the code of an expression that fits pushes its value, and
changes nothing else. -/

theorem exp_runs (L : Layout) (hL : L.Ok) (st : St) : ∀ e : Exp, ERuns L st e := by
  intro e
  induction e with
  | lit v =>
    intro s _ h
    simp only [ecode] at h
    obtain ⟨w, i, d, sm⟩ := run_li (rest := []) (by rw [List.append_nil]; exact h) (by simp [depth])
    exact ⟨step s, Steps.one h.run (notIo_li (rest := []) (by rw [List.append_nil]; exact h)), w,
      by rw [i]; simp [ecode], by rw [d]; rfl, sm⟩
  | var x =>
    intro s hf h
    simp only [Fits] at hf
    simp only [ecode, depth] at h ⊢
    obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_li h le_rfl
    have hc := CodeAt.append.mp h.code
    have haddr : L.addr x + 3 < MAXBYTE := by unfold Layout.addr; have := hL.2; omega
    have hop : high (step s) (getIP (step s)) = 0x93 := by
      rw [sm₁.high, i₁]; have := hc.2 0 (by simp); simpa using this
    obtain ⟨w₂, i₂, d₂, sm₂⟩ := step_ri (step s) (dstack s) (UInt32.ofNat (L.addr x)) w₁
      (by rw [i₁]; have := h.lo; omega) (by rw [i₁]; have := h.hi; unfold MAXBYTE at this; simp at this; omega)
      hop d₁ (by rw [toNat_ofNat_addr (by omega)]; unfold Layout.addr; have := hL.1; omega)
      (by rw [toNat_ofNat_addr (by omega)]; exact haddr)
    refine ⟨step (step s), (Steps.one h.run (notIo_li h)).tail
      ⟨sm₁.running h.run, notIo_of_hop (by rw [i₁]; have := h.lo; omega) hop, rfl⟩, w₂,
      by rw [i₂, i₁]; simp, ?_, sm₁.trans sm₂⟩
    rw [d₂, toNat_ofNat_addr (by omega), sm₁.high, h.vars.1 x hf]
    rfl
  | bin op a b iha ihb =>
    intro s hf h
    cases op <;> simp only [Fits] at hf
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, _⟩ := hf
      exact run_bin L st _ a b 0x80 (fun x y => fromInt32 (toInt32 x + toInt32 y)) (fun s _ => runOp_ad s) rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_add ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, _⟩ := hf
      exact run_bin L st _ a b 0x81 (fun x y => fromInt32 (toInt32 x - toInt32 y)) (fun s _ => runOp_sb s) rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_sub ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, _⟩ := hf
      exact run_bin L st _ a b 0x82 (fun x y => fromInt32 (toInt32 x * toInt32 y)) (fun s _ => runOp_ml s) rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_mul ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, hpos, _⟩ := hf
      rw [eb, Value.toInt_int] at hpos
      exact run_bin L st _ a b 0x83 (fun x y => fromInt32 (toInt32 x / toInt32 y))
        (fun s e => runOp_dv s (by rw [e, eb, enc_int]; exact fromInt32_ne_zero rb (by omega)))
        rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_div ra rb hpos) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, hpos, _⟩ := hf
      rw [eb, Value.toInt_int] at hpos
      exact run_bin L st _ a b 0x84 (fun x y => fromInt32 (toInt32 x % toInt32 y))
        (fun s e => runOp_md s (by rw [e, eb, enc_int]; exact fromInt32_ne_zero rb (by omega)))
        rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_mod ra rb hpos) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩⟩ | ⟨⟨x, ea⟩, ⟨y, eb⟩⟩⟩ := hf
      · exact run_bin L st _ a b 0x8A (fun x y => if x == y then 0xFFFFFFFF else 0) (fun s _ => runOp_eq s) rfl (by decide)
          (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_eq ra rb) iha ihb fa fb s h
      · exact run_bin L st _ a b 0x8A (fun x y => if x == y then 0xFFFFFFFF else 0) (fun s _ => runOp_eq s) rfl (by decide)
          (by simp only [Exp.eval]; rw [ea, eb]; cases x <;> cases y <;> rfl) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩⟩ := hf
      exact run_bin L st _ a b 0x8B (fun x y => if toInt32 x < toInt32 y then 0xFFFFFFFF else 0) (fun s _ => runOp_lt s) rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_lt ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨x, ea⟩, ⟨y, eb⟩⟩ := hf
      exact run_bin L st _ a b 0x86 (· &&& ·) (fun s _ => runOp_an s) rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb]; cases x <;> cases y <;> rfl) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨x, ea⟩, ⟨y, eb⟩⟩ := hf
      exact run_bin L st _ a b 0x87 (· ||| ·) (fun s _ => runOp_or s) rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb]; cases x <;> cases y <;> rfl) iha ihb fa fb s h
  | un op a iha =>
    intro s hf h
    cases op <;> try simp only [Fits] at hf
    · -- -a is 0 - a
      obtain ⟨fa, ⟨ka, ea, ra⟩, rn⟩ := hf
      simp only [ecode, depth] at h ⊢
      rw [List.append_assoc] at h
      obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_li h (by omega)
      have h₁ : At L st (step s) (ecode L a ++ [0x81]) (depth a) := by
        have := h.after (bs₁ := 0x97 :: le4 0) (d₂ := depth a) (by omega) w₁
          (by rw [i₁]; rfl) d₁ sm₁
        exact this
      obtain ⟨s₂, r₂, w₂, i₂, d₂, sm₂⟩ := iha (step s) fa (h₁.left le_rfl)
      have h₂ := h₁.after (d₂ := 0) (depth_pos a) w₂ i₂ d₂ sm₂
      have hop : high s₂ (getIP s₂) = 0x81 := by have := h₂.code 0 (by simp); simpa using this
      obtain ⟨w₃, i₃, d₃, sm₃⟩ := step_binop' s₂ 0x81 (fun x y => fromInt32 (toInt32 x - toInt32 y)) (dstack s) 0 (enc (a.eval st))
        w₂ h₂.lo (by have := h₂.hi; simp at this; unfold MAXBYTE at this; omega) hop
        (by rw [d₂, d₁]; simp) runOp_sb
      refine ⟨step s₂, ((Steps.one h.run (notIo_li h)).trans r₂).tail
        ⟨h₂.run, notIo_of_hop h₂.lo hop, rfl⟩, w₃, ?_, ?_,
        sm₁.trans (sm₂.trans sm₃)⟩
      · rw [i₃, i₂, i₁]; simp; omega
      · rw [d₃]; congr 2; simp only [Exp.eval]; rw [ea, enc_int]; exact enc_neg ra
    · obtain ⟨fa, b, eb⟩ := hf
      simp only [ecode, depth] at h ⊢
      obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := iha s fa (h.left le_rfl)
      have h₁ := h.after (d₂ := 0) (depth_pos a) w₁ i₁ d₁ sm₁
      have hop : high s₁ (getIP s₁) = 0x89 := by have := h₁.code 0 (by simp); simpa using this
      obtain ⟨w₂, i₂, d₂, sm₂⟩ := step_nt s₁ (dstack s) (enc (a.eval st)) w₁ h₁.lo
        (by have := h₁.hi; simp at this; unfold MAXBYTE at this; omega) hop d₁
      refine ⟨step s₁, r₁.tail ⟨h₁.run, notIo_of_hop h₁.lo hop, rfl⟩, w₂, by rw [i₂, i₁]; simp; omega, ?_,
        sm₁.trans sm₂⟩
      rw [d₂]; simp only [Exp.eval]; rw [eb, enc_not b]
    · cases a with
      | var x =>
        simp only [Fits] at hf
        obtain ⟨a₀, cap, vs, hx, hvs, hl, hc⟩ := hf
        simp only [ecode, hx] at h ⊢
        obtain ⟨w, i, d, sm⟩ := run_li (rest := []) (by rw [List.append_nil]; exact h)
          (by simp [depth])
        refine ⟨step s, Steps.one h.run (notIo_li (rest := []) (by rw [List.append_nil]; exact h)),
          w, by rw [i]; simp, ?_, sm⟩
        rw [d]
        simp only [Exp.eval, hvs, UnOp.apply, Value.toList_list, hl, enc_int]
        rw [fromInt32_natCast (by omega)]
      | _ => exact hf.elim
  | nil => intro s hf; exact hf.elim
  | cons => intro s hf; exact hf.elim
  | index a i _ ihi =>
    intro s hf h
    cases a with
    | var x =>
      simp only [Fits] at hf
      obtain ⟨fi, a₀, cap, vs, j, hx, hvs, hj, hj0, hjc, hjl⟩ := hf
      have hb := L.arrayAt_bounds hx
      have hL2 := hL.2
      simp only [ecode, depth, hx] at h ⊢
      rw [List.append_assoc] at h
      obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := ihi s fi (h.left (le_max_left _ _))
      have h₁ := h.after (d₂ := 1) (by omega) w₁ i₁ d₁ sm₁
      rw [hj, enc_int] at d₁
      obtain ⟨s₂, r₂, w₂, i₂, d₂, sm₂⟩ := run_addr h₁ le_rfl d₁ hj0 (by unfold MAXBYTE at *; omega)
      have hop : high s₂ (getIP s₂) = 0x93 := by
        rw [sm₂.high, i₂]; simpa using (CodeAt.append.mp h₁.code).2 0 (by simp)
      have hi₂ : getIP s₂ + 1 < 2 ^ 32 := by
        rw [i₂]; have := h₁.hi; simp at this; unfold MAXBYTE at this; omega
      obtain ⟨w₃, i₃, d₃, sm₃⟩ := step_ri s₂ (dstack s) (UInt32.ofNat (a₀ + 4 * j.toNat)) w₂
        (by rw [i₂]; have := h₁.lo; omega) hi₂ hop d₂
        (by rw [toNat_ofNat_addr (by unfold MAXBYTE at *; omega)]; have := hL.1; omega)
        (by rw [toNat_ofNat_addr (by unfold MAXBYTE at *; omega)]; unfold MAXBYTE at *; omega)
      refine ⟨step s₂, r₁.trans (r₂.tail ⟨sm₂.running h₁.run,
        notIo_of_hop (by rw [i₂]; have := h₁.lo; omega) hop, rfl⟩), w₃, ?_, ?_,
        sm₁.trans (sm₂.trans sm₃)⟩
      · rw [i₃, i₂, i₁]; simp; omega
      · rw [d₃, toNat_ofNat_addr (by unfold MAXBYTE at *; omega), sm₂.high, sm₁.high,
          h.vars.2 x a₀ cap hx vs hvs j.toNat hjc hjl]
        simp only [Exp.eval, hvs, hj, Value.index, Value.toInt_int, Value.toList_list, hj0, ite_true]
    | _ => exact hf.elim
  | cond c a b ihc iha ihb =>
    intro s hf h
    obtain ⟨fc, ⟨x, ex⟩, hla, hlb, fab⟩ := hf
    simp only [ecode, depth] at h ⊢
    obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := ihc s fc (h.left (le_max_left _ _))
    have hA : At L st s₁ ([0x9C, UInt8.ofNat ((ecode L a).length + 9)] ++ (ecode L a ++
        ((0x97 :: le4 0) ++ ([0x9C, UInt8.ofNat ((ecode L b).length + 2)] ++ ecode L b)))) 0 :=
      h.after (by omega) w₁ i₁ d₁ sm₁
    have hop : high s₁ (getIP s₁) = 0x9C := by simpa using hA.code 0 (by simp)
    have hd : high s₁ (getIP s₁ + 1) = UInt8.ofNat ((ecode L a).length + 9) := by
      simpa using hA.code 1 (by simp)
    have hsb : sbyte (UInt8.ofNat ((ecode L a).length + 9)) = (ecode L a).length + 9 := sbyte_small hla
    have hhi := hA.hi
    simp only [List.length_append, List.length_cons, length_le4] at hhi
    have hdep := h.stack
    have hpa := depth_pos a
    have hpb := depth_pos b
    obtain ⟨w₂, i₂, d₂, sm₂⟩ := step_h0 s₁ (dstack s) (enc (c.eval st)) w₁ hA.lo
      (by unfold MAXBYTE at *; omega) hop d₁
      (by rw [hd, hsb]; have := hA.lo; simp only [Int.ofNat_eq_natCast]; omega)
      (by rw [hd, hsb]; simp only [Int.ofNat_eq_natCast]; unfold MAXBYTE at *; omega)
    have r₂ : Steps s (step s₁) := r₁.tail ⟨sm₁.running h.run, notIo_of_hop hA.lo hop (by decide), rfl⟩
    rw [ex] at d₁ i₂ fab
    cases x with
    | true =>
      simp only [Value.toBool, ite_true] at fab
      simp only [enc, ite_true, show (0xFFFFFFFF : UInt32) ≠ 0 by decide, ite_false] at i₂
      have hB : At L st (step s₁) (ecode L a ++ ((0x97 :: le4 0) ++
          ([0x9C, UInt8.ofNat ((ecode L b).length + 2)] ++ ecode L b))) (depth a + 1) :=
        ⟨w₂, sm₂.running (sm₁.running h.run), by rw [i₂]; have := hA.lo; omega,
          by simp only [List.length_append, List.length_cons, length_le4]; rw [i₂]; omega,
          by rw [i₂, sm₂.high]; exact (CodeAt.append.mp hA.code).2,
          by rw [sm₂.high, sm₁.high]; exact h.vars, by rw [d₂]; omega⟩
      obtain ⟨s₃, r₃, w₃, i₃, d₃, sm₃⟩ := iha (step s₁) fab (hB.left (by omega))
      have hC := hB.after (d₂ := 1) (by omega) w₃ i₃ d₃ sm₃
      obtain ⟨w₄, i₄, d₄, sm₄⟩ := run_li hC le_rfl
      have hC' := hC.after (bs₁ := 0x97 :: le4 0) (d₂ := 0) le_rfl w₄ (by rw [i₄]; rfl) d₄ sm₄
      have hop' : high (step s₃) (getIP (step s₃)) = 0x9C := by simpa using hC'.code 0 (by simp)
      have hd' : high (step s₃) (getIP (step s₃) + 1) = UInt8.ofNat ((ecode L b).length + 2) := by
        simpa using hC'.code 1 (by simp)
      have hsb' := sbyte_small (k := (ecode L b).length + 2) (by omega)
      have hhi' := hC'.hi
      simp only [List.length_append, List.length_cons] at hhi'
      obtain ⟨w₅, i₅, d₅, sm₅⟩ := step_h0 (step s₃) (dstack s ++ [enc (a.eval st)]) 0 w₄ hC'.lo
        (by unfold MAXBYTE at *; omega) hop' (by rw [d₄, d₃, d₂])
        (by rw [hd', hsb']; have := hC'.lo; simp only [Int.ofNat_eq_natCast]; omega)
        (by rw [hd', hsb']; simp only [Int.ofNat_eq_natCast]; unfold MAXBYTE at *; omega)
      refine ⟨step (step s₃), (r₂.trans r₃).tail ⟨hC.run, notIo_li hC, rfl⟩ |>.tail
        ⟨hC'.run, notIo_of_hop hC'.lo hop' (by decide), rfl⟩, w₅, ?_, ?_,
        sm₁.trans (sm₂.trans (sm₃.trans (sm₄.trans sm₅)))⟩
      · rw [i₅, hd', hsb', i₄, i₃, i₂, i₁]; simp; omega
      · rw [d₅]; simp [Exp.eval, ex, Value.toBool]
    | false =>
      simp only [Value.toBool, Bool.false_eq_true, ite_false] at fab
      simp only [enc, Bool.false_eq_true, ite_false, ite_true] at i₂
      rw [hd, hsb] at i₂
      replace i₂ : getIP (step s₁) = getIP s₁ + ((ecode L a).length + 9) := by
        rw [i₂]; simp only [Int.ofNat_eq_natCast]; omega
      have hB : At L st (step s₁) (ecode L b) (depth b) :=
        ⟨w₂, sm₂.running (sm₁.running h.run), by rw [i₂]; have := hA.lo; omega,
          by rw [i₂]; omega,
          by
            rw [i₂, sm₂.high]
            have := (CodeAt.append.mp (CodeAt.append.mp (CodeAt.append.mp
              (CodeAt.append.mp hA.code).2).2).2).2
            convert this using 1; simp; omega,
          by rw [sm₂.high, sm₁.high]; exact h.vars, by rw [d₂]; omega⟩
      obtain ⟨s₃, r₃, w₃, i₃, d₃, sm₃⟩ := ihb (step s₁) fab hB
      refine ⟨s₃, r₂.trans r₃, w₃, ?_, ?_, sm₁.trans (sm₂.trans sm₃)⟩
      · rw [i₃, i₂, i₁]; simp; omega
      · rw [d₃, d₂]; simp [Exp.eval, ex, Value.toBool]

/-! ### Statements -/

/-- `jm a`. -/
def jmTo (a : ℕ) : List UInt8 := 0x9A :: le4 (UInt32.ofNat a)

/-- The test of `if` and `while`: complement the condition, and hop over the
`jm` that follows when it was true. -/
def test : List UInt8 := [0x89, 0x9C, 7]

/-- The code of several expressions, one after the other: it pushes their values. -/
def ecodes (L : Layout) : List Exp → List UInt8
  | [] => []
  | e :: es => ecode L e ++ ecodes L es

/-- Store the top `k` words of the stack in cells `k-1`, …, `0` of the array at
`a₀`, the top one in cell `k-1`. -/
def storeCode (a₀ : ℕ) : ℕ → List UInt8
  | 0 => []
  | k + 1 => ((0x97 :: le4 (UInt32.ofNat (a₀ + 4 * k))) ++ [0x95]) ++ storeCode a₀ k

@[simp] theorem length_storeCode (a₀ k : ℕ) : (storeCode a₀ k).length = 6 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [storeCode, ih]; omega

/-- The length of a statement's code. -/
def slen (L : Layout) : Stmt → ℕ
  | .ok => 0
  | .assign _ e => (ecode L e).length + 6
  | .seq p q => slen L p + slen L q
  | .cond c p q => (ecode L c).length + 8 + slen L p + 5 + slen L q
  | .loop c p => (ecode L c).length + 8 + slen L p + 5
  | .tick => 8
  | .send _ e => (ecode L e).length + 11
  | .recv _ _ => 17
  | .call _ => 5
  | .scope _ e p => 7 + ((ecode L e).length + 6) + slen L p + 7
  | .ret => 1
  | .restore _ _ => 7
  | .check _ _ => 17
  | .store x i e =>
    match L.arrayAt x with
    | some _ => (ecode L e).length + (ecode L i).length + 13
    | none => 0
  | .choice p q => 415 + slen L p + 5 + slen L q
  | .ensure c => (ecode L c).length + 474
  | .fill x es =>
    match L.arrayAt x with
    | some _ => (ecodes L es).length + 6 * es.length
    | none => 0

/-- The code of the statements backtracking's runtime is written in — `ok`,
assignment, sequence, `if`, `while` and stores — as `scode` makes it
(`scodeR_eq`). -/
def scodeR (L : Layout) (a : ℕ) : Stmt → List UInt8
  | .ok => []
  | .assign x e => ecode L e ++ (0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]
  | .seq p q => scodeR L a p ++ scodeR L (a + slen L p) q
  | .cond c p q =>
    let t := a + (ecode L c).length + 8
    let el := t + slen L p + 5
    ecode L c ++ test ++ jmTo el ++ scodeR L t p ++ jmTo (el + slen L q) ++ scodeR L el q
  | .loop c p =>
    let b := a + (ecode L c).length + 8
    ecode L c ++ test ++ jmTo (b + slen L p + 5) ++ scodeR L b p ++ jmTo a
  | .store x i e =>
    match L.arrayAt x with
    | some (a₀, _) => ecode L e ++ ecode L i ++ addrCode a₀ ++ [0x95]
    | none => []
  | _ => []

@[simp] theorem Layout.rt_arrayAt0 (L : Layout) :
    L.rt.arrayAt 0 = some (L.base, L.W + 5 + L.choices * (L.W + 1)) := by
  simp [Layout.rt, Layout.arrayAt, arrFrom]

set_option maxRecDepth 8000 in
theorem length_scodeR_save (L : Layout) (w alt a : ℕ) : (scodeR L.rt a (RT.save w alt)).length = 415 := by
  simp [RT.save, RT.copy, RT.recAt, scodeR, ecode, slen, addrCode, jmTo, test]

set_option maxRecDepth 8000 in
theorem length_scodeR_pop (L : Layout) (w a : ℕ) : (scodeR L.rt a (RT.pop w)).length = 367 := by
  simp [RT.pop, RT.copy, RT.recAt, scodeR, ecode, slen, addrCode, jmTo, test]

theorem length_scodeR_halt (L : Layout) (w a : ℕ) : (scodeR L.rt a (RT.halt w)).length = 23 := by
  simp [RT.halt, scodeR, ecode, addrCode]

theorem length_ecode_cnt (L : Layout) (w : ℕ) : (ecode L.rt (RT.mem (RT.lit w))).length = 18 := by
  simp [ecode, addrCode]

theorem length_ecode_alt (L : Layout) (w : ℕ) : (ecode L.rt (RT.mem (RT.recAt w))).length = 43 := by
  simp [ecode, addrCode, RT.recAt, binByte]

/-- What a failed `ensure` runs, at `f`: with no choice point kept, set the
flag and halt; otherwise take the last one back and go to its other choice. -/
def failCode (L : Layout) (f : ℕ) : List UInt8 :=
  ecode L.rt (RT.mem (RT.lit L.W)) ++ [0x9C, 7] ++ jmTo (f + 49) ++
    (scodeR L.rt (f + 25) (RT.halt L.W) ++ [0xFF]) ++
    (scodeR L.rt (f + 49) (RT.pop L.W) ++ ecode L.rt (RT.mem (RT.recAt L.W)) ++ [0x90, 0x9E])

theorem length_failCode (L : Layout) (f : ℕ) : (failCode L f).length = 461 := by
  simp [failCode, length_scodeR_halt, length_scodeR_pop, length_ecode_cnt, length_ecode_alt, jmTo]

/-- **The code of a statement** placed at address `a`. -/
def scode (L : Layout) (a : ℕ) : Stmt → List UInt8
  | .ok => []
  | .assign x e => ecode L e ++ (0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]
  | .seq p q => scode L a p ++ scode L (a + slen L p) q
  | .cond c p q =>
    let t := a + (ecode L c).length + 8
    let el := t + slen L p + 5
    ecode L c ++ test ++ jmTo el ++ scode L t p ++ jmTo (el + slen L q) ++ scode L el q
  | .loop c p =>
    let b := a + (ecode L c).length + 8
    ecode L c ++ test ++ jmTo (b + slen L p + 5) ++ scode L b p ++ jmTo a
  | .tick => [0x34] ++ (0x97 :: le4 1) ++ [0x80, 0x54]
  | .send c e => ecode L e ++ (0x97 :: le4 (UInt32.ofNat c)) ++ (0x97 :: le4 SEND) ++ [0xFD]
  | .recv c x => (0x97 :: le4 (UInt32.ofNat c)) ++ (0x97 :: le4 RECV) ++ [0xFD] ++
      (0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]
  | .call k => 0x9D :: le4 (UInt32.ofNat (L.entry k))
  | .scope x e p =>
    let b := a + 7 + ((ecode L e).length + 6)
    ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x93, 0x90]) ++
      (ecode L e ++ (0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]) ++
      scode L b p ++ ([0x91] ++ (0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])
  | .ret => [0x9E]
  | .restore x _ => [0x91] ++ (0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]
  | .check c x => (0x97 :: le4 (UInt32.ofNat c)) ++ (0x97 :: le4 CHECK) ++ [0xFD] ++
      (0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]
  | .store x i e =>
    match L.arrayAt x with
    | some (a₀, _) => ecode L e ++ ecode L i ++ addrCode a₀ ++ [0x95]
    | none => []
  | .choice p q =>
    let b := a + 415
    let alt := b + slen L p + 5
    scodeR L.rt a (RT.save L.W alt) ++ scode L b p ++ jmTo (alt + slen L q) ++ scode L alt q
  | .ensure c =>
    let f := a + (ecode L c).length + 13
    ecode L c ++ test ++ jmTo f ++ jmTo (f + 461) ++ failCode L f
  | .fill x es =>
    -- every item first, so that each is computed from the old list
    match L.arrayAt x with
    | some (a₀, _) => ecodes L es ++ storeCode a₀ es.length
    | none => []

theorem length_scode (L : Layout) : ∀ (p : Stmt) (a : ℕ), (scode L a p).length = slen L p
  | .ok, _ => rfl
  | .assign _ _, _ => by simp [scode, slen]
  | .seq p q, a => by simp [scode, slen, length_scode L p, length_scode L q]
  | .cond c p q, a => by
    simp [scode, slen, length_scode L p, length_scode L q, test, jmTo]; omega
  | .loop c p, a => by simp [scode, slen, length_scode L p, test, jmTo]; omega
  | .tick, _ => rfl
  | .send _ _, _ => by simp [scode, slen]
  | .recv _ _, _ => rfl
  | .call _, _ => rfl
  | .scope _ _ p, a => by simp [scode, slen, length_scode L p]; omega
  | .ret, _ => rfl
  | .restore _ _, _ => rfl
  | .check _ _, _ => rfl
  | .store x _ _, _ => by
    cases hx : L.arrayAt x <;> simp [scode, slen, hx]; omega
  | .choice p q, a => by
    simp [scode, slen, length_scode L p, length_scode L q, length_scodeR_save, jmTo]; omega
  | .ensure _, _ => by simp [scode, slen, length_failCode, test, jmTo]
  | .fill x _, _ => by cases hx : L.arrayAt x <;> simp [scode, slen, hx]

/-- How deep the stack gets in any of several expressions. -/
def maxDepth : List Exp → ℕ
  | [] => 0
  | e :: es => max (depth e) (maxDepth es)

/-- How deep the stack gets in a statement. -/
def sdepth : Stmt → ℕ
  | .ok => 0
  | .assign _ e => depth e + 1
  | .seq p q => max (sdepth p) (sdepth q)
  | .cond c p q => max (depth c) (max (sdepth p) (sdepth q))
  | .loop c p => max (depth c) (sdepth p)
  | .tick => 2
  | .send _ e => max (depth e) 3
  | .recv _ _ => 2
  | .call _ => 0
  | .scope _ e p => max 2 (max (depth e + 1) (sdepth p))
  | .ret => 0
  | .restore _ _ => 2
  | .check _ _ => 2
  | .store _ i e => max (depth e) (max (depth i + 1) 3)
  | .choice p q => max 4 (max (sdepth p) (sdepth q))
  | .ensure c => max (depth c) 4
  | .fill _ es => es.length + maxDepth es + 1

/-- The named statements' code, each at its entry and followed by `rt`, below
the variables. -/
def Layout.Image (L : Layout) (m : ℕ → UInt8) : Prop :=
  ∀ k ∈ L.keys, 256 ≤ L.entry k ∧ L.entry k + slen L (L.defs k) + 1 ≤ L.base ∧
    sdepth (L.defs k) ≤ STACKSZ ∧ CodeAt m (L.entry k) (scode L (L.entry k) (L.defs k) ++ [0x9E])

theorem Layout.Image.mono {L : Layout} {m m' : ℕ → UInt8} (h : L.Image m)
    (hm : ∀ i < L.base, m' i = m i) : L.Image m' := fun k hk => by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h k hk
  refine ⟨h₁, h₂, h₃, fun i hi => ?_⟩
  simp [length_scode] at hi
  rw [hm _ (by omega)]; exact h₄ i (by simp [length_scode]; omega)

/-- **Execution in 32 bits**: the language's execution of a statement, with `d`
entries on the machine's control stack, in which every expression evaluated fits
(`Fits`), every assigned variable has a cell, every condition is a binary, every
call is of a defined name, and the control stack does not overflow. -/
inductive SEval (L : Layout) : ℕ → Stmt → St → St → Prop
  /-- `ok`. -/
  | ok {d : ℕ} {s : St} : SEval L d .ok s s
  /-- An assignment, of a value that fits, to a variable with a cell. -/
  | assign {d : ℕ} {x : ℕ} {e : Exp} {s : St} : x < L.n → L.arrayAt x = none → Fits L s e →
      SEval L d (.assign x e) s (Function.update s x (e.eval s))
  /-- `P. Q`. -/
  | seq {d : ℕ} {p q : Stmt} {s t u : St} : SEval L d p s t → SEval L d q t u →
      SEval L d (.seq p q) s u
  /-- `if` with a true condition. -/
  | condT {d : ℕ} {c : Exp} {p q : Stmt} {s t : St} : Fits L s c → c.eval s = .bool true →
      SEval L d p s t → SEval L d (.cond c p q) s t
  /-- `if` with a false condition. -/
  | condF {d : ℕ} {c : Exp} {p q : Stmt} {s t : St} : Fits L s c → c.eval s = .bool false →
      SEval L d q s t → SEval L d (.cond c p q) s t
  /-- A loop that goes round. -/
  | loopT {d : ℕ} {c : Exp} {p : Stmt} {s t u : St} : Fits L s c → c.eval s = .bool true →
      SEval L d p s t → SEval L d (.loop c p) t u → SEval L d (.loop c p) s u
  /-- A loop that exits. -/
  | loopF {d : ℕ} {c : Exp} {p : Stmt} {s : St} : Fits L s c → c.eval s = .bool false →
      SEval L d (.loop c p) s s
  /-- A call: the named statement runs, one deeper. -/
  | call {d : ℕ} {k : ℕ} {s t : St} : k ∈ L.keys → d < STACKSZ →
      SEval L (d + 1) (L.defs k) s t → SEval L d (.call k) s t
  /-- A scope: `x` holds `e` while `P` runs, one deeper, and gets its value back. -/
  | scope {d : ℕ} {x : ℕ} {e : Exp} {p : Stmt} {s t : St} : x < L.n → L.arrayAt x = none →
      Fits L s e →
      d < STACKSZ → SEval L (d + 1) p (Function.update s x (e.eval s)) t →
      SEval L d (.scope x e p) s (Function.update t x (s x))
  /-- `A i:= e`, an index inside the array and a value that fits. -/
  | store {d : ℕ} {x : ℕ} {i e : Exp} {s : St} : Fits L s (.index (.var x) i) → Fits L s e →
      SEval L d (.store x i e) s
        (Function.update s x ((s x).update [(i.eval s).toInt] (e.eval s)))
  /-- `A:= [e₀; …; eₖ₋₁]`, on an array of `k` cells that holds a list of `k` items,
  with items that fit. -/
  | fill {d : ℕ} {x a₀ : ℕ} {es : List Exp} {s : St} {vs : List Value} :
      L.arrayAt x = some (a₀, es.length) → s x = .list vs → vs.length = es.length →
      (∀ e ∈ es, Fits L s e) →
      SEval L d (.fill x es) s (Function.update s x ((Exp.ofList es).eval s))

/-- The definitions a layout carries, as the interpreter's. -/
@[instance_reducible] def Layout.env (L : Layout) : Defs ℕ Value := ⟨fun k => (L.defs k).toProg⟩

/-- Execution in 32 bits is execution: the language's semantics allows it. -/
theorem eval_of_sEval {L : Layout} {d : ℕ} {p : Stmt} {s t : St} (h : SEval L d p s t) :
    @Eval ℕ Value L.env _ p.toProg s t := by
  let _ := L.env
  induction h with
  | ok => exact .ok
  | assign => exact .assign
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | condT _ hc _ ih => exact .condTrue (by simp [Exp.test, hc]) ih
  | condF _ hc _ ih => exact .condFalse (by simp [Exp.test, hc]) ih
  | loopT _ hc _ _ ih₁ ih₂ => exact .whileTrue (by simp [Exp.test, hc]) ih₁ ih₂
  | loopF _ hc => exact .whileFalse (by simp [Exp.test, hc])
  | call _ _ _ ih => exact .call ih
  | scope _ _ _ _ _ ih => exact .newLocal ih
  | store => exact .assign
  | fill => exact .assign

/-! ### Running statements -/

theorem CodeAt.mono {m m' : ℕ → UInt8} {a b : ℕ} {bs : List UInt8} (h : CodeAt m a bs)
    (hm : ∀ i < b, m' i = m i) (hb : a + bs.length ≤ b) : CodeAt m' a bs :=
  fun i hi => by rw [hm _ (by omega)]; exact h i hi

/-- `jm t` at the pointer. -/
theorem run_jm {s : State} {t : ℕ} (hw : WF s) (hlo : 256 ≤ getIP s) (hhi : getIP s + 6 < MAXBYTE)
    (hc : CodeAt (high s) (getIP s) (jmTo t)) (ht : 256 ≤ t) (ht' : t < MAXBYTE) :
    WF (step s) ∧ getIP (step s) = t ∧ dstack (step s) = dstack s ∧ Same s (step s) := by
  rw [jmTo, show 0x9A :: le4 (UInt32.ofNat t) = [0x9A] ++ le4 (UInt32.ofNat t) from rfl,
    CodeAt.append] at hc
  have hop : high s (getIP s) = 0x9A := by simpa using hc.1 0 (by simp)
  have hword : word (high s) (getIP s + 1) = UInt32.ofNat t := word_le4 (by simpa using hc.2)
  have htn : (UInt32.ofNat t).toNat = t := toNat_ofNat_addr ht'
  obtain ⟨w, i, d, sm⟩ := step_jm s hw hlo (by omega) hop (by rw [hword, htn]; exact ht)
  exact ⟨w, by rw [i, hword, htn], d, sm⟩

theorem notIo_jm {s : State} {t : ℕ} (hlo : 256 ≤ getIP s)
    (hc : CodeAt (high s) (getIP s) (jmTo t)) : NotIo s :=
  notIo_of_hop (op := 0x9A) hlo (by
    have := hc 0 (by simp [jmTo])
    simpa only [jmTo, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
      Nat.add_zero] using this) (by decide)

/-- The test: from the condition's value `b` on the stack, go on to the `jm`
after it if `b` is false, and past it if `b` is true. -/
theorem run_test {s : State} {b : Bool} (hw : WF s) (hr : Running s) (hlo : 256 ≤ getIP s)
    (hhi : getIP s + 9 < MAXBYTE) (hc : CodeAt (high s) (getIP s) test)
    (hd : dstack s = [enc (.bool b)]) :
    ∃ s', Steps s s' ∧ WF s' ∧ getIP s' = (if b then getIP s + 8 else getIP s + 3) ∧
      dstack s' = [] ∧ Same s s' := by
  have hop₁ : high s (getIP s) = 0x89 := by simpa [test] using hc 0 (by simp [test])
  obtain ⟨w₁, i₁, d₁, sm₁⟩ := step_nt s [] _ hw hlo (by unfold MAXBYTE at hhi; omega) hop₁
    (by simpa using hd)
  have hop₂ : high (step s) (getIP (step s)) = 0x9C := by
    rw [sm₁.high, i₁]; simpa [test] using hc 1 (by simp [test])
  have hd₂ : high (step s) (getIP (step s) + 1) = 7 := by
    rw [sm₁.high, i₁]; simpa [test] using hc 2 (by simp [test])
  have h7 : sbyte 7 = 7 := by decide
  obtain ⟨w₂, i₂, d₂, sm₂⟩ := step_h0 (step s) [] _ w₁ (by rw [i₁]; omega)
    (by rw [i₁]; omega) hop₂ (by simpa using d₁)
    (by rw [hd₂, h7, i₁]; simp only [Int.ofNat_eq_natCast]; omega)
    (by rw [hd₂, h7, i₁]; simp only [Int.ofNat_eq_natCast]; omega)
  refine ⟨step (step s), (Steps.one hr (notIo_of_hop hlo hop₁)).tail
    ⟨sm₁.running hr, notIo_of_hop (by rw [i₁]; omega) hop₂, rfl⟩, w₂, ?_, d₂, sm₁.trans sm₂⟩
  rw [i₂, hd₂, h7, i₁]
  cases b <;> simp [enc]; omega

/-- What a statement's run keeps: the code and everything else below the
variables, the control stack and the output. -/
structure Keeps (L : Layout) (s s' : State) : Prop where
  /-- Memory below the cells: the code. -/
  low : ∀ i < L.base, high s' i = high s i
  /-- The control stack. -/
  cs : cstack s' = cstack s
  /-- The output. -/
  ob : s'.ob = s.ob
  /-- The clock. -/
  clk : getClk s' = getClk s
  /-- And everything above the cells. -/
  top : ∀ i, L.top ≤ i → high s' i = high s i

theorem Keeps.trans {L : Layout} {s₁ s₂ s₃ : State} (h₁ : Keeps L s₁ s₂) (h₂ : Keeps L s₂ s₃) :
    Keeps L s₁ s₃ :=
  ⟨fun i hi => (h₂.low i hi).trans (h₁.low i hi), h₂.cs.trans h₁.cs, h₂.ob.trans h₁.ob,
    h₂.clk.trans h₁.clk, fun i hi => (h₂.top i hi).trans (h₁.top i hi)⟩

theorem _root_.B4.Same.keeps {L : Layout} {s s' : State} (h : Same s s') : Keeps L s s' :=
  ⟨fun i _ => by rw [h.high], h.cs, h.ob, h.clk, fun i _ => by rw [h.high]⟩

/-- Writing a variable's cell keeps what is above the cells. -/
theorem writeWord_top {L : Layout} {m : ℕ → UInt8} {a i : ℕ} {v : UInt32} (ha : a + 4 ≤ L.top)
    (hi : L.top ≤ i) : writeWord m a v i = m i := by
  unfold writeWord
  simp [show i ≠ a by omega, show i ≠ a + 1 by omega, show i ≠ a + 2 by omega,
    show i ≠ a + 3 by omega]

/-- What every statement lemma assumes of the machine: statement `p`'s code at
the pointer `a`, below the variables, which hold `st`, and an empty stack. -/
structure SAt (L : Layout) (d : ℕ) (st : St) (s : State) (a : ℕ) (p : Stmt) : Prop where
  wf : WF s
  run : Running s
  ip : getIP s = a
  lo : 256 ≤ a
  hi : a + slen L p ≤ L.base
  code : CodeAt (high s) a (scode L a p)
  vars : VarsOk L (high s) st
  stack : dstack s = []
  depth : sdepth p ≤ STACKSZ
  cs : (cstack s).length = d
  image : L.Image (high s)

/-- What a statement's code does. -/
def SRuns (L : Layout) (d : ℕ) (p : Stmt) (st st' : St) : Prop :=
  ∀ s a, SAt L d st s a p → ∃ s', Steps s s' ∧ WF s' ∧ Running s' ∧ getIP s' = a + slen L p ∧
    dstack s' = [] ∧ VarsOk L (high s') st' ∧ Keeps L s s'

theorem varsOk_write {L : Layout} {m : ℕ → UInt8} {st : St} {x : ℕ} {v : Value}
    (h : VarsOk L m st) (hx : x < L.n) (ha : L.arrayAt x = none) :
    VarsOk L (writeWord m (L.addr x) (enc v)) (Function.update st x v) := by
  refine ⟨fun y hy => ?_, fun y a₀ cap hy vs hvs j hj hj' => ?_⟩
  · by_cases hxy : y = x
    · subst hxy; rw [Function.update_self, word_writeWord_self]
    · rw [Function.update_of_ne hxy, word_writeWord_of_disjoint _ _ _ _ (by
        unfold Layout.addr; omega)]
      exact h.1 y hy
  · have hxy : y ≠ x := by rintro rfl; rw [ha] at hy; cases hy
    rw [Function.update_of_ne hxy] at hvs
    have hb := Layout.arrayAt_bounds hy
    rw [word_writeWord_of_disjoint _ _ _ _ (by unfold Layout.addr; omega)]
    exact h.2 y a₀ cap hy vs hvs j hj hj'

/-- **Assignment**: compute, push the cell's address, store. -/
theorem assign_runs (L : Layout) (hL : L.Ok) {d x : ℕ} {e : Exp} {st : St} (hx : x < L.n)
    (ha : L.arrayAt x = none)
    (hf : Fits L st e) : SRuns L d (.assign x e) st (Function.update st x (e.eval st)) := by
  intro s a h
  have hcode := h.code
  simp only [scode] at hcode
  have hlen : (scode L a (.assign x e)).length = slen L (.assign x e) := length_scode L _ a
  simp only [scode, slen] at hlen
  have hA : At L st s (ecode L e ++ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]))
      (depth e + 1) := by
    refine ⟨h.wf, h.run, h.ip ▸ h.lo, ?_, by rw [h.ip, ← List.append_assoc]; exact hcode, h.vars,
      by rw [h.stack]; have := h.depth; simp [sdepth] at this; simp; omega⟩
    have h1 := h.hi; have h2 := hL.2; have h3 := h.ip; simp [slen] at h1 ⊢; omega
  obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := exp_runs L hL st e s hf (hA.left (by omega))
  have h₁ := hA.after (d₂ := depth e) (by omega) w₁ i₁ d₁ sm₁
  obtain ⟨w₂, i₂, d₂, sm₂⟩ := run_li h₁ (by have := depth_pos e; omega)
  have haddr : L.addr x + 3 < MAXBYTE := by unfold Layout.addr; have := hL.2; omega
  have hop : high (step s₁) (getIP (step s₁)) = 0x95 := by
    rw [sm₂.high, i₂]; have := (CodeAt.append.mp h₁.code).2 0 (by simp); simpa using this
  obtain ⟨w₃, i₃, d₃, c₃, st₃, db₃, hi₃, o₃⟩ := step_wi (step s₁) [] (enc (e.eval st))
    (UInt32.ofNat (L.addr x)) w₂ (by rw [i₂]; have := h₁.lo; omega)
    (by rw [i₂]; have := h₁.hi; unfold MAXBYTE at this; simp at this; omega) hop
    (by rw [d₂, d₁, h.stack]; rfl)
    (by rw [toNat_ofNat_addr (by omega)]; unfold Layout.addr; have := hL.1; omega)
    (by rw [toNat_ofNat_addr (by omega)]; exact haddr)
  have hclk := step_wi_clk (step s₁) [] (enc (e.eval st)) (UInt32.ofNat (L.addr x)) w₂
    (by rw [i₂]; have := h₁.lo; omega) hop (by rw [d₂, d₁, h.stack]; rfl)
    (by rw [toNat_ofNat_addr (by omega)]; unfold Layout.addr; have := hL.1; omega)
  rw [toNat_ofNat_addr (by omega)] at hi₃
  have hr₂ : Running (step s₁) := sm₂.running (sm₁.running h.run)
  refine ⟨step (step s₁), (r₁.tail ⟨sm₁.running h.run, notIo_li h₁, rfl⟩).tail
    ⟨hr₂, notIo_of_hop (by rw [i₂]; have := h₁.lo; omega) hop, rfl⟩, w₃,
    ⟨st₃.trans hr₂.1, db₃.trans hr₂.2⟩, ?_, d₃, ?_, ?_⟩
  · rw [i₃, i₂, i₁, h.ip]; simp [slen]; omega
  · rw [hi₃, sm₂.high, sm₁.high]; exact varsOk_write h.vars hx ha
  · refine ⟨fun i hi => ?_, by rw [c₃, sm₂.cs, sm₁.cs], by rw [o₃, sm₂.ob, sm₁.ob],
      by rw [hclk, sm₂.clk, sm₁.clk], fun i hi => ?_⟩
    swap
    · rw [hi₃, sm₂.high, sm₁.high, writeWord_top (by unfold Layout.addr Layout.top; omega) hi]
    rw [hi₃, sm₂.high, sm₁.high]
    unfold writeWord Layout.addr
    have : i < L.base := hi
    simp [show i ≠ L.base + 4 * x by omega, show i ≠ L.base + 4 * x + 1 by omega,
      show i ≠ L.base + 4 * x + 2 by omega, show i ≠ L.base + 4 * x + 3 by omega]

/-- Writing cell `j` of array `x` keeps the cells holding the state, with item `j`
of `x` set. -/
theorem varsOk_store {L : Layout} {m : ℕ → UInt8} {st : St} {x a₀ cap j : ℕ} {vs : List Value}
    {v : Value} (h : VarsOk L m st) (hx : L.arrayAt x = some (a₀, cap)) (hvs : st x = .list vs)
    (hj : j < cap) :
    VarsOk L (writeWord m (a₀ + 4 * j) (enc v)) (Function.update st x (.list (vs.set j v))) := by
  have hb := L.arrayAt_bounds hx
  refine ⟨fun y hy => ?_, fun y a₁ c₁ hy vs' hvs' j' hj' hj'l => ?_⟩
  · rw [word_writeWord_of_disjoint _ _ _ _ (by unfold Layout.addr; omega), h.1 y hy]
    by_cases hxy : y = x
    · subst hxy; rw [Function.update_self, hvs]; rfl
    · rw [Function.update_of_ne hxy]
  · by_cases hxy : y = x
    · subst hxy
      rw [hx] at hy; cases hy
      rw [Function.update_self] at hvs'; cases hvs'
      rw [List.length_set] at hj'l
      by_cases hjj : j' = j
      · subst hjj
        rw [word_writeWord_self, List.getD_eq_getElem _ _ (by simpa using hj'l),
          List.getElem_set_self]
      · rw [word_writeWord_of_disjoint _ _ _ _ (by omega), h.2 _ _ _ hx vs hvs j' hj' hj'l]
        simp [List.getD_eq_getElem?_getD, Ne.symm hjj]
    · rw [Function.update_of_ne hxy] at hvs'
      have hd := arrFrom_disjoint _ _ _ _ _ _ _ _ hxy hy hx
      rw [word_writeWord_of_disjoint _ _ _ _ (by omega)]
      exact h.2 y a₁ c₁ hy vs' hvs' j' hj' hj'l

/-- **`A i:= e`**: compute the value, then the cell's address, and store. -/
theorem store_runs (L : Layout) (hL : L.Ok) {d x : ℕ} {i e : Exp} {st : St}
    (hfi : Fits L st (.index (.var x) i)) (hf : Fits L st e) :
    SRuns L d (.store x i e) st
      (Function.update st x ((st x).update [(i.eval st).toInt] (e.eval st))) := by
  intro s a h
  have hfi' := hfi
  simp only [Fits] at hfi'
  obtain ⟨fi, a₀, cap, vs, j, hx, hvs, hj, hj0, hjc, hjl⟩ := hfi'
  have hb := L.arrayAt_bounds hx
  have hL1 := hL.1; have hL2 := hL.2
  have hcode := h.code
  simp only [scode, hx] at hcode
  have hhi := h.hi; simp only [slen, hx] at hhi
  have hdep := h.depth; simp only [sdepth] at hdep
  have hA : At L st s (ecode L e ++ (ecode L i ++ (addrCode a₀ ++ [0x95])))
      (max (depth e) (max (depth i + 1) 3)) := by
    refine ⟨h.wf, h.run, h.ip ▸ h.lo, ?_, by rw [h.ip]; simpa only [List.append_assoc] using hcode,
      h.vars, by rw [h.stack]; simpa using hdep⟩
    have h3 := h.ip; simp; omega
  obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := exp_runs L hL st e s hf (hA.left (le_max_left _ _))
  have h₁ := hA.after (d₂ := max (depth i) 2) (by omega) w₁ i₁ d₁ sm₁
  obtain ⟨s₂, r₂, w₂, i₂, d₂, sm₂⟩ := exp_runs L hL st i s₁ fi (h₁.left (le_max_left _ _))
  have h₂ := h₁.after (d₂ := 1) (by omega) w₂ i₂ d₂ sm₂
  rw [d₁, h.stack, hj, enc_int] at d₂
  obtain ⟨s₃, r₃, w₃, i₃, d₃, sm₃⟩ := run_addr h₂ le_rfl d₂ hj0 (by unfold MAXBYTE at *; omega)
  have hop : high s₃ (getIP s₃) = 0x95 := by
    rw [sm₃.high, i₃]; simpa using (CodeAt.append.mp h₂.code).2 0 (by simp)
  have hlo₃ : 256 ≤ getIP s₃ := by rw [i₃]; have := h₂.lo; omega
  have hA₃ : (UInt32.ofNat (a₀ + 4 * j.toNat)).toNat = a₀ + 4 * j.toNat :=
    toNat_ofNat_addr (by unfold MAXBYTE at *; omega)
  obtain ⟨w₄, i₄, d₄, c₄, st₄, db₄, hi₄, o₄⟩ := step_wi s₃ [] (enc (e.eval st))
    (UInt32.ofNat (a₀ + 4 * j.toNat)) w₃ hlo₃
    (by rw [i₃]; have := h₂.hi; unfold MAXBYTE at this; simp at this; omega) hop
    (by rw [d₃]; rfl) (by rw [hA₃]; omega) (by rw [hA₃]; unfold MAXBYTE at *; omega)
  have hclk := step_wi_clk s₃ [] (enc (e.eval st)) (UInt32.ofNat (a₀ + 4 * j.toNat)) w₃ hlo₃ hop
    (by rw [d₃]; rfl) (by rw [hA₃]; omega)
  rw [hA₃] at hi₄
  have sm := sm₁.trans (sm₂.trans sm₃)
  have hr₃ : Running s₃ := sm.running h.run
  refine ⟨step s₃, (r₁.trans (r₂.trans r₃)).tail ⟨hr₃, notIo_of_hop hlo₃ hop, rfl⟩, w₄,
    ⟨st₄.trans hr₃.1, db₄.trans hr₃.2⟩, ?_, d₄, ?_, ?_⟩
  · rw [i₄, i₃, i₂, i₁, h.ip]; simp [slen, hx]; omega
  · rw [hi₄, sm.high, hvs, hj, Value.toInt_int, Value.update_single ⟨hj0, hjl⟩]
    exact varsOk_store h.vars hx hvs hjc
  · refine ⟨fun k hk => ?_, by rw [c₄, sm.cs], by rw [o₄, sm.ob], by rw [hclk, sm.clk], fun k hk => ?_⟩
    swap
    · rw [hi₄, sm.high, writeWord_top (by unfold Layout.top; omega) hk]
    rw [hi₄, sm.high]
    unfold writeWord
    simp [show k ≠ a₀ + 4 * j.toNat by omega, show k ≠ a₀ + 4 * j.toNat + 1 by omega,
      show k ≠ a₀ + 4 * j.toNat + 2 by omega, show k ≠ a₀ + 4 * j.toNat + 3 by omega]

theorem eval_ofList (st : St) : ∀ es : List Exp,
    (Exp.ofList es).eval st = .list (es.map (·.eval st))
  | [] => rfl
  | e :: es => by simp [Exp.ofList, Exp.eval, eval_ofList st es]

theorem depth_le_maxDepth : ∀ {es : List Exp} {e : Exp}, e ∈ es → depth e ≤ maxDepth es
  | _ :: _, _, .head _ => le_max_left _ _
  | _ :: _, _, .tail _ h => le_trans (depth_le_maxDepth h) (le_max_right _ _)

/-- **Several expressions**, one after the other: their values are pushed in order. -/
theorem push_runs (L : Layout) (hL : L.Ok) (st : St) (rest : List UInt8) :
    ∀ (es : List Exp) (s : State), (∀ e ∈ es, Fits L st e) →
      At L st s (ecodes L es ++ rest) (es.length + maxDepth es) →
      ∃ s', Steps s s' ∧ WF s' ∧ getIP s' = getIP s + (ecodes L es).length ∧
        dstack s' = dstack s ++ es.map (fun e => enc (e.eval st)) ∧ Same s s'
  | [], s, _, h => ⟨s, .refl, h.wf, by simp [ecodes], by simp, Same.refl s⟩
  | e :: es, s, hf, h => by
    have h' : At L st s (ecode L e ++ (ecodes L es ++ rest))
        (es.length + 1 + max (depth e) (maxDepth es)) := by
      simpa [ecodes, maxDepth, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := exp_runs L hL st e s (hf e (.head _))
      (h'.left (by omega))
    have h₁ := h'.after (d₂ := es.length + maxDepth es) (by omega) w₁ i₁ d₁ sm₁
    obtain ⟨s₂, r₂, w₂, i₂, d₂, sm₂⟩ := push_runs L hL st rest es s₁
      (fun e he => hf e (.tail _ he)) h₁
    refine ⟨s₂, r₁.trans r₂, w₂, by rw [i₂, i₁]; simp [ecodes]; omega, by rw [d₂, d₁]; simp,
      sm₁.trans sm₂⟩

theorem set_take_drop {vs vals : List Value} {k : ℕ} (hk : k < vs.length) (hk' : k < vals.length) :
    (vs.take (k + 1) ++ vals.drop (k + 1)).set k vals[k] = vs.take k ++ vals.drop k := by
  rw [List.take_succ_eq_append_getElem hk, List.drop_eq_getElem_cons hk', List.append_assoc,
    List.set_append_right _ _ (by simp; try omega), List.length_take,
    show k - min k vs.length = 0 by omega]
  rfl

/-- **Storing a list**: the top `k` words of the stack, the first `k` items of
`vals`, go to the array's first `k` cells, which then hold `vals` throughout. -/
theorem store_loop (L : Layout) (hL : L.Ok) {x a₀ cap : ℕ} (hx : L.arrayAt x = some (a₀, cap))
    {st₀ : St} {vs vals : List Value} (hl : vs.length = cap) (hl' : vals.length = cap)
    (hcap : cap < STACKSZ) :
    ∀ k, k ≤ cap → ∀ s, WF s → Running s → 256 ≤ getIP s → getIP s + 6 * k ≤ L.base →
      CodeAt (high s) (getIP s) (storeCode a₀ k) → dstack s = (vals.take k).map enc →
      VarsOk L (high s) (Function.update st₀ x (.list (vs.take k ++ vals.drop k))) →
      ∃ s', Steps s s' ∧ WF s' ∧ Running s' ∧ getIP s' = getIP s + 6 * k ∧ dstack s' = [] ∧
        VarsOk L (high s') (Function.update st₀ x (.list vals)) ∧ Keeps L s s'
  | 0, _, s, w, r, _, _, _, d, v => ⟨s, .refl, w, r, rfl, by simpa using d, by simpa using v,
      (Same.refl s).keeps⟩
  | k + 1, hk, s, w, r, lo, hi, c, d, v => by
    have hb := L.arrayAt_bounds hx
    have hL1 := hL.1; have hL2 := hL.2
    have hi' : getIP s + 6 * (k + 1) + 8 < MAXBYTE := by omega
    have hkv : k < vals.length := by omega
    have hd : dstack s = (vals.take k).map enc ++ [enc vals[k]] := by
      rw [d, List.take_succ_eq_append_getElem hkv, List.map_append]; rfl
    have hA : At L (Function.update st₀ x (.list (vs.take (k + 1) ++ vals.drop (k + 1)))) s
        ((0x97 :: le4 (UInt32.ofNat (a₀ + 4 * k))) ++ ([0x95] ++ storeCode a₀ k)) 1 :=
      ⟨w, r, lo, by simp; omega, by simpa [storeCode] using c, v,
        by rw [d]; simp; omega⟩
    obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_li hA le_rfl
    have hop : high (step s) (getIP (step s)) = 0x95 := by
      rw [sm₁.high, i₁]; simpa using (CodeAt.append.mp hA.code).2 0 (by simp)
    have hlo₁ : 256 ≤ getIP (step s) := by rw [i₁]; omega
    have hA₀ : (UInt32.ofNat (a₀ + 4 * k)).toNat = a₀ + 4 * k :=
      toNat_ofNat_addr (by unfold MAXBYTE at *; omega)
    have hd₁ : dstack (step s) = (vals.take k).map enc ++ [enc vals[k], UInt32.ofNat (a₀ + 4 * k)] := by
      rw [d₁, hd]; simp
    obtain ⟨w₂, i₂, d₂, c₂, st₂, db₂, hi₂, o₂⟩ := step_wi (step s) _ (enc vals[k])
      (UInt32.ofNat (a₀ + 4 * k)) w₁ hlo₁ (by rw [i₁]; unfold MAXBYTE at *; omega) hop hd₁
      (by rw [hA₀]; omega) (by rw [hA₀]; unfold MAXBYTE at *; omega)
    have hclk := step_wi_clk (step s) _ (enc vals[k]) (UInt32.ofNat (a₀ + 4 * k)) w₁ hlo₁ hop hd₁
      (by rw [hA₀]; omega)
    rw [hA₀] at hi₂
    have hr₁ : Running (step s) := sm₁.running r
    have hr₂ : Running (step (step s)) := ⟨st₂.trans hr₁.1, db₂.trans hr₁.2⟩
    have hv₂ : VarsOk L (high (step (step s)))
        (Function.update st₀ x (.list (vs.take k ++ vals.drop k))) := by
      have := varsOk_store (v := vals[k]) (j := k) v hx (by rw [Function.update_self]) (by omega)
      rw [Function.update_idem, set_take_drop (by omega) hkv] at this
      rw [hi₂, sm₁.high]; exact this
    obtain ⟨s', r', w', run', i', d', v', k'⟩ := store_loop L hL hx hl hl' hcap k (by omega)
      (step (step s)) w₂ hr₂ (by rw [i₂, i₁]; omega) (by rw [i₂, i₁]; omega)
      (by
        rw [hi₂, sm₁.high, i₂, i₁]
        have hc := (CodeAt.append.mp (CodeAt.append.mp hA.code).2).2
        refine fun j hj => ?_
        have hj' := hc j hj
        have hjl := length_storeCode a₀ k
        unfold writeWord
        simp at hj' ⊢
        split_ifs <;> omega)
      (by rw [d₂]) hv₂
    refine ⟨s', ((Steps.one r (notIo_li hA)).tail ⟨hr₁, notIo_of_hop hlo₁ hop (by decide), rfl⟩).trans r',
      w', run', by rw [i', i₂, i₁]; omega, d', v', ?_⟩
    refine (sm₁.keeps.trans ⟨fun i hi => ?_, by rw [c₂], by rw [o₂], by rw [hclk], fun i hi => ?_⟩).trans k'
    · rw [hi₂]
      unfold writeWord
      simp [show i ≠ a₀ + 4 * k by omega, show i ≠ a₀ + 4 * k + 1 by omega,
        show i ≠ a₀ + 4 * k + 2 by omega, show i ≠ a₀ + 4 * k + 3 by omega]
    · rw [hi₂, writeWord_top (by unfold Layout.top; omega) hi]

/-- **`A:= [e₀; …; eₖ₋₁]`**: push every item, then store them from the last. -/
theorem fill_runs (L : Layout) (hL : L.Ok) {d x a₀ : ℕ} {es : List Exp} {st : St} {vs : List Value}
    (hx : L.arrayAt x = some (a₀, es.length)) (hvs : st x = .list vs) (hl : vs.length = es.length)
    (hf : ∀ e ∈ es, Fits L st e) :
    SRuns L d (.fill x es) st (Function.update st x ((Exp.ofList es).eval st)) := by
  intro s a h
  have hcode := h.code
  simp only [scode, hx] at hcode
  have hhi := h.hi; simp only [slen, hx] at hhi
  have hdep := h.depth; simp only [sdepth] at hdep
  have hL2 := hL.2
  have hA : At L st s (ecodes L es ++ storeCode a₀ es.length) (es.length + maxDepth es) :=
    ⟨h.wf, h.run, h.ip ▸ h.lo, by rw [h.ip]; simp; omega, by rw [h.ip]; exact hcode, h.vars,
      by rw [h.stack]; simp; omega⟩
  obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := push_runs L hL st _ es s hf hA
  rw [h.stack, List.nil_append] at d₁
  obtain ⟨s', r', w', run', i', d', v', k'⟩ := store_loop L hL hx (st₀ := st) hl
    (vals := es.map (·.eval st)) (by simp) (by omega) es.length le_rfl s₁ w₁ (sm₁.running h.run)
    (by rw [i₁, h.ip]; have := h.lo; omega) (by rw [i₁, h.ip]; omega)
    (by rw [sm₁.high, i₁]; exact (CodeAt.append.mp hA.code).2)
    (by rw [d₁, List.take_of_length_le (by simp)]; simp)
    (by
      rw [List.take_of_length_le (by omega), List.drop_of_length_le (by simp), List.append_nil,
        ← hvs, Function.update_eq_self, sm₁.high]
      exact h.vars)
  refine ⟨s', r₁.trans r', w', run', by rw [i', i₁, h.ip]; simp [slen, hx]; omega, d', ?_,
    sm₁.keeps.trans k'⟩
  rw [eval_ofList]; exact v'

@[simp] theorem length_jmTo (t : ℕ) : (jmTo t).length = 5 := rfl
@[simp] theorem length_test : test.length = 3 := rfl

/-- The pieces of an `if`'s code. -/
theorem cond_code {L : Layout} {m : ℕ → UInt8} {a : ℕ} {c : Exp} {p q : Stmt}
    (h : CodeAt m a (scode L a (.cond c p q))) :
    let t := a + (ecode L c).length + 8
    let el := t + slen L p + 5
    CodeAt m a (ecode L c) ∧ CodeAt m (a + (ecode L c).length) test ∧
      CodeAt m (a + (ecode L c).length + 3) (jmTo el) ∧ CodeAt m t (scode L t p) ∧
      CodeAt m (t + slen L p) (jmTo (el + slen L q)) ∧ CodeAt m el (scode L el q) := by
  simp only [scode] at h
  rw [CodeAt.append, CodeAt.append, CodeAt.append, CodeAt.append, CodeAt.append] at h
  obtain ⟨⟨⟨⟨⟨hE, hT⟩, hJ⟩, hP⟩, hJ'⟩, hQ⟩ := h
  simp only [List.length_append, length_test, length_jmTo, length_scode] at hT hJ hP hJ' hQ
  refine ⟨hE, hT, by convert hJ using 1, by convert hP using 1, by convert hJ' using 1; omega,
    by convert hQ using 1; omega⟩

/-- The pieces of a `while`'s code. -/
theorem loop_code {L : Layout} {m : ℕ → UInt8} {a : ℕ} {c : Exp} {p : Stmt}
    (h : CodeAt m a (scode L a (.loop c p))) :
    let b := a + (ecode L c).length + 8
    CodeAt m a (ecode L c) ∧ CodeAt m (a + (ecode L c).length) test ∧
      CodeAt m (a + (ecode L c).length + 3) (jmTo (b + slen L p + 5)) ∧
      CodeAt m b (scode L b p) ∧ CodeAt m (b + slen L p) (jmTo a) := by
  simp only [scode] at h
  rw [CodeAt.append, CodeAt.append, CodeAt.append, CodeAt.append] at h
  obtain ⟨⟨⟨⟨hE, hT⟩, hJ⟩, hP⟩, hJ'⟩ := h
  simp only [List.length_append, length_test, length_jmTo, length_scode] at hT hJ hP hJ'
  refine ⟨hE, hT, by convert hJ using 1, by convert hP using 1, by convert hJ' using 1; omega⟩

/-- The condition of an `if` or `while` at the pointer: compute it, test it. -/
theorem run_cond {L : Layout} (hL : L.Ok) {st : St} {s : State} {a : ℕ} {c : Exp} {b : Bool}
    {rest : List UInt8} (hf : Fits L st c) (hc : c.eval st = .bool b) (hw : WF s) (hr : Running s)
    (hip : getIP s = a) (hlo : 256 ≤ a) (hhi : a + (ecode L c).length + 3 + rest.length ≤ L.base)
    (hcode : CodeAt (high s) a (ecode L c ++ test ++ rest)) (hv : VarsOk L (high s) st)
    (hd : dstack s = []) (hdep : depth c ≤ STACKSZ) :
    ∃ s', Steps s s' ∧ WF s' ∧ Running s' ∧
      getIP s' = (if b then a + (ecode L c).length + 8 else a + (ecode L c).length + 3) ∧
      dstack s' = [] ∧ Same s s' := by
  have hA : At L st s (ecode L c ++ (test ++ rest)) (depth c) :=
    ⟨hw, hr, hip ▸ hlo, by have := hL.2; simp; omega, by rw [hip, ← List.append_assoc]; exact hcode,
      hv, by rw [hd]; simpa using hdep⟩
  obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := exp_runs L hL st c s hf (hA.left le_rfl)
  have hc₁ := (CodeAt.append.mp (CodeAt.append.mp hcode).1).2
  rw [← sm₁.high, ← hip, ← i₁] at hc₁
  obtain ⟨s₂, r₂, w₂, i₂, d₂, sm₂⟩ := run_test (b := b) w₁ (sm₁.running hr)
    (by rw [i₁, hip]; omega) (by rw [i₁, hip]; have := hL.2; omega) hc₁
    (by rw [d₁, hd, hc]; rfl)
  refine ⟨s₂, r₁.trans r₂, w₂, sm₂.running (sm₁.running hr), by rw [i₂, i₁, hip], d₂, sm₁.trans sm₂⟩

/-- `jm` at the end of a statement's code, below the variables. -/
theorem run_jm' {L : Layout} (hL : L.Ok) {s : State} {t : ℕ} (hw : WF s) (hlo : 256 ≤ getIP s)
    (hhi : getIP s + 5 ≤ L.base) (hc : CodeAt (high s) (getIP s) (jmTo t)) (ht : 256 ≤ t)
    (ht' : t ≤ L.base) :
    WF (step s) ∧ getIP (step s) = t ∧ dstack (step s) = dstack s ∧ Same s (step s) :=
  run_jm hw hlo (by have := hL.2; omega) hc ht (by have := hL.2; omega)

/-- **Statements**: the code of a statement, run from a state in which the
variables hold `st`, ends where the code does with the variables holding `st'`,
whenever the language takes `st` to `st'` in 32 bits. -/
theorem stmt_runs (L : Layout) (hL : L.Ok) {d : ℕ} {p : Stmt} {st st' : St}
    (h : SEval L d p st st') : SRuns L d p st st' := by
  induction h with
  | ok =>
    intro s a h
    exact ⟨s, .refl, h.wf, h.run, by rw [h.ip]; rfl, h.stack, h.vars, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | assign hx ha hf => exact assign_runs L hL hx ha hf
  | store hfi hf => exact store_runs L hL hfi hf
  | fill hx hvs hl hf => exact fill_runs L hL hx hvs hl hf
  | @seq _ p q s t u _ _ ih₁ ih₂ =>
    intro σ a h
    have hc := CodeAt.append.mp h.code
    rw [length_scode] at hc
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, v₁, k₁⟩ := ih₁ σ a
      ⟨h.wf, h.run, h.ip, h.lo, by omega, hc.1, h.vars, h.stack, by omega, h.cs, h.image⟩
    obtain ⟨σ₂, r₂, w₂, run₂, i₂, d₂, v₂, k₂⟩ := ih₂ σ₁ (a + slen L p)
      ⟨w₁, run₁, i₁, by omega, by omega,
        hc.2.mono k₁.low (by rw [length_scode]; omega), v₁, d₁, by omega,
        by rw [k₁.cs]; exact h.cs, h.image.mono k₁.low⟩
    exact ⟨σ₂, r₁.trans r₂, w₂, run₂, by rw [i₂]; simp [slen]; omega, d₂, v₂, k₁.trans k₂⟩
  | @condT _ c p q s t hf hc _ ih =>
    intro σ a h
    obtain ⟨hE, hT, hJ, hP, hJ', hQ⟩ := cond_code h.code
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hcode := h.code; simp only [scode] at hcode
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, sm₁⟩ := run_cond (b := true) hL hf hc h.wf h.run h.ip h.lo
      (rest := jmTo _ ++ scode L _ p ++ jmTo _ ++ scode L _ q)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) h.vars
      h.stack (by omega)
    simp only [ite_true] at i₁
    obtain ⟨σ₂, r₂, w₂, run₂, i₂, d₂, v₂, k₂⟩ := ih σ₁ _
      ⟨w₁, run₁, i₁, by omega, by omega, by rw [sm₁.high]; exact hP,
        by rw [sm₁.high]; exact h.vars, d₁, by omega, by rw [sm₁.cs]; exact h.cs,
        by rw [sm₁.high]; exact h.image⟩
    have hJ₂ : CodeAt (high σ₂) (getIP σ₂) (jmTo (a + (ecode L c).length + 8 + slen L p + 5 + slen L q)) := by
      rw [i₂]; exact (hJ'.mono (fun i hi => by rw [k₂.low i hi, sm₁.high]) (by simp; omega))
    obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_jm' hL w₂ (by rw [i₂]; omega) (by rw [i₂]; omega) hJ₂
      (by omega) (by omega)
    refine ⟨step σ₂, (r₁.trans r₂).tail ⟨run₂, notIo_jm (by rw [i₂]; omega) hJ₂, rfl⟩, w₃, sm₃.running run₂, by rw [i₃]; simp [slen]; omega,
      by rw [d₃, d₂], by rw [sm₃.high]; exact v₂, sm₁.keeps.trans (k₂.trans sm₃.keeps)⟩
  | @condF _ c p q s t hf hc _ ih =>
    intro σ a h
    obtain ⟨hE, hT, hJ, hP, hJ', hQ⟩ := cond_code h.code
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hcode := h.code; simp only [scode] at hcode
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, sm₁⟩ := run_cond (b := false) hL hf hc h.wf h.run h.ip h.lo
      (rest := jmTo _ ++ scode L _ p ++ jmTo _ ++ scode L _ q)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) h.vars
      h.stack (by omega)
    simp only [Bool.false_eq_true, ite_false] at i₁
    have hJ₁ := (show CodeAt (high σ₁) (getIP σ₁) (jmTo (a + (ecode L c).length + 8 + slen L p + 5)) by
      rw [i₁, sm₁.high]; exact hJ)
    obtain ⟨w₂, i₂, d₂, sm₂⟩ := run_jm' hL w₁ (by rw [i₁]; omega) (by rw [i₁]; omega)
      hJ₁ (by omega) (by omega)
    obtain ⟨σ₃, r₃, w₃, run₃, i₃, d₃, v₃, k₃⟩ := ih (step σ₁) _
      ⟨w₂, sm₂.running run₁, i₂, by omega, by omega, by rw [sm₂.high, sm₁.high]; exact hQ,
        by rw [sm₂.high, sm₁.high]; exact h.vars, by rw [d₂, d₁], by omega,
        by rw [sm₂.cs, sm₁.cs]; exact h.cs, by rw [sm₂.high, sm₁.high]; exact h.image⟩
    refine ⟨σ₃, (r₁.tail ⟨run₁, notIo_jm (by rw [i₁]; omega) hJ₁, rfl⟩).trans r₃, w₃, run₃, by rw [i₃]; simp [slen]; omega,
      d₃, v₃, sm₁.keeps.trans (sm₂.keeps.trans k₃)⟩
  | @loopT _ c p s t u hf hc _ _ ih₁ ih₂ =>
    intro σ a h
    obtain ⟨hE, hT, hJ, hP, hJ'⟩ := loop_code h.code
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hcode := h.code; simp only [scode] at hcode
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, sm₁⟩ := run_cond (b := true) hL hf hc h.wf h.run h.ip h.lo
      (rest := jmTo _ ++ scode L _ p ++ jmTo a)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) h.vars
      h.stack (by omega)
    simp only [ite_true] at i₁
    obtain ⟨σ₂, r₂, w₂, run₂, i₂, d₂, v₂, k₂⟩ := ih₁ σ₁ _
      ⟨w₁, run₁, i₁, by omega, by omega, by rw [sm₁.high]; exact hP,
        by rw [sm₁.high]; exact h.vars, d₁, by omega, by rw [sm₁.cs]; exact h.cs,
        by rw [sm₁.high]; exact h.image⟩
    have hJ₂ : CodeAt (high σ₂) (getIP σ₂) (jmTo a) := by
      rw [i₂]; exact (hJ'.mono (fun i hi => by rw [k₂.low i hi, sm₁.high]) (by simp; omega))
    obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_jm' hL w₂ (by rw [i₂]; omega) (by rw [i₂]; omega) hJ₂
      (by omega) (by omega)
    have k₃ : Keeps L σ (step σ₂) := sm₁.keeps.trans (k₂.trans sm₃.keeps)
    obtain ⟨σ₄, r₄, w₄, run₄, i₄, d₄, v₄, k₄⟩ := ih₂ (step σ₂) a
      ⟨w₃, sm₃.running run₂, i₃, hlo, h.hi, h.code.mono (fun i hi => k₃.low i hi)
        (by rw [length_scode]; exact h.hi), by rw [sm₃.high]; exact v₂, by rw [d₃, d₂], h.depth,
        by rw [k₃.cs]; exact h.cs, h.image.mono k₃.low⟩
    exact ⟨σ₄, ((r₁.trans r₂).tail ⟨run₂, notIo_jm (by rw [i₂]; omega) hJ₂, rfl⟩).trans r₄, w₄, run₄, i₄, d₄, v₄, k₃.trans k₄⟩
  | @loopF _ c p s hf hc =>
    intro σ a h
    obtain ⟨hE, hT, hJ, hP, hJ'⟩ := loop_code h.code
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hcode := h.code; simp only [scode] at hcode
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, sm₁⟩ := run_cond (b := false) hL hf hc h.wf h.run h.ip h.lo
      (rest := jmTo _ ++ scode L _ p ++ jmTo a)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) h.vars
      h.stack (by omega)
    simp only [Bool.false_eq_true, ite_false] at i₁
    have hJ₁ := (show CodeAt (high σ₁) (getIP σ₁) (jmTo (a + (ecode L c).length + 8 + slen L p + 5)) by
      rw [i₁, sm₁.high]; exact hJ)
    obtain ⟨w₂, i₂, d₂, sm₂⟩ := run_jm' hL w₁ (by rw [i₁]; omega) (by rw [i₁]; omega)
      hJ₁ (by omega) (by omega)
    exact ⟨step σ₁, r₁.tail ⟨run₁, notIo_jm (by rw [i₁]; omega) hJ₁, rfl⟩, w₂, sm₂.running run₁, by rw [i₂]; simp [slen]; omega,
      by rw [d₂, d₁], by rw [sm₂.high, sm₁.high]; exact h.vars, sm₁.keeps.trans sm₂.keeps⟩

  | @call d k s t hk hd _ ih =>
    intro σ a h
    have hcode := h.code; simp only [scode] at hcode
    rw [show (0x9D : UInt8) :: le4 (UInt32.ofNat (L.entry k)) =
      [0x9D] ++ le4 (UInt32.ofNat (L.entry k)) from rfl, CodeAt.append] at hcode
    obtain ⟨he₁, he₂, he₃, he₄⟩ := h.image k hk
    have hb := hL.2
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hop : high σ (getIP σ) = 0x9D := by rw [h.ip]; simpa using hcode.1 0 (by simp)
    have hword : word (high σ) (getIP σ + 1) = UInt32.ofNat (L.entry k) := by
      rw [h.ip]; exact word_le4 (by simpa using hcode.2)
    have hen : (UInt32.ofNat (L.entry k)).toNat = L.entry k := toNat_ofNat_addr (by omega)
    obtain ⟨w₁, i₁, d₁, c₁, f₁⟩ := step_cl σ h.wf (by rw [h.ip]; omega) (by rw [h.ip]; omega) hop
      (by rw [hword, hen]; exact he₁) (by rw [h.cs]; exact hd)
    rw [hword, hen] at i₁
    have hc₂ := CodeAt.append.mp he₄
    rw [length_scode] at hc₂
    have run₁ : Running (step σ) := ⟨f₁.st.trans h.run.1, f₁.db.trans h.run.2⟩
    obtain ⟨σ₂, r₂, w₂, run₂, i₂, d₂, v₂, k₂⟩ := ih (step σ) (L.entry k)
      ⟨w₁, run₁, i₁, he₁, by omega, by rw [f₁.high]; exact hc₂.1, by rw [f₁.high]; exact h.vars,
        by rw [d₁]; exact h.stack, he₃, by rw [c₁]; simp [h.cs], by rw [f₁.high]; exact h.image⟩
    have hop₂ : high σ₂ (getIP σ₂) = 0x9E := by
      rw [i₂, k₂.low _ (by omega), f₁.high]; simpa using hc₂.2 0 (by simp)
    have hret : ((getIP σ + 5).toUInt32).toNat = a + 5 := by
      rw [h.ip]; exact toNat_ofNat_addr (by omega)
    obtain ⟨w₃, i₃, d₃, c₃, f₃⟩ := step_rt σ₂ (cstack σ) (getIP σ + 5).toUInt32 w₂
      (by rw [i₂]; omega) hop₂ (by rw [k₂.cs, c₁]) (by rw [hret]; omega)
    refine ⟨step σ₂, ((Steps.one h.run (notIo_of_hop (by rw [h.ip]; omega) hop)).trans r₂).tail
      ⟨run₂, notIo_of_hop (by rw [i₂]; omega) hop₂, rfl⟩, w₃,
      ⟨f₃.st.trans run₂.1, f₃.db.trans run₂.2⟩, by rw [i₃, hret]; simp [slen],
      by rw [d₃, d₂], by rw [f₃.high]; exact v₂, ⟨fun i hi => by rw [f₃.high, k₂.low i hi, f₁.high],
        c₃, by rw [f₃.ob, k₂.ob, f₁.ob], by rw [f₃.clk, k₂.clk, f₁.clk],
        fun i hi => by rw [f₃.high, k₂.top i hi, f₁.high]⟩⟩
  | @scope d x e p s t hx ha hf hd _ ih =>
    intro σ a h
    have hb := hL.2
    have hhi := h.hi; simp only [slen] at hhi
    have hdep := h.depth; simp only [sdepth] at hdep
    have hlo := h.lo
    have hcode := h.code
    simp only [scode] at hcode
    have hcode' := hcode
    rw [CodeAt.append, CodeAt.append, CodeAt.append] at hcode'
    obtain ⟨⟨⟨hA, hB⟩, hP⟩, hC⟩ := hcode'
    simp only [List.length_append, List.length_cons, length_le4, length_scode] at hB hP hC
    replace hP : CodeAt (high σ) (a + 7 + ((ecode L e).length + 6))
        (scode L (a + 7 + ((ecode L e).length + 6)) p) := by
      exact hP.cast (by first | omega | (simp; omega))
    replace hC : CodeAt (high σ) (a + 7 + ((ecode L e).length + 6) + slen L p)
        ([0x91] ++ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])) := by
      have := hC.cast (b := a + 7 + ((ecode L e).length + 6) + slen L p)
        (by first | omega | (simp; omega))
      rwa [List.append_assoc] at this
    have haddr : L.addr x + 3 < MAXBYTE := by unfold Layout.addr; omega
    have haddr' : 256 ≤ (UInt32.ofNat (L.addr x)).toNat := by
      rw [toNat_ofNat_addr (by omega)]; unfold Layout.addr; have := hL.1; omega
    -- `li x ri dc`: the old value goes on the control stack
    have hAt : At L s σ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x93, 0x90]) 1 :=
      ⟨h.wf, h.run, by rw [h.ip]; omega, by rw [h.ip]; simp; omega, by rw [h.ip]; exact hA, h.vars,
        by rw [h.stack]; simp [STACKSZ]⟩
    obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_li hAt le_rfl
    have hA₂ := (CodeAt.append.mp hA).2
    simp only [List.length_cons, length_le4] at hA₂
    have hop₁ : high (step σ) (getIP (step σ)) = 0x93 := by
      rw [sm₁.high, i₁, h.ip]; simpa using hA₂ 0 (by simp)
    obtain ⟨w₂, i₂, d₂, sm₂⟩ := step_ri (step σ) [] (UInt32.ofNat (L.addr x)) w₁
      (by rw [i₁, h.ip]; omega) (by rw [i₁, h.ip]; unfold MAXBYTE at hb; omega) hop₁
      (by rw [d₁, h.stack]) haddr' (by rw [toNat_ofNat_addr (by omega)]; exact haddr)
    rw [toNat_ofNat_addr (by omega), sm₁.high, h.vars.1 x hx] at d₂
    have hop₂ : high (step (step σ)) (getIP (step (step σ))) = 0x90 := by
      rw [sm₂.high, sm₁.high, i₂, i₁, h.ip]; simpa using hA₂ 1 (by simp)
    obtain ⟨w₃, i₃, d₃, c₃, f₃⟩ := step_dc (step (step σ)) [] (enc (s x)) w₂
      (by rw [i₂, i₁, h.ip]; omega) (by rw [i₂, i₁, h.ip]; unfold MAXBYTE at hb; omega) hop₂ d₂
      (by rw [sm₂.cs, sm₁.cs, h.cs]; exact hd)
    set σ₃ := step (step (step σ)) with hσ₃
    have sm₁₂ := sm₁.trans sm₂
    have run₃ : Running σ₃ := ⟨f₃.st.trans (sm₁₂.running h.run).1, f₃.db.trans (sm₁₂.running h.run).2⟩
    have hip₃ : getIP σ₃ = a + 7 := by rw [i₃, i₂, i₁, h.ip]
    have hcs₃ : cstack σ₃ = cstack σ ++ [enc (s x)] := by rw [c₃, sm₂.cs, sm₁.cs]
    have hhigh₃ : high σ₃ = high σ := by rw [f₃.high, sm₂.high, sm₁.high]
    -- `x:= e`
    obtain ⟨σ₄, r₄, w₄, run₄, i₄, d₄, v₄, k₄⟩ := assign_runs L hL (d := d + 1) hx ha hf σ₃ (a + 7)
      ⟨w₃, run₃, hip₃, by omega, by simp [slen]; omega,
        by rw [hhigh₃]; simpa [scode] using hB, by rw [hhigh₃]; exact h.vars, d₃,
        by simp [sdepth]; omega, by rw [hcs₃]; simp [h.cs], by rw [hhigh₃]; exact h.image⟩
    simp only [slen] at i₄
    -- the body
    obtain ⟨σ₅, r₅, w₅, run₅, i₅, d₅, v₅, k₅⟩ := ih σ₄ (a + 7 + ((ecode L e).length + 6))
      ⟨w₄, run₄, by rw [i₄], by omega, by omega,
        hP.mono (m' := high σ₄) (fun i hi => by rw [k₄.low i hi, hhigh₃])
          (by rw [length_scode]; omega), v₄, d₄, by omega,
        by rw [k₄.cs, hcs₃]; simp [h.cs], (h.image.mono fun i hi => by rw [k₄.low i hi, hhigh₃])⟩
    -- `cd li x wi`: the old value back
    have hk₅ : Keeps L σ₃ σ₅ := k₄.trans k₅
    have hC' : CodeAt (high σ₅) (getIP σ₅)
        ([0x91] ++ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])) := by
      refine (hC.mono (m' := high σ₅) (fun i hi => by rw [hk₅.low i hi, hhigh₃]) ?_).cast ?_
      · simp; omega
      · rw [i₅]
    rw [CodeAt.append] at hC'
    have hop₅ : high σ₅ (getIP σ₅) = 0x91 := by simpa using hC'.1 0 (by simp)
    obtain ⟨w₆, i₆, d₆, c₆, f₆⟩ := step_cd σ₅ (cstack σ) (enc (s x)) w₅ (by rw [i₅]; omega)
      (by rw [i₅]; unfold MAXBYTE at hb; omega) hop₅ (by rw [hk₅.cs, hcs₃]) (by rw [d₅]; simp [STACKSZ])
    have run₆ : Running (step σ₅) := ⟨f₆.st.trans run₅.1, f₆.db.trans run₅.2⟩
    have hAt₆ : At L t (step σ₅) ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]) 1 :=
      ⟨w₆, run₆, by rw [i₆, i₅]; omega, by rw [i₆, i₅]; simp; omega,
        by rw [f₆.high, i₆]; simpa using hC'.2,
        by rw [f₆.high]; exact v₅, by rw [d₆, d₅]; simp [STACKSZ]⟩
    obtain ⟨w₇, i₇, d₇, sm₇⟩ := run_li hAt₆ le_rfl
    have hop₇ : high (step (step σ₅)) (getIP (step (step σ₅))) = 0x95 := by
      rw [sm₇.high, f₆.high, i₇, i₆]
      have := (CodeAt.append.mp hC'.2).2 0 (by simp); simpa using this
    have hip₇ : 256 ≤ getIP (step (step σ₅)) := by rw [i₇, i₆, i₅]; omega
    have hd₇ : dstack (step (step σ₅)) = [] ++ [enc (s x), UInt32.ofNat (L.addr x)] := by
      rw [d₇, d₆, d₅]; rfl
    obtain ⟨w₈, i₈, d₈, c₈, st₈, db₈, hi₈, o₈⟩ := step_wi (step (step σ₅)) [] (enc (s x))
      (UInt32.ofNat (L.addr x)) w₇ hip₇ (by rw [i₇, i₆, i₅]; unfold MAXBYTE at hb; omega) hop₇ hd₇
      haddr' (by rw [toNat_ofNat_addr (by omega)]; exact haddr)
    have hclk₈ := step_wi_clk (step (step σ₅)) [] (enc (s x)) (UInt32.ofNat (L.addr x)) w₇ hip₇
      hop₇ hd₇ haddr'
    rw [toNat_ofNat_addr (by omega)] at hi₈
    have run₇ : Running (step (step σ₅)) := sm₇.running run₆
    refine ⟨step (step (step σ₅)), ?_, w₈, ⟨st₈.trans run₇.1, db₈.trans run₇.2⟩, ?_, d₈, ?_, ?_⟩
    · refine ((((((Steps.one h.run (notIo_li hAt)).tail ⟨sm₁.running h.run,
        notIo_of_hop (by rw [i₁, h.ip]; omega) hop₁, rfl⟩).tail ⟨sm₁₂.running h.run,
        notIo_of_hop (by rw [i₂, i₁, h.ip]; omega) hop₂, rfl⟩).trans r₄).trans r₅).tail
        ⟨run₅, notIo_of_hop (by rw [i₅]; omega) hop₅, rfl⟩).tail
        ⟨run₆, notIo_li hAt₆, rfl⟩ |>.tail ⟨run₇, notIo_of_hop hip₇ hop₇, rfl⟩
    · rw [i₈, i₇, i₆, i₅]; simp [slen]; omega
    · rw [hi₈, sm₇.high, f₆.high]; exact varsOk_write v₅ hx ha
    · refine ⟨fun i hi => ?_, by rw [c₈, sm₇.cs, c₆], by rw [o₈, sm₇.ob, f₆.ob, hk₅.ob, f₃.ob,
        sm₂.ob, sm₁.ob], by rw [hclk₈, sm₇.clk, f₆.clk, hk₅.clk, f₃.clk, sm₂.clk, sm₁.clk],
        fun i hi => ?_⟩
      swap
      · rw [hi₈, sm₇.high, f₆.high, writeWord_top (by unfold Layout.addr Layout.top; omega) hi,
          ← hhigh₃, ← hk₅.top i hi]
      rw [hi₈, sm₇.high, f₆.high, ← hhigh₃, ← hk₅.low i hi]
      unfold writeWord Layout.addr
      have : i < L.base := hi
      simp [show i ≠ L.base + 4 * x by omega, show i ≠ L.base + 4 * x + 1 by omega,
        show i ≠ L.base + 4 * x + 2 by omega, show i ≠ L.base + 4 * x + 3 by omega]

/-! ### A scope's start and end, on their own -/

/-- `li x ri dc`, a scope's start: the variable's old value goes on the control
stack. -/
theorem enter_runs (L : Layout) (hL : L.Ok) {s : State} {st : St} {x : ℕ} (hx : x < L.n)
    (hw : WF s) (hr : Running s) (hlo : 256 ≤ getIP s) (hhi : getIP s + 7 ≤ L.base)
    (hc : CodeAt (high s) (getIP s) ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x93, 0x90]))
    (hv : VarsOk L (high s) st) (hd : dstack s = []) (hcs : (cstack s).length < STACKSZ) :
    ∃ s', Steps s s' ∧ WF s' ∧ Running s' ∧ getIP s' = getIP s + 7 ∧ dstack s' = [] ∧
      cstack s' = cstack s ++ [enc (st x)] ∧ Frame s s' := by
  have hb := hL.2
  have haddr : L.addr x + 3 < MAXBYTE := by unfold Layout.addr; omega
  have haddr' : 256 ≤ (UInt32.ofNat (L.addr x)).toNat := by
    rw [toNat_ofNat_addr (by omega)]; unfold Layout.addr; have := hL.1; omega
  have hAt : At L st s ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x93, 0x90]) 1 :=
    ⟨hw, hr, hlo, by simp; omega, hc, hv, by rw [hd]; simp [STACKSZ]⟩
  obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_li hAt le_rfl
  have hA₂ := (CodeAt.append.mp hc).2
  simp only [List.length_cons, length_le4] at hA₂
  have hop₁ : high (step s) (getIP (step s)) = 0x93 := by
    rw [sm₁.high, i₁]; simpa using hA₂ 0 (by simp)
  obtain ⟨w₂, i₂, d₂, sm₂⟩ := step_ri (step s) [] (UInt32.ofNat (L.addr x)) w₁
    (by rw [i₁]; omega) (by rw [i₁]; unfold MAXBYTE at hb; omega) hop₁
    (by rw [d₁, hd]) haddr' (by rw [toNat_ofNat_addr (by omega)]; exact haddr)
  rw [toNat_ofNat_addr (by omega), sm₁.high, hv.1 x hx] at d₂
  have hop₂ : high (step (step s)) (getIP (step (step s))) = 0x90 := by
    rw [sm₂.high, sm₁.high, i₂, i₁]; simpa using hA₂ 1 (by simp)
  obtain ⟨w₃, i₃, d₃, c₃, f₃⟩ := step_dc (step (step s)) [] (enc (st x)) w₂
    (by rw [i₂, i₁]; omega) (by rw [i₂, i₁]; unfold MAXBYTE at hb; omega) hop₂ d₂
    (by rw [sm₂.cs, sm₁.cs]; exact hcs)
  have sm₁₂ := sm₁.trans sm₂
  refine ⟨step (step (step s)), ((Steps.one hr (notIo_li hAt)).tail ⟨sm₁.running hr,
      notIo_of_hop (by rw [i₁]; omega) hop₁, rfl⟩).tail ⟨sm₁₂.running hr,
      notIo_of_hop (by rw [i₂, i₁]; omega) hop₂, rfl⟩, w₃,
    ⟨f₃.st.trans (sm₁₂.running hr).1, f₃.db.trans (sm₁₂.running hr).2⟩,
    by rw [i₃, i₂, i₁], d₃, by rw [c₃, sm₂.cs, sm₁.cs], (Frame.of_same sm₁₂).trans f₃⟩

/-- `cd li x wi`, a scope's end: the variable gets its old value back from the
control stack. -/
theorem restore_runs (L : Layout) (hL : L.Ok) {s : State} {st : St} {x : ℕ} {v : Value}
    {cs : List UInt32} (hx : x < L.n) (ha : L.arrayAt x = none) (hw : WF s) (hr : Running s)
    (hlo : 256 ≤ getIP s) (hhi : getIP s + 7 ≤ L.base)
    (hc : CodeAt (high s) (getIP s) ([0x91] ++ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])))
    (hv : VarsOk L (high s) st) (hd : dstack s = []) (hcs : cstack s = cs ++ [enc v]) :
    ∃ s', Steps s s' ∧ WF s' ∧ Running s' ∧ getIP s' = getIP s + 7 ∧ dstack s' = [] ∧
      cstack s' = cs ∧ VarsOk L (high s') (Function.update st x v) ∧
      (∀ i < L.base, high s' i = high s i) ∧ s'.ob = s.ob ∧ getClk s' = getClk s ∧
      (∀ i, L.top ≤ i → high s' i = high s i) := by
  have hb := hL.2
  have haddr : L.addr x + 3 < MAXBYTE := by unfold Layout.addr; omega
  have haddr' : 256 ≤ (UInt32.ofNat (L.addr x)).toNat := by
    rw [toNat_ofNat_addr (by omega)]; unfold Layout.addr; have := hL.1; omega
  rw [CodeAt.append] at hc
  have hop₅ : high s (getIP s) = 0x91 := by simpa using hc.1 0 (by simp)
  obtain ⟨w₆, i₆, d₆, c₆, f₆⟩ := step_cd s cs (enc v) hw hlo
    (by unfold MAXBYTE at hb; omega) hop₅ hcs (by rw [hd]; simp [STACKSZ])
  have run₆ : Running (step s) := ⟨f₆.st.trans hr.1, f₆.db.trans hr.2⟩
  have hAt₆ : At L st (step s) ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]) 1 :=
    ⟨w₆, run₆, by rw [i₆]; omega, by rw [i₆]; simp; omega,
      by rw [f₆.high, i₆]; simpa using hc.2, by rw [f₆.high]; exact hv,
      by rw [d₆, hd]; simp [STACKSZ]⟩
  obtain ⟨w₇, i₇, d₇, sm₇⟩ := run_li hAt₆ le_rfl
  have hop₇ : high (step (step s)) (getIP (step (step s))) = 0x95 := by
    rw [sm₇.high, f₆.high, i₇, i₆]
    have := (CodeAt.append.mp hc.2).2 0 (by simp); simpa using this
  have hip₇ : 256 ≤ getIP (step (step s)) := by rw [i₇, i₆]; omega
  have hd₇ : dstack (step (step s)) = [] ++ [enc v, UInt32.ofNat (L.addr x)] := by
    rw [d₇, d₆, hd]; rfl
  obtain ⟨w₈, i₈, d₈, c₈, st₈, db₈, hi₈, o₈⟩ := step_wi (step (step s)) [] (enc v)
    (UInt32.ofNat (L.addr x)) w₇ hip₇ (by rw [i₇, i₆]; unfold MAXBYTE at hb; omega) hop₇ hd₇
    haddr' (by rw [toNat_ofNat_addr (by omega)]; exact haddr)
  have hclk₈ := step_wi_clk (step (step s)) [] (enc v) (UInt32.ofNat (L.addr x)) w₇ hip₇
    hop₇ hd₇ haddr'
  rw [toNat_ofNat_addr (by omega)] at hi₈
  have run₇ : Running (step (step s)) := sm₇.running run₆
  refine ⟨step (step (step s)), ((Steps.one hr (notIo_of_hop hlo hop₅)).tail
      ⟨run₆, notIo_li hAt₆, rfl⟩).tail ⟨run₇, notIo_of_hop hip₇ hop₇, rfl⟩, w₈,
    ⟨st₈.trans run₇.1, db₈.trans run₇.2⟩, by rw [i₈, i₇, i₆], d₈,
    by rw [c₈, sm₇.cs, c₆], ?_, ?_, by rw [o₈, sm₇.ob, f₆.ob], by rw [hclk₈, sm₇.clk, f₆.clk],
    fun i hi => by rw [hi₈, sm₇.high, f₆.high, writeWord_top (by unfold Layout.addr Layout.top; omega) hi]⟩
  · rw [hi₈, sm₇.high, f₆.high]; exact varsOk_write hv hx ha
  · intro i hi
    rw [hi₈, sm₇.high, f₆.high]
    unfold writeWord Layout.addr
    simp [show i ≠ L.base + 4 * x by omega, show i ≠ L.base + 4 * x + 1 by omega,
      show i ≠ L.base + 4 * x + 2 by omega, show i ≠ L.base + 4 * x + 3 by omega]

/-! ### Whole programs -/

/-- A running machine takes its steps under `runN`. -/
theorem runN_of_steps {s s' : State} (h : Steps s s') : ∃ n, runN n s = s' := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨hr, -, rfl⟩ := hab
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [runN_succ_of_running _ _ hr, hn]⟩

/-- A stopped machine stays as it is. -/
theorem runN_of_stopped (n : ℕ) {s : State} (h : getRST s = 0) : runN n s = s := by
  cases n with
  | zero => rfl
  | succ n => simp [runN, h]

/-! ### Programs with named statements -/

/-- A named statement's code: its body, then `rt`. -/
def Layout.block (L : Layout) (k : ℕ) : List UInt8 := scode L (L.entry k) (L.defs k) ++ [0x9E]

/-- The named statements' code, end to end. -/
def Layout.blocks (L : Layout) : List ℕ → List UInt8
  | [] => []
  | k :: ks => L.block k ++ L.blocks ks

/-- The named statements `ks` are laid end to end from `a`: each entry is where
its code starts. -/
def Layout.Laid (L : Layout) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, k :: ks => L.entry k = a ∧ L.Laid (a + slen L (L.defs k) + 1) ks

@[simp] theorem Layout.length_block (L : Layout) (k : ℕ) :
    (L.block k).length = slen L (L.defs k) + 1 := by
  simp [Layout.block, length_scode]

/-- Laid end to end, the named statements' code gives the image a call needs. -/
theorem Layout.image_of_laid (L : Layout) {m : ℕ → UInt8} : ∀ (ks : List ℕ) (a : ℕ),
    L.Laid a ks → CodeAt m a (L.blocks ks) → 256 ≤ a → a + (L.blocks ks).length ≤ L.base →
    (∀ k ∈ ks, sdepth (L.defs k) ≤ STACKSZ) → ∀ k ∈ ks, 256 ≤ L.entry k ∧
      L.entry k + slen L (L.defs k) + 1 ≤ L.base ∧ sdepth (L.defs k) ≤ STACKSZ ∧
      CodeAt m (L.entry k) (scode L (L.entry k) (L.defs k) ++ [0x9E])
  | [], _, _, _, _, _, _ => fun _ hk => absurd hk (by simp)
  | k :: ks, a, ⟨he, hl⟩, hc, ha, hb, hd => by
    rw [Layout.blocks, CodeAt.append, Layout.length_block] at hc
    simp only [Layout.blocks, List.length_append, Layout.length_block] at hb
    intro k' hk'
    by_cases h : k' = k
    · subst h
      have h₁ := hc.1
      rw [Layout.block, he] at h₁
      exact ⟨by omega, by omega, hd _ (by simp), by rw [he]; exact h₁⟩
    · exact L.image_of_laid ks _ hl hc.2 (by omega) (by omega)
        (fun j hj => hd j (by simp [hj])) k' (by simpa [h] using hk')

/-- Where the main statement's code starts: after the named statements', which
start at `0x100`, the start of code. -/
def Layout.start (L : Layout) : ℕ := 0x100 + (L.blocks L.keys).length

/-- The program: the named statements' code from `0x100`, then the main
statement's code and `hl`. -/
def compile (L : Layout) (p : Stmt) : List UInt8 := L.blocks L.keys ++ (scode L L.start p ++ [0xFF])

@[simp] theorem length_compile (L : Layout) (p : Stmt) :
    (compile L p).length = (L.blocks L.keys).length + (slen L p + 1) := by
  simp [compile, length_scode]

/-- What loading a program `p` needs of its layout: the named statements laid out
from `0x100`, the main code and its `hl` after them, everything below the
variables, and the stack depths within bounds. -/
structure Layout.Fit (L : Layout) (p : Stmt) : Prop where
  /-- The named statements are laid out from `0x100`. -/
  laid : L.Laid 0x100 L.keys
  /-- The main code and its `hl` end below the variables. -/
  hi : L.start + slen L p + 1 ≤ L.base
  /-- The main statement's stack fits. -/
  depth : sdepth p ≤ STACKSZ
  /-- Each named statement's stack fits. -/
  depths : ∀ k ∈ L.keys, sdepth (L.defs k) ≤ STACKSZ

/-- The image a call needs, from the loaded program. -/
theorem Layout.image_of_compile (L : Layout) {m : ℕ → UInt8} {p : Stmt} (hF : L.Fit p)
    (hc : CodeAt m 0x100 (compile L p)) : L.Image m := by
  have hfit := hF.hi
  unfold Layout.start at hfit
  rw [compile, CodeAt.append] at hc
  exact L.image_of_laid L.keys _ hF.laid hc.1 (by omega) (by omega) hF.depths

/-- The main code, from the loaded program. -/
theorem Layout.main_of_compile (L : Layout) {m : ℕ → UInt8} {p : Stmt}
    (hc : CodeAt m 0x100 (compile L p)) :
    CodeAt m L.start (scode L L.start p) ∧ m (L.start + slen L p) = 0xFF := by
  rw [compile, CodeAt.append, CodeAt.append] at hc
  obtain ⟨-, h₁, h₂⟩ := hc
  rw [length_scode] at h₂
  exact ⟨h₁, by have := h₂ 0 (by simp); simpa [Layout.start] using this⟩

/-- **The compiler is correct.** Load the compiled program at `0x100` with the
variables, in their cells above it, holding `st`, and start the machine at the
main code with empty stacks: if the language takes `st` to `st'` without
leaving 32 bits (`SEval`, which is an execution of the language:
`eval_of_sEval`), the machine halts with the variables holding `st'`. -/
theorem compile_correct (L : Layout) (hL : L.Ok) {p : Stmt} {st st' : St} (h : SEval L 0 p st st')
    (hF : L.Fit p) (s : State) (hw : WF s) (hr : Running s) (hip : getIP s = L.start)
    (hc : CodeAt (high s) 0x100 (compile L p)) (hv : VarsOk L (high s) st) (hd : dstack s = [])
    (hcs : cstack s = []) :
    ∃ n, getRST (runN n s) = 0 ∧ VarsOk L (high (runN n s)) st' := by
  have hfit := hF.hi
  have hs : 256 ≤ L.start := by unfold Layout.start; omega
  have himg := L.image_of_compile hF hc
  obtain ⟨hc₁, hc₂⟩ := L.main_of_compile hc
  obtain ⟨s', r', w', run', i', d', v', k'⟩ := stmt_runs L hL h s L.start
    ⟨hw, hr, hip, hs, by omega, hc₁, hv, hd, hF.depth, by rw [hcs]; rfl, himg⟩
  have hop : high s' (getIP s') = 0xFF := by
    rw [i', k'.low _ (by omega)]; exact hc₂
  have hst : getRST (step s') = 0 := step_hl s' w' (by rw [i']; omega) hop
  have hhigh : high (step s') = high s' := by
    rw [step_of s' _ (by rw [i']; omega) hop, runOp_hl]; simp
  obtain ⟨n, hn⟩ := runN_of_steps (r'.tail ⟨run', notIo_of_hop (by rw [i']; omega) hop, rfl⟩)
  exact ⟨n, by rw [hn]; exact hst, by rw [hn, hhigh]; exact v'⟩

/-! ### Building layouts -/

theorem arrFrom_isSome : ∀ (l : List (ℕ × ℕ)) (a b x : ℕ),
    (arrFrom a l x).isSome = (arrFrom b l x).isSome
  | [], _, _, _ => rfl
  | (y, _) :: rest, a, b, x => by
    simp only [arrFrom]; split_ifs
    · rfl
    · exact arrFrom_isSome rest _ _ x

theorem Layout.arrayAt_isSome {L L' : Layout} (h : L.arrays = L'.arrays) (x : ℕ) :
    (L.arrayAt x).isSome = (L'.arrayAt x).isSome := by
  unfold Layout.arrayAt; rw [h]; exact arrFrom_isSome _ _ _ x

/-- How long a statement's code is does not depend on the layout, only on which
variables are arrays. -/
theorem length_ecode_congr (L L' : Layout) (h : ∀ x, (L.arrayAt x).isSome = (L'.arrayAt x).isSome)
    (e : Exp) :
    (ecode L e).length = (ecode L' e).length := by
  induction e with
  | un op a ih =>
    cases op
    case len =>
      cases a with
      | var x =>
        have := h x
        cases h₁ : L.arrayAt x <;> cases h₂ : L'.arrayAt x <;> simp_all [ecode]
      | _ => rfl
    all_goals simp [ecode, ih]
  | bin op a b iha ihb => simp [ecode, iha, ihb]
  | lit => rfl
  | var => rfl
  | nil => rfl
  | cons => rfl
  | index a i _ ihi =>
    cases a with
    | var x =>
      have := h x
      cases h₁ : L.arrayAt x <;> cases h₂ : L'.arrayAt x <;> simp_all [ecode]
    | _ => rfl
  | cond c a b ihc iha ihb => simp [ecode, ihc, iha, ihb]

theorem slen_congr (L L' : Layout) (h : ∀ x, (L.arrayAt x).isSome = (L'.arrayAt x).isSome) :
    ∀ p : Stmt, slen L p = slen L' p := by
  intro p
  induction p with
  | store x i e =>
    have := h x
    cases h₁ : L.arrayAt x <;> cases h₂ : L'.arrayAt x <;>
      simp_all [slen, length_ecode_congr L L' h]
  | fill x es =>
    have := h x
    have hes : (ecodes L es).length = (ecodes L' es).length := by
      induction es with
      | nil => rfl
      | cons e es ih => simp [ecodes, length_ecode_congr L L' h e, ih]
    cases h₁ : L.arrayAt x <;> cases h₂ : L'.arrayAt x <;> simp_all [slen]
  | _ => simp_all [slen, length_ecode_congr L L' h]

/-- Entries for the names `ks`, laid end to end from `a`. -/
def Layout.place (L : Layout) (a : ℕ) : List ℕ → ℕ → ℕ
  | [] => fun _ => 0
  | k :: ks => fun j => if j = k then a else L.place (a + slen L (L.defs k) + 1) ks j

theorem Layout.laid_of_place (L L₀ : Layout) (hd : L.defs = L₀.defs) (ha : L.arrays = L₀.arrays) :
    ∀ (ks : List ℕ) (a : ℕ), ks.Nodup → (∀ k ∈ ks, L.entry k = L₀.place a ks k) → L.Laid a ks
  | [], _, _, _ => trivial
  | k :: ks, a, hn, he => by
    refine ⟨by simpa [Layout.place] using he k (by simp), ?_⟩
    rw [List.nodup_cons] at hn
    refine L.laid_of_place L₀ hd ha ks _ hn.2 fun j hj => ?_
    rw [he j (by simp [hj]), Layout.place, hd, slen_congr L L₀ (L.arrayAt_isSome ha)]
    simp [show j ≠ k by rintro rfl; exact hn.1 hj]

/-- The layout's variables and named statements, before placing them. -/
def Layout.named (base n : ℕ) (defs : List (ℕ × Stmt)) (arrays : List (ℕ × ℕ) := []) : Layout :=
  { base := base, n := n, defs := fun k => (defs.lookup k).getD .ok, keys := defs.map Prod.fst,
    arrays := arrays }

/-- A layout for named statements `defs`: variables `0` to `n - 1` at `base`,
the named statements laid out from `0x100`. -/
def Layout.build (base n : ℕ) (defs : List (ℕ × Stmt)) (arrays : List (ℕ × ℕ) := []) : Layout :=
  let L₀ := Layout.named base n defs arrays
  { L₀ with entry := L₀.place 0x100 L₀.keys }

theorem Layout.build_laid (base n : ℕ) (defs : List (ℕ × Stmt)) (arrays : List (ℕ × ℕ))
    (h : (defs.map Prod.fst).Nodup) :
    (Layout.build base n defs arrays).Laid 0x100 (Layout.build base n defs arrays).keys :=
  (Layout.build base n defs arrays).laid_of_place (Layout.named base n defs arrays) rfl rfl _ _ h
    fun _ _ => rfl

/-! ### Loading -/

/-- Write bytes into memory from address `a`. -/
def writeBytes (m : ByteArray) (a : ℕ) : List UInt8 → ByteArray
  | [] => m
  | b :: bs => writeBytes (m.set! a b) (a + 1) bs

@[simp] theorem size_writeBytes (m : ByteArray) (a : ℕ) (bs : List UInt8) :
    (writeBytes m a bs).size = m.size := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => simp [writeBytes, ih]

theorem get!_writeBytes (m : ByteArray) (a : ℕ) (bs : List UInt8) (hs : a + bs.length ≤ m.size)
    (i : ℕ) : (writeBytes m a bs).get! i =
      if a ≤ i ∧ i < a + bs.length then bs.getD (i - a) 0 else m.get! i := by
  induction bs generalizing m a with
  | nil => simp [writeBytes]
  | cons b bs ih =>
    simp only [writeBytes]
    rw [ih _ _ (by simp at hs ⊢; omega)]
    simp only [List.length_cons]
    by_cases h₁ : a + 1 ≤ i ∧ i < a + 1 + bs.length
    · rw [ite_eq_left h₁, ite_eq_left (by omega)]
      rw [show i - a = (i - (a + 1)) + 1 by omega]; rfl
    · rw [ite_eq_right h₁]
      by_cases h₂ : i = a
      · subst h₂; rw [get!_set!_self _ _ _ (by simp at hs; omega), ite_eq_left (by omega)]; simp
      · rw [get!_set!_ne _ _ _ _ (Ne.symm h₂), ite_eq_right (by omega)]

/-- Write the variables' cells, `0` to `k - 1`. -/
def writeVars (L : Layout) (st : St) (m : ByteArray) : ℕ → ByteArray
  | 0 => m
  | k + 1 => setVal (writeVars L st m k) (L.addr k) (enc (st k))

@[simp] theorem size_writeVars (L : Layout) (st : St) (m : ByteArray) (k : ℕ) :
    (writeVars L st m k).size = m.size := by
  induction k with
  | zero => rfl
  | succ k ih => simp [writeVars, ih]

/-- Write cells `0` to `k - 1` of an array at `a₀`, cell `j` holding `f j`. -/
def writeArr (m : ByteArray) (a₀ : ℕ) (f : ℕ → UInt32) : ℕ → ByteArray
  | 0 => m
  | k + 1 => setVal (writeArr m a₀ f k) (a₀ + 4 * k) (f k)

/-- The value an array's cell `j` starts with: item `j` of the list. -/
def cellVal (st : St) (x j : ℕ) : UInt32 := enc ((st x).toList.getD j default)

/-- Write the arrays' cells, the arrays `l` laid out from `a`. -/
def writeArrs (st : St) : ByteArray → ℕ → List (ℕ × ℕ) → ByteArray
  | m, _, [] => m
  | m, a, (x, cap) :: rest => writeArrs st (writeArr m a (cellVal st x) cap) (a + 4 * cap) rest

@[simp] theorem size_writeArr (m : ByteArray) (a₀ : ℕ) (f : ℕ → UInt32) (k : ℕ) :
    (writeArr m a₀ f k).size = m.size := by
  induction k with
  | zero => rfl
  | succ k ih => simp [writeArr, ih]

@[simp] theorem size_writeArrs (st : St) : ∀ (m : ByteArray) (a : ℕ) (l : List (ℕ × ℕ)),
    (writeArrs st m a l).size = m.size
  | _, _, [] => rfl
  | m, a, (x, cap) :: rest => by simp [writeArrs, size_writeArrs st _ _ rest]

theorem get!_writeArr_out (m : ByteArray) (a₀ : ℕ) (f : ℕ → UInt32) (k i : ℕ)
    (h : i < a₀ ∨ a₀ + 4 * k ≤ i) : (writeArr m a₀ f k).get! i = m.get! i := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [writeArr]; rw [get!_setVal_of_lt _ _ _ _ (by omega), ih (by omega)]

theorem get!_writeArrs_out (st : St) : ∀ (m : ByteArray) (a : ℕ) (l : List (ℕ × ℕ)) (i : ℕ),
    (i < a ∨ a + 4 * cellsOf l ≤ i) → (writeArrs st m a l).get! i = m.get! i
  | _, _, [], _, _ => rfl
  | m, a, (x, cap) :: rest, i, h => by
    simp only [cellsOf, List.map_cons, List.sum_cons] at h
    simp only [writeArrs]
    rw [get!_writeArrs_out st _ _ rest i (by simp only [cellsOf] at *; omega),
      get!_writeArr_out _ _ _ _ _ (by omega)]

theorem getVal_eq_of_get! {m m' : ByteArray} {b : ℕ} (hs : m.size = m'.size)
    (h : ∀ i, b ≤ i → i < b + 4 → m.get! i = m'.get! i) : getVal m b = getVal m' b := by
  unfold getVal; rw [hs]
  split
  · rw [h b (by omega) (by omega), h (b + 1) (by omega) (by omega), h (b + 2) (by omega) (by omega),
      h (b + 3) (by omega) (by omega)]
  · rfl

theorem getVal_writeArr (m : ByteArray) (a₀ : ℕ) (f : ℕ → UInt32) (k j : ℕ) (hj : j < k)
    (hs : a₀ + 4 * k ≤ m.size) : getVal (writeArr m a₀ f k) (a₀ + 4 * j) = f j := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [writeArr]
    by_cases hjk : j = k
    · subst hjk; exact getVal_setVal_self _ _ _ (by simp; omega)
    · rw [getVal_setVal_of_disjoint _ _ _ _ (by omega)]; exact ih (by omega) (by omega)

theorem getVal_writeArrs (st : St) : ∀ (m : ByteArray) (a : ℕ) (l : List (ℕ × ℕ)) (x a₀ cap j : ℕ),
    arrFrom a l x = some (a₀, cap) → j < cap → a + 4 * cellsOf l ≤ m.size →
    getVal (writeArrs st m a l) (a₀ + 4 * j) = cellVal st x j
  | _, _, [], _, _, _, _, h, _, _ => by simp [arrFrom] at h
  | m, a, (y, c) :: rest, x, a₀, cap, j, h, hj, hs => by
    simp only [arrFrom] at h
    simp only [cellsOf, List.map_cons, List.sum_cons] at hs
    simp only [writeArrs]
    split_ifs at h with hy
    · cases h; subst hy
      rw [getVal_eq_of_get! (by simp) fun i _ hi =>
        get!_writeArrs_out st _ _ rest i (Or.inl (by omega))]
      exact getVal_writeArr _ _ _ _ _ hj (by omega)
    · exact getVal_writeArrs st _ _ rest x a₀ cap j h hj (by simp only [cellsOf] at *; simp; omega)

theorem get!_writeVars_out (L : Layout) (st : St) (m : ByteArray) (k : ℕ) (i : ℕ)
    (hi : i < L.base ∨ L.base + 4 * k ≤ i) : (writeVars L st m k).get! i = m.get! i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [writeVars]
    rw [get!_setVal_of_lt _ _ _ _ (by unfold Layout.addr; omega), ih (by omega)]

/-- A memory of zeros. -/
def zeros : ByteArray := ByteArray.mk (Array.replicate MAXBYTE 0)

theorem get!_zeros (i : ℕ) : zeros.get! i = 0 := by
  simp only [zeros, ByteArray.get!]
  by_cases h : i < MAXBYTE
  · rw [getElem!_pos _ i (by simpa using h)]; simp
  · rw [getElem!_neg _ i (by simpa using h)]; rfl

/-- **The machine, loaded**: the compiled program at `0x100`, the variables' cells
holding `st`, the pointer at the program, running. -/
def load (L : Layout) (p : Stmt) (st : St) : State :=
  let m := writeVars L st (writeArrs st (writeBytes zeros 0x100 (compile L p))
    (L.base + 4 * L.n) L.arrays) L.n
  setRST (setIP ⟨m, Array.replicate STACKSZ 0, Array.replicate STACKSZ 0, ""⟩ L.start) 1

/-- What a run leaves in the variables, as integers. -/
def readVars (L : Layout) (s : State) : List ℤ :=
  (List.range L.n).map fun x => toInt32 (getVal s.mem (L.addr x))

@[simp] theorem size_zeros : zeros.size = MAXBYTE := by simp [zeros, ByteArray.size]

theorem get!_writeVars_low (L : Layout) (st : St) (m : ByteArray) (k : ℕ) (i : ℕ)
    (hi : i < L.base) : (writeVars L st m k).get! i = m.get! i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [writeVars]
    rw [get!_setVal_of_lt _ _ _ _ (by unfold Layout.addr; omega), ih]

theorem getVal_writeVars (L : Layout) (hL : L.Ok) (st : St) (m : ByteArray) (hm : m.size = MAXBYTE) :
    ∀ k ≤ L.n, ∀ x < k, getVal (writeVars L st m k) (L.addr x) = enc (st x) := by
  intro k
  induction k with
  | zero => intro _ x hx; omega
  | succ k ih =>
    intro hk x hx
    simp only [writeVars]
    by_cases hxk : x = k
    · subst hxk
      exact getVal_setVal_self _ _ _ (by simp [hm]; unfold Layout.addr; have := hL.2; omega)
    · rw [getVal_setVal_of_disjoint _ _ _ _ (by unfold Layout.addr; omega)]
      exact ih (by omega) x (by omega)

/-- The memory of the loaded machine. -/
def loadMem (L : Layout) (p : Stmt) (st : St) : ByteArray :=
  writeVars L st (writeArrs st (writeBytes zeros 0x100 (compile L p)) (L.base + 4 * L.n) L.arrays) L.n

theorem loadMem_low (L : Layout) (p : Stmt) (st : St) (hfit : L.start + slen L p + 1 ≤ L.base)
    (hL : L.Ok) (i : ℕ) (hi : i < 256) : (loadMem L p st).get! i = 0 := by
  unfold loadMem
  rw [get!_writeVars_low _ _ _ _ _ (by have := hL.1; omega),
    get!_writeArrs_out _ _ _ _ _ (Or.inl (by have := hL.1; omega)),
    get!_writeBytes _ _ _ (by simp; unfold Layout.start at hfit; have := hL.2; omega),
    ite_eq_right (by omega), get!_zeros]

theorem getVal_of_zero (m : ByteArray) (off : ℕ) (h : ∀ i, off ≤ i → i < off + 4 → m.get! i = 0) :
    getVal m off = 0 := by
  unfold getVal
  split
  · rw [h off (by omega) (by omega), h (off + 1) (by omega) (by omega), h (off + 2) (by omega) (by omega),
      h (off + 3) (by omega) (by omega)]; decide
  · rfl

/-- **The loaded machine is ready**: it satisfies what `compile_correct` asks. -/
theorem load_ready (L : Layout) (hL : L.Ok) (p : Stmt) (st : St)
    (hfit : L.start + slen L p + 1 ≤ L.base) :
    let s := load L p st
    WF s ∧ Running s ∧ getIP s = L.start ∧ CodeAt (high s) 0x100 (compile L p) ∧
      VarsOk L (high s) st ∧ dstack s = [] ∧ cstack s = [] := by
  have hsz : (loadMem L p st).size = MAXBYTE := by simp [loadMem]
  have hlow := loadMem_low L p st hfit hL
  have hreg : ∀ off, off + 4 ≤ 256 → getVal (loadMem L p st) off = 0 :=
    fun off ho => getVal_of_zero _ _ fun i _ hi => hlow i (by omega)
  let s₀ : State := ⟨loadMem L p st, Array.replicate STACKSZ 0, Array.replicate STACKSZ 0, ""⟩
  have hdsh : getDSH s₀ = 0 := by
    simp only [getDSH, s₀]; rw [hreg _ (by unfold RDS_OFF; omega)]; rfl
  have hcsh : getCSH s₀ = 0 := by
    simp only [getCSH, s₀]; rw [hreg _ (by unfold RCS_OFF; omega)]; rfl
  have hdb : getRDB s₀ = 0 := by simp only [getRDB, s₀]; rw [hreg _ (by unfold RDB_OFF; omega)]
  have hload : load L p st = setRST (setIP s₀ L.start) 1 := rfl
  have hw : WF (load L p st) := by
    rw [hload]
    refine ⟨by simp [s₀, hsz], by simp [s₀, STACKSZ], by simp [s₀, STACKSZ], ?_, ?_⟩
    · rw [getDSH_setRST, getDSH_setIP, hdsh]; unfold STACKSZ; omega
    · rw [getCSH_setRST, getCSH_setIP, hcsh]; unfold STACKSZ; omega
  have hhigh : high (load L p st) = high s₀ := by rw [hload]; simp
  have hhs : ∀ a, 256 ≤ a → high s₀ a = (loadMem L p st).get! a := fun a ha => by
    simp [high, s₀, ha]
  refine ⟨hw, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hload, getRST_setRST _ _ (by simp [s₀, hsz])]
  · rw [hload, getRDB_setRST, getRDB_setIP, hdb]
  · rw [hload, getIP_setRST, getIP_setIP _ _ (by have := hL.2; unfold MAXBYTE at this; omega)
      (by simp [s₀, hsz])]
  · intro i hi
    rw [hhigh, hhs _ (by omega)]
    unfold loadMem
    unfold Layout.start at hfit
    rw [get!_writeVars_low _ _ _ _ _ (by simp at hi; omega),
      get!_writeArrs_out _ _ _ _ _ (Or.inl (by simp at hi; omega)),
      get!_writeBytes _ _ _ (by simp; have := hL.2; omega),
      ite_eq_left (by omega)]
    simp
  · have hw₀ : WF s₀ := ⟨by simp [s₀, hsz], by simp [s₀, STACKSZ],
      by simp [s₀, STACKSZ], by rw [hdsh]; unfold STACKSZ; omega, by rw [hcsh]; unfold STACKSZ; omega⟩
    refine ⟨fun x hx => ?_, fun x a₀ cap hx vs hvs j hj hjl => ?_⟩
    · rw [hhigh, ← getVal_high s₀ _ hw₀
        (by unfold Layout.addr; have := hL.1; omega) (by unfold Layout.addr; have := hL.2; omega)]
      exact getVal_writeVars L hL st _ (by simp) L.n le_rfl x hx
    · have hb := L.arrayAt_bounds hx
      have hL2 := hL.2
      rw [hhigh, ← getVal_high s₀ _ hw₀ (by have := hL.1; omega) (by omega)]
      simp only [s₀, loadMem]
      rw [getVal_eq_of_get! (by simp) fun i _ _ => get!_writeVars_out _ _ _ _ i (Or.inr (by omega)),
        getVal_writeArrs st _ _ _ x a₀ cap j hx hj (by simp; omega), cellVal, hvs]
      rfl
  · rw [dstack, hload, getDSH_setRST, getDSH_setIP, hdsh]; rfl
  · rw [cstack, hload, getCSH_setRST, getCSH_setIP, hcsh]; rfl

/-- **Compiled and loaded, the program computes what the language does**: if the
language takes `st` to `st'` in 32 bits, the loaded machine, run long enough,
halts with the variables holding `st'`. -/
theorem load_correct (L : Layout) (hL : L.Ok) {p : Stmt} {st st' : St} (h : SEval L 0 p st st')
    (hF : L.Fit p) :
    ∃ n, getRST (runN n (load L p st)) = 0 ∧ VarsOk L (high (runN n (load L p st))) st' := by
  obtain ⟨hw, hr, hip, hc, hv, hd, hcs⟩ := load_ready L hL p st hF.hi
  exact compile_correct L hL h hF _ hw hr hip hc hv hd hcs

/-! ### Demonstration -/

namespace Demo

/-- `i:= 0. s:= 0. while i < n do i:= i+1. s:= s+i od`, with `i`, `s`, `n`
variables `0`, `1`, `2`. -/
def sumTo : Stmt :=
  .seq (.assign 0 (.lit (.int 0))) (.seq (.assign 1 (.lit (.int 0)))
    (.loop (.bin .lt (.var 0) (.var 2))
      (.seq (.assign 0 (.bin .add (.var 0) (.lit (.int 1))))
        (.assign 1 (.bin .add (.var 1) (.var 0))))))

/-- Its cells, above its code. -/
def sumToLayout : Layout := { base := 0x400, n := 3 }

/-- `n = 10`. -/
def sumToStart : St := Function.update (fun _ => .int 0) 2 (.int 10)

/-- Its bytecode. -/
def sumToCode : List UInt8 := compile sumToLayout sumTo

-- The code is 86 bytes.
#eval sumToCode.length
-- Run on the b4 machine: `i = 10, s = 55, n = 10`.
#eval readVars sumToLayout (runN 10000 (load sumToLayout sumTo sumToStart))
-- And by b4's own `run`, the same.
#eval readVars sumToLayout (B4.run (load sumToLayout sumTo sumToStart))

/-- Factorial by recursion, with `n`, `r` variables `0`, `1`: named statement
`0` is `if 0 < n then (n:= n-1. fact. n:= n+1. r:= r×n) else r:= 1`. -/
def fact : Stmt :=
  .cond (.bin .lt (.lit (.int 0)) (.var 0))
    (.seq (.assign 0 (.bin .sub (.var 0) (.lit (.int 1))))
      (.seq (.call 0) (.seq (.assign 0 (.bin .add (.var 0) (.lit (.int 1))))
        (.assign 1 (.bin .mul (.var 1) (.var 0))))))
    (.assign 1 (.lit (.int 1)))

/-- Its layout: `fact` at `0x100`. -/
def factLayout : Layout := Layout.build 0x400 2 [(0, fact)]

-- `n = 6`, `r = 720`: the recursion went six deep on the control stack.
#eval readVars factLayout (B4.run (load factLayout (.call 0) (fun x => if x = 0 then .int 6 else .int 0)))

-- A scope, `var n:= 5· r:= n×n`: `r = 25`, and `n` keeps its value `2`.
#eval readVars factLayout (B4.run (load factLayout
  (.scope 0 (.lit (.int 5)) (.assign 1 (.bin .mul (.var 0) (.var 0))))
  (fun x => if x = 0 then .int 2 else .int 0)))

end Demo

end LaPToP.ProgramTheory.CompileB4
