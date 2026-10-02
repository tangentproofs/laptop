import B4.Theory
import LaPToP.ProgramTheory.InterpreterLang
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

/-- The address of variable `x`. -/
def Layout.addr (L : Layout) (x : ℕ) : ℕ := L.base + 4 * x

/-- The cells lie in high memory. -/
def Layout.Ok (L : Layout) : Prop := 256 ≤ L.base ∧ L.base + 4 * L.n + 16 ≤ MAXBYTE

/-- The cells hold the values of the state. -/
def VarsOk (L : Layout) (m : ℕ → UInt8) (st : St) : Prop := ∀ x < L.n, word m (L.addr x) = enc (st x)

/-! ### Expressions -/

/-- An integer that fits. -/
def IsInt (v : Value) : Prop := ∃ k, v = .int k ∧ InRange k

/-- A value that has a word. -/
def Rep (v : Value) : Prop := IsInt v ∨ ∃ b, v = .bool b

/-- The opcode of a binary operator the compiler handles. -/
def binByte : BinOp → UInt8
  | .add => 0x80 | .sub => 0x81 | .mul => 0x82 | .eq => 0x8A | .lt => 0x8B | _ => 0

/-- The code of an expression: it pushes the expression's value. -/
def ecode (L : Layout) : Exp → List UInt8
  | .lit v => 0x97 :: le4 (enc v)
  | .var x => (0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x93]
  | .bin op a b => ecode L a ++ ecode L b ++ [binByte op]
  | .un .neg a => (0x97 :: le4 0) ++ ecode L a ++ [0x81]
  | .un .not a => ecode L a ++ [0x89]
  | _ => []

/-- How deep the stack gets. -/
def depth : Exp → ℕ
  | .bin _ a b => max (depth a) (depth b + 1)
  | .un .neg a => depth a + 1
  | .un _ a => depth a
  | _ => 1

theorem depth_pos : ∀ e : Exp, 0 < depth e
  | .bin _ a b => by simp [depth]
  | .un .neg a => by simp [depth]
  | .un .not a => by simp only [depth]; exact depth_pos a
  | .un .len a => by simp only [depth]; exact depth_pos a
  | .lit _ | .var _ | .nil | .cons _ _ | .index _ _ | .cond _ _ _ => by simp [depth]

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
  | .bin .eq a b => Fits L st a ∧ Fits L st b ∧ IsInt (a.eval st) ∧ IsInt (b.eval st)
  | .bin .lt a b => Fits L st a ∧ Fits L st b ∧ IsInt (a.eval st) ∧ IsInt (b.eval st)
  | .un .neg a => Fits L st a ∧ IsInt (a.eval st) ∧ InRange (-(a.eval st).toInt)
  | .un .not a => Fits L st a ∧ ∃ b, a.eval st = .bool b
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
    (hr : ∀ s, runOp s byte = (let (y, s) := dpop s; let (x, s) := dpop s; dpush s (f x y)))
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
  obtain ⟨w₃, i₃, d₃, sm₃⟩ := step_binop' s₂ byte f (dstack s) (enc (a.eval st)) (enc (b.eval st))
    w₂ h₂.lo (by have := h₂.hi; simp at this; unfold MAXBYTE at this; omega) hop (by rw [d₂, d₁]; simp) hr
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
    rw [d₂, toNat_ofNat_addr (by omega), sm₁.high, h.vars x hf]
    rfl
  | bin op a b iha ihb =>
    intro s hf h
    cases op <;> simp only [Fits] at hf
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, _⟩ := hf
      exact run_bin L st _ a b 0x80 (fun x y => fromInt32 (toInt32 x + toInt32 y)) runOp_ad rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_add ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, _⟩ := hf
      exact run_bin L st _ a b 0x81 (fun x y => fromInt32 (toInt32 x - toInt32 y)) runOp_sb rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_sub ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, _⟩ := hf
      exact run_bin L st _ a b 0x82 (fun x y => fromInt32 (toInt32 x * toInt32 y)) runOp_ml rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_mul ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩⟩ := hf
      exact run_bin L st _ a b 0x8A (fun x y => if x == y then 0xFFFFFFFF else 0) runOp_eq rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_eq ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩⟩ := hf
      exact run_bin L st _ a b 0x8B (fun x y => if toInt32 x < toInt32 y then 0xFFFFFFFF else 0) runOp_lt rfl (by decide)
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_lt ra rb) iha ihb fa fb s h
  | un op a iha =>
    intro s hf h
    cases op <;> simp only [Fits] at hf
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
  | nil => intro s hf; exact hf.elim
  | cons => intro s hf; exact hf.elim
  | index => intro s hf; exact hf.elim
  | cond => intro s hf; exact hf.elim

/-! ### Statements -/

/-- The statements the compiler takes: the integer fragment of the language. -/
inductive Stmt where
  /-- `ok`. -/
  | ok
  /-- `x:= e`. -/
  | assign (x : ℕ) (e : Exp)
  /-- `P. Q`. -/
  | seq (p q : Stmt)
  /-- `if c then P else Q fi`. -/
  | cond (c : Exp) (p q : Stmt)
  /-- `while c do P od`. -/
  | loop (c : Exp) (p : Stmt)

/-- A statement as a program of the language. -/
def Stmt.toProg : Stmt → P
  | .ok => .ok
  | .assign x e => Lang.assign x e
  | .seq p q => .seq p.toProg q.toProg
  | .cond c p q => ifThen c p.toProg q.toProg
  | .loop c p => Lang.loop c p.toProg

/-- `jm a`. -/
def jmTo (a : ℕ) : List UInt8 := 0x9A :: le4 (UInt32.ofNat a)

/-- The test of `if` and `while`: complement the condition, and hop over the
`jm` that follows when it was true. -/
def test : List UInt8 := [0x89, 0x9C, 7]

/-- The length of a statement's code. -/
def slen (L : Layout) : Stmt → ℕ
  | .ok => 0
  | .assign _ e => (ecode L e).length + 6
  | .seq p q => slen L p + slen L q
  | .cond c p q => (ecode L c).length + 8 + slen L p + 5 + slen L q
  | .loop c p => (ecode L c).length + 8 + slen L p + 5

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

theorem length_scode (L : Layout) : ∀ (p : Stmt) (a : ℕ), (scode L a p).length = slen L p
  | .ok, _ => rfl
  | .assign _ _, _ => by simp [scode, slen]
  | .seq p q, a => by simp [scode, slen, length_scode L p, length_scode L q]
  | .cond c p q, a => by
    simp [scode, slen, length_scode L p, length_scode L q, test, jmTo]; omega
  | .loop c p, a => by simp [scode, slen, length_scode L p, test, jmTo]; omega

/-- How deep the stack gets in a statement. -/
def sdepth : Stmt → ℕ
  | .ok => 0
  | .assign _ e => depth e + 1
  | .seq p q => max (sdepth p) (sdepth q)
  | .cond c p q => max (depth c) (max (sdepth p) (sdepth q))
  | .loop c p => max (depth c) (sdepth p)

/-- **Execution in 32 bits**: the language's execution of a statement, in which
every expression evaluated fits (`Fits`), every assigned variable has a cell, and
every condition is a binary. -/
inductive SEval (L : Layout) : Stmt → St → St → Prop
  /-- `ok`. -/
  | ok {s : St} : SEval L .ok s s
  /-- An assignment, of a value that fits, to a variable with a cell. -/
  | assign {x : ℕ} {e : Exp} {s : St} : x < L.n → Fits L s e →
      SEval L (.assign x e) s (Function.update s x (e.eval s))
  /-- `P. Q`. -/
  | seq {p q : Stmt} {s t u : St} : SEval L p s t → SEval L q t u → SEval L (.seq p q) s u
  /-- `if` with a true condition. -/
  | condT {c : Exp} {p q : Stmt} {s t : St} : Fits L s c → c.eval s = .bool true →
      SEval L p s t → SEval L (.cond c p q) s t
  /-- `if` with a false condition. -/
  | condF {c : Exp} {p q : Stmt} {s t : St} : Fits L s c → c.eval s = .bool false →
      SEval L q s t → SEval L (.cond c p q) s t
  /-- A loop that goes round. -/
  | loopT {c : Exp} {p : Stmt} {s t u : St} : Fits L s c → c.eval s = .bool true →
      SEval L p s t → SEval L (.loop c p) t u → SEval L (.loop c p) s u
  /-- A loop that exits. -/
  | loopF {c : Exp} {p : Stmt} {s : St} : Fits L s c → c.eval s = .bool false →
      SEval L (.loop c p) s s

/-- Execution in 32 bits is execution: the language's semantics allows it. -/
theorem eval_of_sEval {L : Layout} {p : Stmt} {s t : St} (h : SEval L p s t) :
    Eval p.toProg s t := by
  induction h with
  | ok => exact .ok
  | assign => exact .assign
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | condT _ hc _ ih => exact .condTrue (by simp [Exp.test, hc]) ih
  | condF _ hc _ ih => exact .condFalse (by simp [Exp.test, hc]) ih
  | loopT _ hc _ _ ih₁ ih₂ => exact .whileTrue (by simp [Exp.test, hc]) ih₁ ih₂
  | loopF _ hc => exact .whileFalse (by simp [Exp.test, hc])

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
  low : ∀ i < L.base, high s' i = high s i
  cs : cstack s' = cstack s
  ob : s'.ob = s.ob

theorem Keeps.trans {L : Layout} {s₁ s₂ s₃ : State} (h₁ : Keeps L s₁ s₂) (h₂ : Keeps L s₂ s₃) :
    Keeps L s₁ s₃ :=
  ⟨fun i hi => (h₂.low i hi).trans (h₁.low i hi), h₂.cs.trans h₁.cs, h₂.ob.trans h₁.ob⟩

theorem _root_.B4.Same.keeps {L : Layout} {s s' : State} (h : Same s s') : Keeps L s s' :=
  ⟨fun i _ => by rw [h.high], h.cs, h.ob⟩

/-- What every statement lemma assumes of the machine: statement `p`'s code at
the pointer `a`, below the variables, which hold `st`, and an empty stack. -/
structure SAt (L : Layout) (st : St) (s : State) (a : ℕ) (p : Stmt) : Prop where
  wf : WF s
  run : Running s
  ip : getIP s = a
  lo : 256 ≤ a
  hi : a + slen L p ≤ L.base
  code : CodeAt (high s) a (scode L a p)
  vars : VarsOk L (high s) st
  stack : dstack s = []
  depth : sdepth p ≤ STACKSZ

/-- What a statement's code does. -/
def SRuns (L : Layout) (p : Stmt) (st st' : St) : Prop :=
  ∀ s a, SAt L st s a p → ∃ s', Steps s s' ∧ WF s' ∧ Running s' ∧ getIP s' = a + slen L p ∧
    dstack s' = [] ∧ VarsOk L (high s') st' ∧ Keeps L s s'

theorem varsOk_write {L : Layout} {m : ℕ → UInt8} {st : St} {x : ℕ} {v : Value}
    (h : VarsOk L m st) : VarsOk L (writeWord m (L.addr x) (enc v)) (Function.update st x v) := by
  intro y hy
  by_cases hxy : y = x
  · subst hxy; rw [Function.update_self, word_writeWord_self]
  · rw [Function.update_of_ne hxy, word_writeWord_of_disjoint _ _ _ _ (by
      unfold Layout.addr; omega)]
    exact h y hy

/-- **Assignment**: compute, push the cell's address, store. -/
theorem assign_runs (L : Layout) (hL : L.Ok) {x : ℕ} {e : Exp} {st : St} (hx : x < L.n)
    (hf : Fits L st e) : SRuns L (.assign x e) st (Function.update st x (e.eval st)) := by
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
  rw [toNat_ofNat_addr (by omega)] at hi₃
  have hr₂ : Running (step s₁) := sm₂.running (sm₁.running h.run)
  refine ⟨step (step s₁), (r₁.tail ⟨sm₁.running h.run, notIo_li h₁, rfl⟩).tail
    ⟨hr₂, notIo_of_hop (by rw [i₂]; have := h₁.lo; omega) hop, rfl⟩, w₃,
    ⟨st₃.trans hr₂.1, db₃.trans hr₂.2⟩, ?_, d₃, ?_, ?_⟩
  · rw [i₃, i₂, i₁, h.ip]; simp [slen]; omega
  · rw [hi₃, sm₂.high, sm₁.high]; exact varsOk_write h.vars
  · refine ⟨fun i hi => ?_, by rw [c₃, sm₂.cs, sm₁.cs], by rw [o₃, sm₂.ob, sm₁.ob]⟩
    rw [hi₃, sm₂.high, sm₁.high]
    unfold writeWord Layout.addr
    have : i < L.base := hi
    simp [show i ≠ L.base + 4 * x by omega, show i ≠ L.base + 4 * x + 1 by omega,
      show i ≠ L.base + 4 * x + 2 by omega, show i ≠ L.base + 4 * x + 3 by omega]

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
theorem stmt_runs (L : Layout) (hL : L.Ok) {p : Stmt} {st st' : St} (h : SEval L p st st') :
    SRuns L p st st' := by
  induction h with
  | ok =>
    intro s a h
    exact ⟨s, .refl, h.wf, h.run, by rw [h.ip]; rfl, h.stack, h.vars, ⟨fun _ _ => rfl, rfl, rfl⟩⟩
  | assign hx hf => exact assign_runs L hL hx hf
  | @seq p q s t u _ _ ih₁ ih₂ =>
    intro σ a h
    have hc := CodeAt.append.mp h.code
    rw [length_scode] at hc
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, v₁, k₁⟩ := ih₁ σ a
      ⟨h.wf, h.run, h.ip, h.lo, by omega, hc.1, h.vars, h.stack, by omega⟩
    obtain ⟨σ₂, r₂, w₂, run₂, i₂, d₂, v₂, k₂⟩ := ih₂ σ₁ (a + slen L p)
      ⟨w₁, run₁, i₁, by omega, by omega,
        hc.2.mono k₁.low (by rw [length_scode]; omega), v₁, d₁, by omega⟩
    exact ⟨σ₂, r₁.trans r₂, w₂, run₂, by rw [i₂]; simp [slen]; omega, d₂, v₂, k₁.trans k₂⟩
  | @condT c p q s t hf hc _ ih =>
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
        by rw [sm₁.high]; exact h.vars, d₁, by omega⟩
    have hJ₂ : CodeAt (high σ₂) (getIP σ₂) (jmTo (a + (ecode L c).length + 8 + slen L p + 5 + slen L q)) := by
      rw [i₂]; exact (hJ'.mono (fun i hi => by rw [k₂.low i hi, sm₁.high]) (by simp; omega))
    obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_jm' hL w₂ (by rw [i₂]; omega) (by rw [i₂]; omega) hJ₂
      (by omega) (by omega)
    refine ⟨step σ₂, (r₁.trans r₂).tail ⟨run₂, notIo_jm (by rw [i₂]; omega) hJ₂, rfl⟩, w₃, sm₃.running run₂, by rw [i₃]; simp [slen]; omega,
      by rw [d₃, d₂], by rw [sm₃.high]; exact v₂, sm₁.keeps.trans (k₂.trans sm₃.keeps)⟩
  | @condF c p q s t hf hc _ ih =>
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
        by rw [sm₂.high, sm₁.high]; exact h.vars, by rw [d₂, d₁], by omega⟩
    refine ⟨σ₃, (r₁.tail ⟨run₁, notIo_jm (by rw [i₁]; omega) hJ₁, rfl⟩).trans r₃, w₃, run₃, by rw [i₃]; simp [slen]; omega,
      d₃, v₃, sm₁.keeps.trans (sm₂.keeps.trans k₃)⟩
  | @loopT c p s t u hf hc _ _ ih₁ ih₂ =>
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
        by rw [sm₁.high]; exact h.vars, d₁, by omega⟩
    have hJ₂ : CodeAt (high σ₂) (getIP σ₂) (jmTo a) := by
      rw [i₂]; exact (hJ'.mono (fun i hi => by rw [k₂.low i hi, sm₁.high]) (by simp; omega))
    obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_jm' hL w₂ (by rw [i₂]; omega) (by rw [i₂]; omega) hJ₂
      (by omega) (by omega)
    have k₃ : Keeps L σ (step σ₂) := sm₁.keeps.trans (k₂.trans sm₃.keeps)
    obtain ⟨σ₄, r₄, w₄, run₄, i₄, d₄, v₄, k₄⟩ := ih₂ (step σ₂) a
      ⟨w₃, sm₃.running run₂, i₃, hlo, h.hi, h.code.mono (fun i hi => k₃.low i hi)
        (by rw [length_scode]; exact h.hi), by rw [sm₃.high]; exact v₂, by rw [d₃, d₂], h.depth⟩
    exact ⟨σ₄, ((r₁.trans r₂).tail ⟨run₂, notIo_jm (by rw [i₂]; omega) hJ₂, rfl⟩).trans r₄, w₄, run₄, i₄, d₄, v₄, k₃.trans k₄⟩
  | @loopF c p s hf hc =>
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

/-- The program: a statement's code at `0x100`, the start of code, then `hl`. -/
def compile (L : Layout) (p : Stmt) : List UInt8 := scode L 0x100 p ++ [0xFF]

/-- **The compiler is correct.** Load the compiled program at `0x100` with the
variables, in their cells above it, holding `st`, and start the machine there: if
the language takes `st` to `st'` without leaving 32 bits (`SEval`, which is an
execution of the language: `eval_of_sEval`), the machine halts with the
variables holding `st'`. -/
theorem compile_correct (L : Layout) (hL : L.Ok) {p : Stmt} {st st' : St} (h : SEval L p st st')
    (s : State) (hw : WF s) (hr : Running s) (hip : getIP s = 0x100)
    (hfit : 0x100 + slen L p + 1 ≤ L.base) (hc : CodeAt (high s) 0x100 (compile L p))
    (hv : VarsOk L (high s) st) (hd : dstack s = []) (hdep : sdepth p ≤ STACKSZ) :
    ∃ n, getRST (runN n s) = 0 ∧ VarsOk L (high (runN n s)) st' := by
  have hc' := CodeAt.append.mp hc
  obtain ⟨s', r', w', run', i', d', v', k'⟩ := stmt_runs L hL h s 0x100
    ⟨hw, hr, hip, le_rfl, by omega, hc'.1, hv, hd, hdep⟩
  rw [length_scode] at hc'
  have hop : high s' (getIP s') = 0xFF := by
    rw [i', k'.low _ (by omega)]; simpa using hc'.2 0 (by simp)
  have hst : getRST (step s') = 0 := step_hl s' w' (by rw [i']; omega) hop
  have hhigh : high (step s') = high s' := by
    rw [step_of s' _ (by rw [i']; omega) hop, runOp_hl]; simp
  obtain ⟨n, hn⟩ := runN_of_steps (r'.tail ⟨run', notIo_of_hop (by rw [i']; omega) hop, rfl⟩)
  exact ⟨n, by rw [hn]; exact hst, by rw [hn, hhigh]; exact v'⟩

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
  let m := writeVars L st (writeBytes zeros 0x100 (compile L p)) L.n
  setRST (setIP ⟨m, Array.replicate STACKSZ 0, Array.replicate STACKSZ 0, ""⟩ 0x100) 1

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
  writeVars L st (writeBytes zeros 0x100 (compile L p)) L.n

theorem loadMem_low (L : Layout) (p : Stmt) (st : St) (hfit : 0x100 + slen L p + 1 ≤ L.base)
    (hL : L.Ok) (i : ℕ) (hi : i < 256) : (loadMem L p st).get! i = 0 := by
  unfold loadMem
  rw [get!_writeVars_low _ _ _ _ _ (by have := hL.1; omega),
    get!_writeBytes _ _ _ (by simp [compile, length_scode]; have := hL.2; omega),
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
    (hfit : 0x100 + slen L p + 1 ≤ L.base) :
    let s := load L p st
    WF s ∧ Running s ∧ getIP s = 0x100 ∧ CodeAt (high s) 0x100 (compile L p) ∧
      VarsOk L (high s) st ∧ dstack s = [] := by
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
  have hload : load L p st = setRST (setIP s₀ 0x100) 1 := rfl
  have hw : WF (load L p st) := by
    rw [hload]
    refine ⟨by simp [s₀, hsz], by simp [s₀, STACKSZ], by simp [s₀, STACKSZ], ?_, ?_⟩
    · rw [getDSH_setRST, getDSH_setIP, hdsh]; unfold STACKSZ; omega
    · rw [getCSH_setRST, getCSH_setIP, hcsh]; unfold STACKSZ; omega
  have hhigh : high (load L p st) = high s₀ := by rw [hload]; simp
  have hhs : ∀ a, 256 ≤ a → high s₀ a = (loadMem L p st).get! a := fun a ha => by
    simp [high, s₀, ha]
  refine ⟨hw, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hload, getRST_setRST _ _ (by simp [s₀, hsz])]
  · rw [hload, getRDB_setRST, getRDB_setIP, hdb]
  · rw [hload, getIP_setRST, getIP_setIP _ _ (by decide) (by simp [s₀, hsz])]
  · intro i hi
    rw [hhigh, hhs _ (by omega)]
    unfold loadMem
    rw [get!_writeVars_low _ _ _ _ _ (by simp [compile, length_scode] at hi; omega),
      get!_writeBytes _ _ _ (by simp [compile, length_scode]; have := hL.2; omega),
      ite_eq_left (by omega)]
    simp
  · intro x hx
    rw [hhigh, ← getVal_high s₀ _ (by rw [hload] at hw; exact ⟨by simp [s₀, hsz], by simp [s₀, STACKSZ],
      by simp [s₀, STACKSZ], by rw [hdsh]; unfold STACKSZ; omega, by rw [hcsh]; unfold STACKSZ; omega⟩)
      (by unfold Layout.addr; have := hL.1; omega) (by unfold Layout.addr; have := hL.2; omega)]
    exact getVal_writeVars L hL st _ (by simp) L.n le_rfl x hx
  · rw [dstack, hload, getDSH_setRST, getDSH_setIP, hdsh]; rfl

/-- **Compiled and loaded, the program computes what the language does**: if the
language takes `st` to `st'` in 32 bits, the loaded machine, run long enough,
halts with the variables holding `st'`. -/
theorem load_correct (L : Layout) (hL : L.Ok) {p : Stmt} {st st' : St} (h : SEval L p st st')
    (hfit : 0x100 + slen L p + 1 ≤ L.base) (hdep : sdepth p ≤ STACKSZ) :
    ∃ n, getRST (runN n (load L p st)) = 0 ∧ VarsOk L (high (runN n (load L p st))) st' := by
  obtain ⟨hw, hr, hip, hc, hv, hd⟩ := load_ready L hL p st hfit
  exact compile_correct L hL h _ hw hr hip hfit hc hv hd hdep

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
def sumToLayout : Layout := ⟨0x400, 3⟩

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

end Demo

end LaPToP.ProgramTheory.CompileB4
