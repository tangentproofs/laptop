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

/-- The machine goes from `s` to `s'`, running all the way. -/
def Steps (s s' : State) : Prop := ReflTransGen (fun a b => Running a ∧ b = step a) s s'

theorem Steps.one {s : State} (h : Running s) : Steps s (step s) := .single ⟨h, rfl⟩

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
def Layout.Ok (L : Layout) : Prop := 256 ≤ L.base ∧ L.base + 4 * L.n + 4 ≤ MAXBYTE

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
    (hb : binByte op = byte)
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
  refine ⟨step s₂, r₁.trans (r₂.trans (Steps.one h₂.run)), w₃, ?_, by rw [d₃, hval],
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

/-- **Expressions**: the code of an expression that fits pushes its value, and
changes nothing else. -/
theorem exp_runs (L : Layout) (hL : L.Ok) (st : St) : ∀ e : Exp, ERuns L st e := by
  intro e
  induction e with
  | lit v =>
    intro s _ h
    simp only [ecode] at h
    obtain ⟨w, i, d, sm⟩ := run_li (rest := []) (by rw [List.append_nil]; exact h) (by simp [depth])
    exact ⟨step s, Steps.one h.run, w, by rw [i]; simp [ecode], by rw [d]; rfl, sm⟩
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
    refine ⟨step (step s), (Steps.one h.run).tail ⟨sm₁.running h.run, rfl⟩, w₂,
      by rw [i₂, i₁]; simp, ?_, sm₁.trans sm₂⟩
    rw [d₂, toNat_ofNat_addr (by omega), sm₁.high, h.vars x hf]
    rfl
  | bin op a b iha ihb =>
    intro s hf h
    cases op <;> simp only [Fits] at hf
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, _⟩ := hf
      exact run_bin L st _ a b 0x80 (fun x y => fromInt32 (toInt32 x + toInt32 y)) runOp_ad rfl
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_add ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, _⟩ := hf
      exact run_bin L st _ a b 0x81 (fun x y => fromInt32 (toInt32 x - toInt32 y)) runOp_sb rfl
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_sub ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩, _⟩ := hf
      exact run_bin L st _ a b 0x82 (fun x y => fromInt32 (toInt32 x * toInt32 y)) runOp_ml rfl
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_mul ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩⟩ := hf
      exact run_bin L st _ a b 0x8A (fun x y => if x == y then 0xFFFFFFFF else 0) runOp_eq rfl
        (by simp only [Exp.eval]; rw [ea, eb, enc_int, enc_int]; exact enc_eq ra rb) iha ihb fa fb s h
    · obtain ⟨fa, fb, ⟨ka, ea, ra⟩, ⟨kb, eb, rb⟩⟩ := hf
      exact run_bin L st _ a b 0x8B (fun x y => if toInt32 x < toInt32 y then 0xFFFFFFFF else 0) runOp_lt rfl
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
      refine ⟨step s₂, ((Steps.one h.run).trans r₂).tail ⟨h₂.run, rfl⟩, w₃, ?_, ?_,
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
      refine ⟨step s₁, r₁.tail ⟨h₁.run, rfl⟩, w₂, by rw [i₂, i₁]; simp; omega, ?_,
        sm₁.trans sm₂⟩
      rw [d₂]; simp only [Exp.eval]; rw [eb, enc_not b]
  | nil => intro s hf; exact hf.elim
  | cons => intro s hf; exact hf.elim
  | index => intro s hf; exact hf.elim
  | cond => intro s hf; exact hf.elim

end LaPToP.ProgramTheory.CompileB4
