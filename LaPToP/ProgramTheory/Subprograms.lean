import LaPToP.ProgramTheory.ForLoop
import LaPToP.ProgramTheory.Scope
import LaPToP.ProgramTheory.Assertions

/-!
# Subprograms

This module formalizes Section 5.5 (Subprograms) of Eric Hehner's *A
Practical Theory of Programming* (aPToP): the value expression (§5.5.0), the
function (§5.5.1), and the procedure (§5.5.2).

## Value expression

"Let `P` be a specification and `e` be an expression in unprimed variables.
Then `P value e` expresses the value that would be obtained by executing `P`
and then evaluating `e`. But `P` is not executed, and all variables are
unchanged. ... The value expression axiom is `P. (P value e)=e`, except that
`(P value e)` is not subject to double-priming in sequential composition, nor
to substitution when using the Substitution Law."

`Spec.value P e s` is *a* value `e s′` for a final state `s′` of `P` from `s`,
chosen by `Classical.epsilon`. The book's axiom is meaningful only when this
value is determined — when every final state gives the same `e s′`, which is
the case for programs (deterministic specifications). That hypothesis,
`ValueDetermined P e`, is made explicit; under it `e s′ = value P e s` for
every final state `s′` (`value_axiom`), and for a deterministic total
assignment `value` is simply `e` of the new state. The book's implementation
("replace each nonlocal variable ... by a fresh local variable initialized to
the value of the nonlocal variable") is proved: `y:= (P value e)` equals a
program that runs `P` on a local copy of the state and assigns `e` of the
copy. Side effects: "`x:= (P value e)` becomes `(P. x:= e)`" is a translation
of a language with side effects into one without; the two are different
specifications (a counterexample is given), which is exactly the book's point
that "with side-effects, mathematical reasoning is not possible".

## Function and procedure

`bexp = ⟨n: int· new r: int := 1· for i:= 0;..n do r:= r×2 od. assert r: int value r⟩`
is assembled from the separately formalized parts (parameter, initialized
local variable, for-loop, value expression) and `bexp n = 2^n` is proved; the
assertion `r: int` is a type check that holds by typing and is omitted.
For procedures: `P = ⟨x: int· a′ < x < b′⟩`, `P (a+1) = a′ < a+1 < b′`,
`a′ < x < b′ ⇐ a:= x–1. b:= x+1`, the translation
`⟨p: D· B⟩ a = (new p: D := a· B)` when `B` does not assign `p`, and the two
variable-parameter examples with different results.
-/

namespace LaPToP.ProgramTheory

universe u v

namespace Spec

variable {σ : Type u} {α : Type v}

/-- `P value e`: a value `e s′` for a final state `s′` of `P` from `s`. -/
noncomputable def value [Inhabited α] (P : Spec σ) (e : σ → α) (s : σ) : α :=
  Classical.epsilon fun v => ∃ s', P s s' ∧ e s' = v

/-- `e` is determined on the outcomes of `P`: every final state from `s` gives the
same value of `e`. This is what makes `P value e` well defined. -/
def ValueDetermined (P : Spec σ) (e : σ → α) : Prop := ∀ s s' s'', P s s' → P s s'' → e s' = e s''

/-- A deterministic specification determines every expression. -/
theorem valueDetermined_of_deterministic {P : Spec σ} (h : ∀ s, Deterministic P s) (e : σ → α) :
    ValueDetermined P e :=
  fun s _ _ h₁ h₂ => congrArg e (h s _ _ h₁ h₂)

variable [Inhabited α]

/-- The value expression axiom `P. (P value e)=e`: for every final state `s′` of
`P` from `s`, `e s′ = (P value e)` evaluated in the initial state `s`. -/
theorem value_spec {P : Spec σ} {e : σ → α} (hdet : ValueDetermined P e) {s s' : σ} (h : P s s') :
    value P e s = e s' := by
  obtain ⟨s₁, h₁, hv⟩ := Classical.epsilon_spec (p := fun v => ∃ s', P s s' ∧ e s' = v) ⟨e s', s', h, rfl⟩
  unfold value
  rw [← hv]
  exact hdet s s₁ s' h₁ h

/-- The axiom as a refinement: `e′ = (P value e) ⇐ P`. -/
theorem value_axiom {P : Spec σ} {e : σ → α} (hdet : ValueDetermined P e) :
    Refines (fun s s' => e s' = value P e s) P :=
  fun _ _ h => (value_spec hdet h).symm

/-- For a total deterministic program `σ:= f σ`, `(σ:= f σ) value e = e (f σ)`. -/
theorem value_assign (f : σ → σ) (e : σ → α) (s : σ) : value (fun s s' => s' = f s) e s = e (f s) :=
  value_spec (fun _ _ _ h₁ h₂ => by rw [h₁, h₂]) rfl

/-- The implementation of `y:= (P value e)`: "replace each nonlocal variable
within `P` and `e` that is assigned within `P` by a fresh local variable
initialized to the value of the nonlocal variable. Then execute the modified
`P` and evaluate the modified `e`." Here the whole state is copied into the
local variable `c`, `P` runs on `c`, and the result is assigned by `f`. -/
theorem value_impl {P : Spec σ} {e : σ → α} (hdet : ValueDetermined P e) (himp : Implementable P)
    (f : σ → α → σ) :
    (fun s s' => s' = f s (value P e s)) =
      newVarInit (fun s => s)
        (seq (fun st st' : σ × σ => st'.1 = st.1 ∧ P st.2 st'.2) fun st st' => st' = (f st.1 (e st.2), st.2)) := by
  refine Spec.ext fun s s' => ?_
  simp only [newVarInit, seq, Prod.mk.injEq]
  constructor
  · rintro rfl
    obtain ⟨s₁, h₁⟩ := himp s
    exact ⟨s₁, (s, s₁), ⟨rfl, h₁⟩, by rw [value_spec hdet h₁], rfl⟩
  · rintro ⟨c', ⟨u₁, u₂⟩, ⟨hu₁, hP⟩, hs', -⟩
    simp only at hu₁ hP hs'
    subst hu₁
    rw [hs', value_spec hdet hP]

/-! ### The book's examples (aPToP §5.5.0), in integer variables `x`, `y` -/

namespace ValueExamples

/-- `x:= x+1` on the state `(x, y)`. -/
def xinc : Spec (ℤ × ℤ) := fun s s' => s' = (s.1 + 1, s.2)

/-- `(x:= x+1 value x) = x+1`. -/
theorem value_xinc (s : ℤ × ℤ) : value xinc (·.1) s = s.1 + 1 := value_assign _ _ s

/-- `y:= (x:= x+1 value x) = y:= x+1`: "the result is as if `x:= x+1` were
executed, then the final value of `x` is the result, except that `x:= x+1` is
not executed, and the value of variable `x` is unchanged". -/
theorem assignY_value : (fun s s' : ℤ × ℤ => s' = (s.1, value xinc (·.1) s)) = fun s s' => s' = (s.1, s.1 + 1) := by
  funext s s'
  rw [value_xinc]

/-- With side effects, `y:= (x:= x+1 value x)` "becomes" `x:= x+1. y:= x`; the two are
different specifications — the first leaves `x` unchanged, the second does not. -/
theorem side_effect_ne :
    (fun s s' : ℤ × ℤ => s' = (s.1, value xinc (·.1) s)) ≠ seq xinc fun s s' => s' = (s.1, s.1) := by
  rw [assignY_value]
  intro h
  have := congrFun (congrFun h (0, 0)) (0, 1)
  simp [seq, xinc] at this

end ValueExamples

end Spec

/-! ### Function (aPToP §5.5.1): `bexp` -/

namespace Function

open Spec BinaryExponentiation

/-- Iterating total specifications is total. -/
theorem iterSeq_implementable {σ : Type u} (P : ℕ → Spec σ) (m k : ℕ) {W : Spec σ}
    (hP : ∀ i, Implementable (P i)) (hW : Implementable W) : Implementable (iterSeq P m k W) := by
  induction k generalizing P m with
  | zero => exact hW
  | succ k ih =>
    intro s
    obtain ⟨u, hu⟩ := hP m s
    obtain ⟨s', hs'⟩ := ih (fun i => P (i + 1)) m (fun i => hP (i + 1)) u
    exact ⟨s', u, hu, hs'⟩

/-- The body of `bexp`: `new r: int := 1· for i:= 0;..n do r:= r×2 od` on the
local state `r` (the natural variable `x` of `LaPToP.ProgramTheory.BinaryExponentiation`,
here playing `r`), with the loop unrolled. -/
def bexpBody (n : ℕ) : Spec XS :=
  seq (assignX fun _ => 1) (iterSeq (fun _ => assignX fun st => 2 * st.x) 0 n ok)

/-- `bexp = ⟨n: int· new r: int := 1· for i:= 0;..n do r:= r×2 od. assert r: int value r⟩`.
The local variable `r` is initialized, so the value does not depend on the
outer state; the assertion `r: int` holds by typing and is omitted. -/
noncomputable def bexp (n : ℕ) : ℕ := value (bexpBody n) XS.x ⟨0⟩

theorem bexpBody_implementable (n : ℕ) : Implementable (bexpBody n) := by
  intro s
  obtain ⟨s', hs'⟩ := iterSeq_implementable (fun _ => assignX fun st : XS => 2 * st.x) 0 n
    (W := ok) (fun _ s => ⟨_, rfl⟩) (fun s => ⟨s, rfl⟩) ⟨1⟩
  exact ⟨s', ⟨1⟩, rfl, hs'⟩

/-- `bexp n = 2^n`. -/
theorem bexp_eq (n : ℕ) : bexp n = 2 ^ n := by
  obtain ⟨s', hs'⟩ := bexpBody_implementable n ⟨0⟩
  have hdet : ValueDetermined (bexpBody n) XS.x := fun s s₁ s₂ h₁ h₂ => by
    rw [refine_pow_unrolled n s s₁ h₁, refine_pow_unrolled n s s₂ h₂]
  rw [bexp, value_spec hdet hs']
  exact refine_pow_unrolled n _ _ hs'

end Function

/-! ### Procedure (aPToP §5.5.2) -/

namespace Procedure

open Spec

/-- The state with integer variables `a`, `b`. -/
structure AB where
  /-- The variable `a`. -/
  a : ℤ
  /-- The variable `b`. -/
  b : ℤ

/-- `P = ⟨x: int· a′ < x < b′⟩`, "a procedure with parameter `x` ... that assigns
variables `a` and `b` values that lie on opposite sides of a value to be
supplied as argument". -/
def P (x : ℤ) : Spec AB := fun _ s' => s'.a < x ∧ x < s'.b

/-- `P (a+1) = a′ < a+1 < b′`: the procedure can be used before its body is refined. -/
theorem P_apply : (fun s s' => P (s.a + 1) s s') = fun s s' : AB => s'.a < s.a + 1 ∧ s.a + 1 < s'.b := rfl

/-- `a:= x–1. b:= x+1`. -/
def body (x : ℤ) : Spec AB := fun _ s' => s' = ⟨x - 1, x + 1⟩

/-- `a′ < x < b′ ⇐ a:= x–1. b:= x+1`. -/
theorem P_refines (x : ℤ) : Refines (P x) (body x) := by
  rintro _ _ rfl
  simp only [P]
  omega

variable {σ : Type u} {D : Type v}

/-- A procedure body `B` with parameter `p`, as a specification inside the scope of
the local variable `p`, "if `B` doesn't use `p′` or `p:=`": `p` is read as a
constant and unchanged. -/
def paramAsLocal (B : D → Spec σ) : Spec (σ × D) := fun st st' => B st.2 st.1 st'.1 ∧ st'.2 = st.2

/-- `⟨p: D· B⟩ a = (new p: D := a· B)`: "a procedure and argument can be translated to
a local variable and initial value". -/
theorem procedure_eq_newVarInit (B : D → Spec σ) (a : D) : B a = newVarInit (fun _ => a) (paramAsLocal B) :=
  Spec.ext fun _ _ => ⟨fun h => ⟨a, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

/-! #### Variable parameters -/

/-- The variables `a`, `b`, `x` of the variable-parameter example. -/
inductive Var where
  /-- The nonlocal variable `a`. -/
  | a
  /-- The nonlocal variable `b`. -/
  | b
  /-- A fresh variable `x`. -/
  | x
  deriving DecidableEq

/-- `⟨new x: int· a:= 3. b:= 4. x:= 5⟩`: a variable parameter "stands for a nonlocal
variable to be supplied as argument", so the body is a function of the
variable name. -/
def body₁ (v : Var) : Spec (State Var ℤ) :=
  seq (assign .a fun _ => 3) (seq (assign .b fun _ => 4) (assign v fun _ => 5))

/-- `⟨new x: int· x:= 5. b:= 4. a:= 3⟩`. -/
def body₂ (v : Var) : Spec (State Var ℤ) :=
  seq (assign v fun _ => 5) (seq (assign .b fun _ => 4) (assign .a fun _ => 3))

/-- `⟨new x: int· a:= 3. b:= 4. x:= 5⟩ a = a:= 3. b:= 4. a:= 5 = a′=5 ∧ b′=4`. -/
theorem body₁_a : body₁ .a = fun s s' => s' .a = 5 ∧ s' .b = 4 ∧ s' .x = s .x := by
  refine Spec.ext fun s s' => ?_
  simp only [body₁, assign_seq, assign_iff]
  constructor
  · rintro ⟨h5, h⟩
    refine ⟨h5, ?_, ?_⟩
    · rw [h .b (by decide)]; simp
    · rw [h .x (by decide)]; simp
  · rintro ⟨h5, h4, hx⟩
    refine ⟨h5, fun y hy => ?_⟩
    cases y <;> simp_all

/-- `⟨new x: int· x:= 5. b:= 4. a:= 3⟩ a = a:= 5. b:= 4. a:= 3 = a′=3 ∧ b′=4`. -/
theorem body₂_a : body₂ .a = fun s s' => s' .a = 3 ∧ s' .b = 4 ∧ s' .x = s .x := by
  refine Spec.ext fun s s' => ?_
  simp only [body₂, assign_seq, assign_iff]
  constructor
  · rintro ⟨h3, h⟩
    refine ⟨h3, ?_, ?_⟩
    · rw [h .b (by decide)]; simp
    · rw [h .x (by decide)]; simp
  · rintro ⟨h3, h4, hx⟩
    refine ⟨h3, fun y hy => ?_⟩
    cases y <;> simp_all

/-- With a fresh argument `x`, the two bodies are equivalent (`a′=3 ∧ b′=4 ∧ x′=5`) ... -/
theorem body₁_x_eq_body₂_x : body₁ .x = body₂ .x := by
  refine Spec.ext fun s s' => ?_
  simp only [body₁, body₂, assign_seq, assign_iff]
  constructor
  · rintro ⟨h5, h⟩
    refine ⟨?_, fun y hy => ?_⟩
    · rw [h .a (by decide)]; simp
    · cases y <;> simp_all
  · rintro ⟨h3, h⟩
    refine ⟨?_, fun y hy => ?_⟩
    · rw [h .x (by decide)]; simp
    · cases y <;> simp_all

/-- ... "but the result is different" with the argument `a`: "variable parameters
prevent the use of specification, and they prevent any reasoning about the
procedure by itself". -/
theorem body₁_a_ne_body₂_a : body₁ .a ≠ body₂ .a := by
  rw [body₁_a, body₂_a]
  intro h
  have := congrFun (congrFun h fun _ => 0) fun v => match v with | .a => 5 | .b => 4 | .x => 0
  simp at this

end Procedure

end LaPToP.ProgramTheory
