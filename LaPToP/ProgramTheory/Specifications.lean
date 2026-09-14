import LaPToP.BasicTheories.Bunch
import Mathlib.Logic.Function.Basic

/-!
# Program Theory: specifications

This module formalizes Section 4.0 (Specifications) of Eric Hehner's
*A Practical Theory of Programming* (aPToP): specifications, the notations
`ok`, `x:= e`, `if b then S else R`, sequential composition `S. R`, refinement,
and the Specification Laws of Section 4.0.1.

## The model

"A specification is a binary expression whose variables represent quantities
of interest": the prestate `σ` and the poststate `σ′`. A *specification* over
a state space `σ` is modelled as a relation `Spec σ := σ → σ → Prop` between
prestate and poststate. It is `Prop`-valued rather than `Binary`-valued for
the same reason as `∀p` in Function Theory: state spaces are infinite, and the
book's `∀σ· ∃σ′· S` is not a computable binary value.

| aPToP                   | here                                        |
| ----------------------- | ------------------------------------------- |
| `S` (in `σ`, `σ′`)      | `S : Spec σ`, `S s s'`                      |
| `ok`                    | `Spec.ok` (`σ′ = σ`)                        |
| `x:= e`                 | `Spec.assign x e` (`σ′ = σ⊲x⊳e`)            |
| `if b then S else R`    | `Spec.cond b S R` (`b` of the prestate)     |
| `S. R`                  | `Spec.seq S R`                              |
| `S ∧ R`, `S ∨ R`, `¬S`  | `Spec.and`, `Spec.or`, `Spec.not`           |
| `P ⇐ S`                 | `Spec.Refines P S` (`∀σ, σ′· P ⇐ S`)        |
| `P = Q`                 | `P = Q` (`∀σ, σ′· P = Q`, by extensionality)|

Equality of specifications is Lean equality of relations, which by
extensionality is exactly the book's `∀σ, σ′· P = Q`; the Specification Laws
are therefore stated as equations.

For assignment, a state is a function from state variables to values,
`State Var Val := Var → Val`, so that `x:= e` is literally the book's
`σ′ = σ⊲address “x”⊳e`: the poststate is the prestate updated at `x`.
-/

namespace LaPToP.ProgramTheory

open LaPToP.BasicTheories

universe u v

/-- A *specification* over a state space `σ` (aPToP §4.0): a binary expression
in the prestate and the poststate, modelled as a relation. -/
abbrev Spec (σ : Type u) := σ → σ → Prop

namespace Spec

variable {σ : Type u}

/-- Two specifications are equal iff they agree on all prestates and
poststates: `∀σ, σ′· P = Q`. -/
theorem ext {P Q : Spec σ} (h : ∀ s s', P s s' ↔ Q s s') : P = Q :=
  funext fun s => funext fun s' => propext (h s s')

/-! ### Satisfiable, deterministic, implementable (aPToP §4.0) -/

/-- `§σ′· S`, the bunch of satisfactory poststates for prestate `s`. -/
def outputs (S : Spec σ) (s : σ) : Bunch σ := {s' | S s s'}

/-- `S` is *satisfiable* for prestate `s`: `∃σ′· S`. -/
def Satisfiable (S : Spec σ) (s : σ) : Prop := ∃ s', S s s'

/-- `S` is *unsatisfiable* for prestate `s`: `¢(§σ′· S) < 1`. -/
def Unsatisfiable (S : Spec σ) (s : σ) : Prop := ¬ Satisfiable S s

/-- `S` is *deterministic* for prestate `s`: `¢(§σ′· S) ≤ 1`. -/
def Deterministic (S : Spec σ) (s : σ) : Prop := ∀ s' s'', S s s' → S s s'' → s' = s''

/-- `S` is *nondeterministic* for prestate `s`: `¢(§σ′· S) > 1`. -/
def Nondeterministic (S : Spec σ) (s : σ) : Prop := ¬ Deterministic S s

/-- `S` is *implementable*: `∀σ· ∃σ′· S` — "there must be at least one
satisfactory output state for each input state". -/
def Implementable (S : Spec σ) : Prop := ∀ s, ∃ s', S s s'

variable (S : Spec σ) (s : σ)

/-- `¢(§σ′· S) ≥ 1` is `∃σ′· S` (the book's rewriting of satisfiable). -/
theorem satisfiable_iff : Satisfiable S s ↔ 1 ≤ Bunch.size (outputs S s) :=
  Set.one_le_encard_iff_nonempty.symm

/-- Unsatisfiable: `¢(§σ′· S) < 1`. -/
theorem unsatisfiable_iff : Unsatisfiable S s ↔ Bunch.size (outputs S s) < 1 := by
  rw [Unsatisfiable, satisfiable_iff, not_le]

/-- Deterministic: `¢(§σ′· S) ≤ 1`. -/
theorem deterministic_iff : Deterministic S s ↔ Bunch.size (outputs S s) ≤ 1 :=
  Set.encard_le_one_iff.symm

/-- Nondeterministic: `¢(§σ′· S) > 1`. -/
theorem nondeterministic_iff : Nondeterministic S s ↔ 1 < Bunch.size (outputs S s) := by
  rw [Nondeterministic, deterministic_iff, not_le]

/-- Implementable means satisfiable for every prestate. -/
theorem implementable_iff : Implementable S ↔ ∀ s, Satisfiable S s := Iff.rfl

/-! ### Specification notations (aPToP §4.0.0) -/

/-- `⊤`, "the easiest specification to implement, because all computer behavior satisfies it". -/
def top : Spec σ := fun _ _ => True

/-- `⊥`, "impossible to implement because it is not satisfied by any computer behavior". -/
def bot : Spec σ := fun _ _ => False

/-- `ok = σ′ = σ`: "the final values of all variables equal the corresponding
initial values. A computer can satisfy this specification by doing nothing." -/
def ok : Spec σ := fun s s' => s' = s

/-- `S ∧ R`, satisfied by computations satisfying both. -/
def and (S R : Spec σ) : Spec σ := fun s s' => S s s' ∧ R s s'

/-- `S ∨ R`, satisfied by computations satisfying either. -/
def or (S R : Spec σ) : Spec σ := fun s s' => S s s' ∨ R s s'

/-- `¬S`, satisfied by computations not satisfying `S`. -/
def not (S : Spec σ) : Spec σ := fun s s' => ¬ S s s'

/-- `if b then S else R`, for `b` a binary expression of the initial state:
`b∧S ∨ ¬b∧R`. -/
def cond (b : σ → Prop) (S R : Spec σ) : Spec σ := fun s s' => (b s ∧ S s s') ∨ (¬ b s ∧ R s s')

/-- `S. R = ∃σ′′· ⟨σ′· S⟩ σ′′ ∧ ⟨σ· R⟩ σ′′`, sequential composition: "a computer
that first behaves according to `S`, then behaves according to `R`, with the
final state from `S` serving as initial state for `R`". -/
def seq (S R : Spec σ) : Spec σ := fun s s' => ∃ s'', S s s'' ∧ R s'' s'

/-- `P ⇐ S`, "`P` is refined by `S`": `∀σ, σ′· P ⇐ S`. "We call `P` the
“problem” and `S` the “solution”." -/
def Refines (P S : Spec σ) : Prop := ∀ s s', S s s' → P s s'

/-- A state as an assignment of values to state variables (aPToP §4): a
function from variable names to values. -/
abbrev State (Var : Type u) (Val : Type v) := Var → Val

/-- `x:= e`, "`x` is assigned `e`": `σ′ = σ⊲address “x”⊳e`, the poststate is
the prestate with `x` replaced by the value of `e` in the prestate; `e` is any
expression of the initial values. -/
def assign {Var : Type u} {Val : Type v} [DecidableEq Var] (x : Var) (e : State Var Val → Val) :
    Spec (State Var Val) :=
  fun s s' => s' = Function.update s x (e s)

/-- `x:= e = x′=e ∧ y′=y ∧ ...`: the assigned variable gets `e`, every other
variable is unchanged. -/
theorem assign_iff {Var : Type u} {Val : Type v} [DecidableEq Var] (x : Var)
    (e : State Var Val → Val) (s s' : State Var Val) :
    assign x e s s' ↔ s' x = e s ∧ ∀ y, y ≠ x → s' y = s y := by
  simp only [assign]
  constructor
  · rintro rfl
    exact ⟨Function.update_self .., fun y hy => Function.update_of_ne hy ..⟩
  · rintro ⟨hx, hy⟩
    funext y
    by_cases h : y = x
    · subst h; simpa using hx
    · rw [Function.update_of_ne h]; exact hy y h

/-! ### Implementability of the notations (aPToP §4.0.0) -/

section Implementability

variable {S R : Spec σ}

/-- `ok` is implementable. -/
theorem implementable_ok : Implementable (ok : Spec σ) := fun s => ⟨s, rfl⟩

/-- `⊤` is implementable. -/
theorem implementable_top : Implementable (top : Spec σ) := fun s => ⟨s, trivial⟩

/-- `⊥` is not implementable (on a nonempty state space). -/
theorem not_implementable_bot [Nonempty σ] : ¬ Implementable (bot : Spec σ) :=
  fun h => let ⟨_, hf⟩ := h (Classical.arbitrary σ); hf

/-- `x:= e` is implementable. -/
theorem implementable_assign {Var : Type u} {Val : Type v} [DecidableEq Var] (x : Var)
    (e : State Var Val → Val) : Implementable (assign x e) :=
  fun s => ⟨Function.update s x (e s), rfl⟩

/-- "The `∨` and `if then else` operators have the nice property that if their
operands are implementable, so is the result": `∨`. -/
theorem implementable_or (hS : Implementable S) : Implementable (or S R) :=
  fun s => let ⟨s', h⟩ := hS s; ⟨s', Or.inl h⟩

/-- `if b then S else R` is implementable when `S` and `R` are. -/
theorem implementable_cond (b : σ → Prop) (hS : Implementable S) (hR : Implementable R) :
    Implementable (cond b S R) := fun s => by
  by_cases hb : b s
  · obtain ⟨s', h⟩ := hS s; exact ⟨s', Or.inl ⟨hb, h⟩⟩
  · obtain ⟨s', h⟩ := hR s; exact ⟨s', Or.inr ⟨hb, h⟩⟩

/-- `S. R` is implementable when `S` and `R` are. -/
theorem implementable_seq (hS : Implementable S) (hR : Implementable R) : Implementable (seq S R) :=
  fun s => let ⟨s'', h⟩ := hS s; let ⟨s', h'⟩ := hR s''; ⟨s', s'', h, h'⟩

/-- "The operators `∧` and `¬` do not have that property": `ok ∧ ¬ok` is not
implementable although `ok` is. -/
theorem not_implementable_and_not [Nonempty σ] : ¬ Implementable (and ok (not ok) : Spec σ) :=
  fun h => let ⟨_, h1, h2⟩ := h (Classical.arbitrary σ); h2 h1

end Implementability

/-! ### Specification Laws (aPToP §4.0.1) -/

section Laws

variable (P Q R S : Spec σ) (b : σ → Prop)

/-- `ok. P = P` (Identity Law). -/
theorem ok_seq : seq ok P = P := ext fun s _s' =>
  ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨s, rfl, hP⟩⟩

/-- `P. ok = P` (Identity Law). -/
theorem seq_ok : seq P ok = P := ext fun _s s' =>
  ⟨fun ⟨_, hP, h⟩ => h ▸ hP, fun hP => ⟨s', hP, rfl⟩⟩

/-- `P. (Q. R) = (P. Q). R` (Associative Law). -/
theorem seq_assoc : seq P (seq Q R) = seq (seq P Q) R := ext fun _s _s' =>
  ⟨fun ⟨t, hP, u, hQ, hR⟩ => ⟨u, ⟨t, hP, hQ⟩, hR⟩, fun ⟨u, ⟨t, hP, hQ⟩, hR⟩ => ⟨t, hP, u, hQ, hR⟩⟩

/-- `if b then P else P = P` (Idempotent Law). -/
theorem cond_self : cond b P P = P := ext fun s s' => by
  simp only [cond]; tauto

/-- `if b then P else Q = if ¬b then Q else P` (Case Reversal Law). -/
theorem cond_not : cond b P Q = cond (fun s => ¬ b s) Q P := ext fun s s' => by
  simp only [cond, not_not]; tauto

/-- `P = if b then b ⇒ P else ¬b ⇒ P` (Case Creation Law). -/
theorem case_creation : P = cond b (fun s s' => b s → P s s') (fun s s' => ¬ b s → P s s') :=
  ext fun s s' => by simp only [cond]; tauto

/-- `if b then S else R = b∧S ∨ ¬b∧R` (Case Analysis Law), the definition. -/
theorem cond_eq_or : cond b S R = or (and (fun s _ => b s) S) (and (fun s _ => ¬ b s) R) := rfl

/-- `if b then S else R = (b⇒S) ∧ (¬b⇒R)` (Case Analysis Law). -/
theorem cond_eq_and : cond b S R = fun s s' => (b s → S s s') ∧ (¬ b s → R s s') :=
  ext fun s s' => by simp only [cond]; tauto

/-- `if b then S else R` for a prestate satisfying `b` is `S`. -/
theorem cond_pos (S R : Spec σ) (b : σ → Prop) {s : σ} (hb : b s) (s' : σ) :
    cond b S R s s' = S s s' := by
  simp [cond, hb]

/-- `if b then S else R` for a prestate not satisfying `b` is `R`. -/
theorem cond_neg (S R : Spec σ) (b : σ → Prop) {s : σ} (hb : ¬ b s) (s' : σ) :
    cond b S R s s' = R s s' := by
  simp [cond, hb]

/-- `P∨Q. R∨S = (P. R) ∨ (P. S) ∨ (Q. R) ∨ (Q. S)` (Distributive Law). -/
theorem or_seq_or : seq (or P Q) (or R S) = or (or (seq P R) (seq P S)) (or (seq Q R) (seq Q S)) :=
  ext fun s s' => by
    simp only [seq, or]
    constructor
    · rintro ⟨t, hP | hQ, hR | hS⟩
      · exact Or.inl (Or.inl ⟨t, hP, hR⟩)
      · exact Or.inl (Or.inr ⟨t, hP, hS⟩)
      · exact Or.inr (Or.inl ⟨t, hQ, hR⟩)
      · exact Or.inr (Or.inr ⟨t, hQ, hS⟩)
    · rintro ((⟨t, h1, h2⟩ | ⟨t, h1, h2⟩) | (⟨t, h1, h2⟩ | ⟨t, h1, h2⟩))
      · exact ⟨t, Or.inl h1, Or.inl h2⟩
      · exact ⟨t, Or.inl h1, Or.inr h2⟩
      · exact ⟨t, Or.inr h1, Or.inl h2⟩
      · exact ⟨t, Or.inr h1, Or.inr h2⟩

/-- `if b then P else Q ∧ R = if b then P∧R else Q∧R` (Distributive Law), for
`∧` and, "replacing `∧` with any other binary operator", for any `op`. -/
theorem cond_op (op : Prop → Prop → Prop) :
    (fun s s' => op (cond b P Q s s') (R s s')) =
      cond b (fun s s' => op (P s s') (R s s')) (fun s s' => op (Q s s') (R s s')) :=
  funext fun s => funext fun s' => by
    by_cases hb : b s
    · rw [cond_pos P Q b hb, cond_pos _ _ b hb]
    · rw [cond_neg P Q b hb, cond_neg _ _ b hb]

/-- The `∧` instance of the Distributive Law, as printed in the book. -/
theorem cond_and : and (cond b P Q) R = cond b (and P R) (and Q R) := cond_op P Q R b And

/-- `if b then P else Q. R = if b then P. R else Q. R` (Distributive Law), for
`b` a binary expression of the prestate. -/
theorem cond_seq : seq (cond b P Q) R = cond b (seq P R) (seq Q R) :=
  funext fun s => funext fun s' => by
    by_cases hb : b s
    · rw [cond_pos _ _ b hb]
      exact propext ⟨fun ⟨t, h, hR⟩ => ⟨t, (cond_pos P Q b hb t) ▸ h, hR⟩,
        fun ⟨t, h, hR⟩ => ⟨t, (cond_pos P Q b hb t).symm ▸ h, hR⟩⟩
    · rw [cond_neg _ _ b hb]
      exact propext ⟨fun ⟨t, h, hR⟩ => ⟨t, (cond_neg P Q b hb t) ▸ h, hR⟩,
        fun ⟨t, h, hR⟩ => ⟨t, (cond_neg P Q b hb t).symm ▸ h, hR⟩⟩

variable {Var : Type u} {Val : Type v} [DecidableEq Var]

open Classical in
/-- `x:= if b then e else f = if b then x:= e else x:= f` (Functional-Imperative Law). -/
theorem assign_ite (x : Var) (b : State Var Val → Prop) (e f : State Var Val → Val) :
    assign x (fun s => if b s then e s else f s) = cond b (assign x e) (assign x f) :=
  funext fun s => funext fun s' => by
    by_cases hb : b s
    · rw [cond_pos _ _ b hb]; simp [assign, hb]
    · rw [cond_neg _ _ b hb]; simp [assign, hb]

/-- `x:= e. P = ⟨x· P⟩ e = (substitute e for x in P)` (Substitution Law), for
`e` an expression of the prestate: an assignment followed by any specification
is the specification evaluated at the updated prestate. -/
theorem assign_seq (x : Var) (e : State Var Val → Val) (P : Spec (State Var Val)) :
    seq (assign x e) P = fun s s' => P (Function.update s x (e s)) s' :=
  ext fun _s _s' => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

end Laws

/-! ### Refinement (aPToP §4.0.2) -/

section Refinement

variable (P Q S : Spec σ)

/-- `P ⇐ P`: refinement is reflexive. -/
theorem refines_refl : Refines P P := fun _ _ h => h

/-- Refinement is transitive: a solution's solution solves the problem. -/
theorem refines_trans (h₁ : Refines P Q) (h₂ : Refines Q S) : Refines P S :=
  fun s s' h => h₁ s s' (h₂ s s' h)

/-- "Two specifications `P` and `Q` are equal if and only if each is satisfied
whenever the other is": mutual refinement is equality. -/
theorem refines_antisymm (h₁ : Refines P Q) (h₂ : Refines Q P) : P = Q :=
  ext fun s s' => ⟨h₂ s s', h₁ s s'⟩

/-- `⊤ ⇐ S`: every specification refines `⊤`. -/
theorem top_refines : Refines top S := fun _ _ _ => trivial

/-- `S ⇐ ⊥`: `⊥` refines every specification (but is unimplementable). -/
theorem refines_bot : Refines S bot := fun _ _ h => h.elim

/-- `⊤ ⇐ ok`: doing nothing implements the always-true specification. -/
theorem top_refines_ok : Refines (top : Spec σ) ok := top_refines ok

/-- "Weaker specifications are easier to implement": a refinement of an
implementable specification by `S` makes `P` implementable too. -/
theorem implementable_of_refines (h : Refines P S) (hS : Implementable S) : Implementable P :=
  fun s => let ⟨s', hs⟩ := hS s; ⟨s', h s s' hs⟩

/-- `P ⇐ S` is `∀σ, σ′· P ⇐ S`: the book's definition, unfolded. -/
theorem refines_iff : Refines P S ↔ ∀ s s', S s s' → P s s' := Iff.rfl

end Refinement

end Spec

/-! ### The book's examples in two integer variables `x`, `y` (aPToP §4.0) -/

namespace Examples

open Spec

/-- The state variables of the book's running example. -/
inductive V
  /-- The state variable `x`. -/
  | x
  /-- The state variable `y`. -/
  | y
  deriving DecidableEq

/-- States over the two integer variables `x` and `y`. -/
abbrev St := State V ℤ

/-- `x′ = x+1 ∧ y′ = y`, "a computer that increases the value of `x` by 1 and
leaves `y` unchanged". -/
def incr : Spec St := fun s s' => s' V.x = s V.x + 1 ∧ s' V.y = s V.y

/-- `x′ = x+1 ∧ y′ = y` is implementable. -/
theorem implementable_incr : Implementable incr := fun s =>
  ⟨Function.update s V.x (s V.x + 1), by simp [incr]⟩

/-- `x′ = x+1 ∧ y′ = y` is deterministic for each prestate. -/
theorem deterministic_incr (s : St) : Deterministic incr s := by
  rintro s' s'' ⟨hx, hy⟩ ⟨hx', hy'⟩
  funext v; cases v
  · rw [hx, hx']
  · rw [hy, hy']

/-- `x′ > x`, "a computation that increases `x` by any amount". -/
def gt : Spec St := fun s s' => s' V.x > s V.x

/-- `x′ > x` is implementable. -/
theorem implementable_gt : Implementable gt := fun s =>
  ⟨Function.update s V.x (s V.x + 1), by simp [gt]⟩

/-- `x′ > x` is nondeterministic for each prestate. -/
theorem nondeterministic_gt (s : St) : Nondeterministic gt s := fun h => by
  have := h (Function.update s V.x (s V.x + 1)) (Function.update s V.x (s V.x + 2))
    (by simp [gt]) (by simp [gt])
  have := congrFun this V.x
  simp at this

/-- `x≥0 ∧ y′=0` is not implementable: "if the initial value of `x` is
negative, there is no way to satisfy the specification". -/
theorem not_implementable_nonneg_and : ¬ Implementable (fun s s' : St => s V.x ≥ 0 ∧ s' V.y = 0) :=
  fun h => by
    obtain ⟨_, hx, -⟩ := h (fun _ => -1)
    exact absurd hx (by decide)

/-- `x≥0 ⇒ y′=0`, the specifier's intended version, is implementable. -/
theorem implementable_nonneg_imp : Implementable (fun s s' : St => s V.x ≥ 0 → s' V.y = 0) :=
  fun s => ⟨Function.update s V.y 0, fun _ => by simp⟩

/-- `x:= x+y = x′=x+y ∧ y′=y`. -/
theorem assign_x_add_y (s s' : St) :
    assign V.x (fun s => s V.x + s V.y) s s' ↔ s' V.x = s V.x + s V.y ∧ s' V.y = s V.y := by
  rw [assign_iff]
  constructor
  · rintro ⟨hx, hy⟩; exact ⟨hx, hy V.y (by decide)⟩
  · rintro ⟨hx, hy⟩; refine ⟨hx, fun v hv => ?_⟩; cases v
    · exact absurd rfl hv
    · exact hy

/-- `x:= 3. y:= x+y = x′=3 ∧ y′=3+y`, the book's worked example. -/
theorem assign_three_seq :
    seq (assign V.x fun _ => 3) (assign V.y fun s => s V.x + s V.y) =
      fun s s' : St => s' V.x = 3 ∧ s' V.y = 3 + s V.y := by
  rw [assign_seq]
  refine Spec.ext fun s s' => ?_
  rw [assign_iff]
  constructor
  · rintro ⟨hy, hx⟩
    refine ⟨?_, ?_⟩
    · rw [hx V.x (by decide)]; simp
    · rw [hy]; simp
  · rintro ⟨hx, hy⟩
    refine ⟨by rw [hy]; simp, fun v hv => ?_⟩
    cases v
    · rw [hx]; simp
    · exact absurd rfl hv

/-- `x′>x ⇐ x′=x+1 ∧ y′=y`. -/
theorem refine₁ : Refines gt incr := fun _ _ ⟨hx, _⟩ => by simp only [gt, hx]; omega

/-- `x′=x+1 ∧ y′=y ⇐ x:= x+1`. -/
theorem refine₂ : Refines incr (assign V.x fun s => s V.x + 1) := fun s s' h => by
  rw [assign_iff] at h
  exact ⟨h.1, h.2 V.y (by decide)⟩

/-- `x′≤x ⇐ if x=0 then x′=x else x′<x`. -/
theorem refine₃ :
    Refines (fun s s' : St => s' V.x ≤ s V.x)
      (cond (fun s => s V.x = 0) (fun s s' => s' V.x = s V.x) (fun s s' => s' V.x < s V.x)) := by
  rintro s s' (⟨-, h⟩ | ⟨-, h⟩) <;> omega

/-- `x′>y′>x ⇐ y:= x+1. x:= y+1`. -/
theorem refine₄ :
    Refines (fun s s' : St => s' V.x > s' V.y ∧ s' V.y > s V.x)
      (seq (assign V.y fun s => s V.x + 1) (assign V.x fun s => s V.y + 1)) := by
  intro s s' h
  rw [assign_seq] at h
  rw [assign_iff] at h
  obtain ⟨hx, hy⟩ := h
  have hy' := hy V.y (by decide)
  simp at hx hy'
  omega

/-- `(x′=x ∨ x′=x+1). (x′=x ∨ x′=x+1) = x′=x ∨ x′=x+1 ∨ x′=x+2`, in one
integer variable: "if we either leave `x` alone or add 1 to it, and then again
we either leave `x` alone or add 1 to it, the net result is that we leave it
alone, or add 1 to it, or add 2 to it". -/
theorem seq_step_step :
    seq (fun x x' : ℤ => x' = x ∨ x' = x + 1) (fun x x' => x' = x ∨ x' = x + 1) =
      fun x x' => x' = x ∨ x' = x + 1 ∨ x' = x + 2 :=
  Spec.ext fun x x' => by
    constructor
    · rintro ⟨t, h1, h2⟩; omega
    · rintro (h | h | h)
      · exact ⟨x, Or.inl rfl, Or.inl h⟩
      · exact ⟨x, Or.inl rfl, Or.inr h⟩
      · exact ⟨x + 1, Or.inr rfl, Or.inr (by omega)⟩

end Examples

end LaPToP.ProgramTheory
