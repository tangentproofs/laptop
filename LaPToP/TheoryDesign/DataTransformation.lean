import LaPToP.ProgramTheory.Scope
import Mathlib.Algebra.Group.Nat.Even

/-!
# Data transformation

This module formalizes Section 7.2 (Data Transformation) of Eric Hehner's
*A Practical Theory of Programming* (aPToP): the data transformer, the
transformed specification, and the two worked examples (Exercises 454(a) and
455(a)).

## The model

"Since a theory user has no access to the implementer's variables except
through the theory, an implementer is free to change them in any way that
provides the same theory to the user. ... We can replace the old
implementer's variables by new implementer's variables using a data
transformer, which is a binary expression `D` relating `old` and `new` such
that `∀new· ∃old· D`. Let `D′` be the same as `D` but with primes on all the
variables. Then each specification `S` in the theory is transformed to
`∀old· D ⇒ ∃old′· D′ ∧ S`."

States are products of the user's variables `U` with the implementer's
variables — old `O` or new `N`. A specification of the theory is
`S : Spec (U × O)`; a transformer is `D : O → N → Prop` with
`∀ n, ∃ o, D o n`; the transformed specification `Spec.transform D S : Spec (U × N)`
is literally `∀old· D ⇒ ∃old′· D′ ∧ S`.

The book's remark "this says that whatever related initial state `old` the
user was imagining, there is a related final state `old′` for the user to
imagine as the result of `S`, and so the fiction is maintained" is the
definition unfolded. Two honest caveats are proved rather than assumed: the
transformed specification of an implementable specification need not be
implementable in general (a counterexample is given), and it is implementable
when the transformer is a bijective correspondence.
-/

namespace LaPToP.TheoryDesign

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

universe u v w

namespace Spec

variable {U : Type u} {O : Type v} {N : Type w}

/-- `∀new· ∃old· D`: every new state represents some old state. -/
def IsTransformer (D : O → N → Prop) : Prop := ∀ n, ∃ o, D o n

/-- The transformed specification `∀old· D ⇒ ∃old′· D′ ∧ S`, in the user's
variables and the new implementer's variables. -/
def transform (D : O → N → Prop) (S : Spec (U × O)) : Spec (U × N) :=
  fun s s' => ∀ o, D o s.2 → ∃ o', D o' s'.2 ∧ S (s.1, o) (s'.1, o')

variable (D : O → N → Prop)

/-- The fiction is maintained: "whatever related initial state `old` the user
was imagining, there is a related final state `old′` for the user to imagine
as the result of `S`". -/
theorem transform_spec (S : Spec (U × O)) {s s' : U × N} (h : transform D S s s') (o : O) (ho : D o s.2) :
    ∃ o', D o' s'.2 ∧ S (s.1, o) (s'.1, o') := h o ho

/-- Transformation is monotonic with respect to refinement. -/
theorem transform_mono {S S' : Spec (U × O)} (h : Refines S S') : Refines (transform D S) (transform D S') :=
  fun _s _s' hS' o ho => let ⟨o', hD, hS⟩ := hS' o ho; ⟨o', hD, h _ _ hS⟩

/-- Transformation preserves implementability when the transformer is a
bijective correspondence between old and new states: each new state
represents exactly one old state and each old state is represented. -/
theorem implementable_transform {S : Spec (U × O)} (hS : Implementable S)
    (hD : ∀ n, ∃! o, D o n) (hD' : ∀ o, ∃ n, D o n) : Implementable (transform D S) := by
  rintro ⟨u, n⟩
  obtain ⟨o, ho, huniq⟩ := hD n
  obtain ⟨⟨u', o'⟩, hS'⟩ := hS (u, o)
  obtain ⟨n', hn'⟩ := hD' o'
  refine ⟨(u', n'), fun o₁ ho₁ => ?_⟩
  rw [huniq o₁ ho₁]
  exact ⟨o', hn', hS'⟩

/-! ### Transformers that mention the user's variables

"Specification `S` talks about its nonlocal variables `old` and `old′` (and
the user's variables), and the transformed specification talks about its
nonlocal variables `new` and `new′` (and the user's variables)." A transformer
`D` may itself mention the user's variables — the security switch of
Section 7.2.0 uses `A=B=c` with `c` a user's variable — and then `D′` "with
primes on all the variables" primes the user's variables too. `transformU`
is this general form; `transform` is the special case in which `D` does not
mention the user's variables. -/

/-- `∀new· ∃old· D`, for a transformer that may mention the user's variables. -/
def IsTransformerU (D : U → O → N → Prop) : Prop := ∀ u n, ∃ o, D u o n

/-- `∀old· D ⇒ ∃old′· D′ ∧ S` where `D′` primes the user's variables as well. -/
def transformU (D : U → O → N → Prop) (S : Spec (U × O)) : Spec (U × N) :=
  fun s s' => ∀ o, D s.1 o s.2 → ∃ o', D s'.1 o' s'.2 ∧ S (s.1, o) (s'.1, o')

/-- `transform` is `transformU` with a transformer ignoring the user's variables. -/
theorem transform_eq_transformU (S : Spec (U × O)) : transform D S = transformU (fun _ => D) S := rfl

theorem isTransformer_iff_isTransformerU [Nonempty U] : IsTransformer D ↔ IsTransformerU (fun _ : U => D) :=
  ⟨fun h _ n => h n, fun h n => h (Classical.arbitrary U) n⟩

/-- Transformation with a general transformer is monotonic with respect to refinement. -/
theorem transformU_mono (D : U → O → N → Prop) {S S' : Spec (U × O)} (h : Refines S S') :
    Refines (transformU D S) (transformU D S') :=
  fun _s _s' hS' o ho => let ⟨o', hD, hS⟩ := hS' o ho; ⟨o', hD, h _ _ hS⟩

end Spec

/-! ### Exercise 454(a): replacing a natural by a binary -/

namespace Exercise454

open Spec

/-- The transformer `w = even v`: the new variable `w: bin` records whether the
old variable `v: nat` is even. -/
def D (v : ℕ) (w : Bool) : Prop := w = decide (Even v)

/-- `∀new· ∃old· D`: `w = ⊤` is represented by `v = 0`, `w = ⊥` by `v = 1`. -/
theorem isTransformer : IsTransformer D := fun w => by
  cases w
  · exact ⟨1, by simp [D, Nat.not_even_one]⟩
  · exact ⟨0, by simp [D]⟩

/-- `even (v+1) = ¬ even v`, in `Bool`. -/
theorem decide_even_succ (v : ℕ) : decide (Even (v + 1)) = !decide (Even v) := by
  by_cases h : Even v <;> simp [Nat.even_add_one, h]

/-- `zero = v:= 0` (the state consists of `u` and `v`). -/
def zero : Spec (Bool × ℕ) := fun s s' => s'.1 = s.1 ∧ s'.2 = 0

/-- `increase = v:= v+1`. -/
def increase : Spec (Bool × ℕ) := fun s s' => s'.1 = s.1 ∧ s'.2 = s.2 + 1

/-- `inquire = u:= even v`. -/
def inquire : Spec (Bool × ℕ) := fun s s' => s'.1 = decide (Even s.2) ∧ s'.2 = s.2

/-- "Operation `zero` becomes ... `w′=⊤ ∧ u′=u` = `w:= ⊤`." -/
theorem transform_zero : transform D zero = fun s s' : Bool × Bool => s'.1 = s.1 ∧ s'.2 = true := by
  refine Spec.ext fun s s' => ⟨fun h => ?_, fun ⟨hu, hw⟩ v _ => ⟨0, by simp [D, hw], hu, rfl⟩⟩
  obtain ⟨v, hv⟩ := isTransformer s.2
  obtain ⟨v', hw', hu, rfl⟩ := h v hv
  exact ⟨hu, by simpa [D] using hw'⟩

/-- "Operation `increase` becomes ... `w′ = ¬w ∧ u′=u` = `w:= ¬w`." -/
theorem transform_increase : transform D increase = fun s s' : Bool × Bool => s'.1 = s.1 ∧ s'.2 = !s.2 := by
  refine Spec.ext fun s s' => ⟨fun h => ?_, fun ⟨hu, hw⟩ v hv => ⟨v + 1, ?_, hu, rfl⟩⟩
  · obtain ⟨v, hv⟩ := isTransformer s.2
    obtain ⟨v', hw', hu, rfl⟩ := h v hv
    refine ⟨hu, ?_⟩
    simp only [D] at hv hw'
    rw [hw', hv, decide_even_succ]
  · simp only [D] at hv ⊢
    rw [hw, hv, decide_even_succ]

/-- "Operation `inquire` becomes ... `w′=w ∧ u′=w` = `u:= w`." -/
theorem transform_inquire : transform D inquire = fun s s' : Bool × Bool => s'.1 = s.2 ∧ s'.2 = s.2 := by
  refine Spec.ext fun s s' => ⟨fun h => ?_, fun ⟨hu, hw⟩ v hv => ⟨v, ?_, ?_, rfl⟩⟩
  · obtain ⟨v, hv⟩ := isTransformer s.2
    obtain ⟨v', hw', hu, rfl⟩ := h v hv
    simp only [D] at hv hw'
    exact ⟨hu.trans hv.symm, hw'.trans hv.symm⟩
  · simp only [D] at hv ⊢; rw [hw, hv]
  · simp only [D] at hv; rw [hu, hv]

end Exercise454

/-! ### Exercise 455(a): replacing a binary by a natural, "just to show that
it works both ways" -/

namespace Exercise455

open Spec

/-- The transformer `v = even w`: the old variable `v: bin` is whether the new
variable `w: nat` is even. -/
def D (v : Bool) (w : ℕ) : Prop := v = decide (Even w)

/-- `∀new· ∃old· D`. -/
theorem isTransformer : IsTransformer D := fun w => ⟨decide (Even w), rfl⟩

/-- `set = v:= ⊤`. -/
def set : Spec (Bool × Bool) := fun s s' => s'.1 = s.1 ∧ s'.2 = true

/-- `flip = v:= ¬v`. -/
def flip : Spec (Bool × Bool) := fun s s' => s'.1 = s.1 ∧ s'.2 = !s.2

/-- `ask = u:= v`. -/
def ask : Spec (Bool × Bool) := fun s s' => s'.1 = s.2 ∧ s'.2 = s.2

/-- "Operation `set` becomes `even w′ ∧ u′=u`." -/
theorem transform_set : transform D set = fun s s' : Bool × ℕ => s'.1 = s.1 ∧ Even s'.2 := by
  refine Spec.ext fun s s' => ⟨fun h => ?_, fun ⟨hu, hw⟩ v _ => ⟨true, by simp [D, hw], hu, rfl⟩⟩
  obtain ⟨v', hw', hu, rfl⟩ := h _ rfl
  exact ⟨hu, by simpa [D] using hw'.symm⟩

/-- "... `⇐ w:= 0`." -/
theorem set_refines : Refines (transform D set) fun s s' : Bool × ℕ => s'.1 = s.1 ∧ s'.2 = 0 := by
  rw [transform_set]
  rintro s s' ⟨hu, hw⟩
  exact ⟨hu, hw ▸ ⟨0, rfl⟩⟩

/-- "Operation `flip` becomes `even w′ = ¬even w ∧ u′=u`." -/
theorem transform_flip :
    transform D flip = fun s s' : Bool × ℕ => s'.1 = s.1 ∧ (Even s'.2 ↔ ¬ Even s.2) := by
  refine Spec.ext fun s s' => ⟨fun h => ?_, fun ⟨hu, hw⟩ v hv => ⟨!v, ?_, hu, rfl⟩⟩
  · obtain ⟨v', hw', hu, rfl⟩ := h _ rfl
    refine ⟨hu, ?_⟩
    simp only [D] at hw'
    have := congrArg (· = true) hw'
    simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at this
    simpa using this.symm
  · simp only [D] at hv ⊢
    rw [hv]
    by_cases h : Even s.2 <;> simp [h, hw]

/-- "... `⇐ w:= w+1`." -/
theorem flip_refines : Refines (transform D flip) fun s s' : Bool × ℕ => s'.1 = s.1 ∧ s'.2 = s.2 + 1 := by
  rw [transform_flip]
  rintro s s' ⟨hu, hw⟩
  exact ⟨hu, hw ▸ Nat.even_add_one⟩

/-- "Operation `ask` becomes `even w′ = even w = u′`." -/
theorem transform_ask :
    transform D ask = fun s s' : Bool × ℕ => s'.1 = decide (Even s.2) ∧ (Even s'.2 ↔ Even s.2) := by
  refine Spec.ext fun s s' => ⟨fun h => ?_, fun ⟨hu, hw⟩ v hv => ⟨v, ?_, ?_, rfl⟩⟩
  · obtain ⟨v', hw', hu, rfl⟩ := h _ rfl
    simp only [D] at hw'
    refine ⟨hu, ?_⟩
    have := congrArg (· = true) hw'
    simpa using this.symm
  · simp only [D] at hv ⊢
    rw [hv]
    by_cases h : Even s.2 <;> simp [h, hw]
  · simp only [D] at hv; rw [hu, hv]

/-- "... `⇐ u:= even w`." -/
theorem ask_refines :
    Refines (transform D ask) fun s s' : Bool × ℕ => s'.1 = decide (Even s.2) ∧ s'.2 = s.2 := by
  rw [transform_ask]
  rintro s s' ⟨hu, hw⟩
  exact ⟨hu, hw ▸ Iff.rfl⟩

end Exercise455

/-! ### A caveat: transformation need not preserve implementability -/

namespace Caveat

open Spec

/-- The implementable, deterministic specification
`if v = 0 then v′ = 0 else v′ = 1` (with `u` unchanged). -/
def S : Spec (Bool × ℕ) := fun s s' => s'.1 = s.1 ∧ s'.2 = if s.2 = 0 then 0 else 1

/-- `S` is implementable. -/
theorem implementable_S : Implementable S := fun s => ⟨(s.1, if s.2 = 0 then 0 else 1), rfl, rfl⟩

/-- Under the transformer `w = even v` of Exercise 454(a), the transformed
specification is not implementable: from `w = ⊤` the old state may be `v = 0`
(giving `v′ = 0`, `w′ = ⊤`) or `v = 2` (giving `v′ = 1`, `w′ = ⊥`), and no single
`w′` serves both. Totality of the transformer alone does not preserve
implementability. -/
theorem not_implementable_transform : ¬ Implementable (transform Exercise454.D S) := fun h => by
  obtain ⟨⟨u', w'⟩, hT⟩ := h (true, true)
  obtain ⟨v₀, h₀, -, hv₀⟩ := hT 0 (by simp [Exercise454.D])
  obtain ⟨v₂, h₂, -, hv₂⟩ := hT 2 (by simp [Exercise454.D])
  simp only [Exercise454.D] at h₀ h₂
  simp at hv₀ hv₂
  subst hv₀ hv₂
  simp [Nat.not_even_one] at h₀ h₂
  exact absurd (h₀.symm.trans h₂) (by decide)

end Caveat

end LaPToP.TheoryDesign
