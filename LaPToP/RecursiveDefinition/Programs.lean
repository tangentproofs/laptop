import LaPToP.ProgramTheory.WhileLoop
import LaPToP.RecursiveDefinition.Nat
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Recursive program definition

This module formalizes Section 6.1 (Recursive Program Definition), Section
6.1.0 (Recursive Program Construction) and Section 6.1.1 (Loop Definition) of
Eric Hehner's *A Practical Theory of Programming* (aPToP).

## The model

"Programs, and more generally, specifications, can be defined by axioms just as
data can. ... The name `zap` is introduced, and the fixed-point equation
`zap = if x=0 then y:= 0 else x:= x–1. t:= t+1. zap` is given as an axiom. The
right side of the equation is the constructor."

The state has a time variable and two integer variables `x`, `y`. Solutions
(e) and (f) of the equation contain `t′ = t + x` for negative `x`, so the time
domain must allow adding a negative integer to a time: we take the time
variable in `WithTop ℤ` (the extended integers without `–∞`, with `∞ = ⊤`),
in which `t + x` is a total operation and `∞ + x = ∞`. This is the honest
reading of the book's arithmetic; nondecreasing time `t ≤ t′` is then a
separate condition (`Implementable` with time), and the book's remark that
(e) and (f) are "unimplementable" is proved in that sense.

`zapC` is the constructor `Z ↦ if x=0 then y:= 0 else x:= x–1. t:= t+1. Z`
on specifications. The six solutions (a)–(f) are each shown to be fixed
points; their refinement order (the book's picture) is proved, including the
non-comparabilities; (a)–(d) are implementable with nondecreasing time, (e)
and (f) are not; (d) is deterministic. Fixed-point induction is proved as a
theorem about *every* solution — indeed about every pre-fixed point
`constructor Z ⇐ Z` — so (a) is the weakest fixed point, exactly as the book
says ("it refines the weakest solution ... and it is refined by its
constructor").

Section 6.1.0 constructs `zap₀ = ⊤`, `zapₙ₊₁ = constructor zapₙ` and the
closed form `zapₙ = 0≤x<n ⇒ x′=y′=0 ∧ t′=t+x`, "proved using nat induction";
(a) is the intersection of the `zapₙ`, the book's `zap∞`.

Section 6.1.1 gives the while-loop three axioms — `t′≥t ⇐ while b do P od`,
`if b then P. t:= t+1. while b do P od else ok ⇐ while b do P od`, and
induction — "closely analogous to the axioms that define nat". They are a
structure `WhileAxioms`; the fixed-point theorems are derived, the axioms are
shown consistent (a specification satisfying them exists — the union of all
pre-fixed points), and the book's contrast with Section 5.2 is proved: from
the least-fixed-point axioms one *cannot* derive `x′≥x ⇐ while b do x′≥x od`,
which is a theorem in the refinement-notation reading `Spec.WhileRefines`.
-/

namespace LaPToP.RecursiveDefinition

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

/-- A state with a time variable in the extended integers (`∞ = ⊤`) and
integer variables `x`, `y`. -/
@[ext]
structure ZS where
  /-- The time variable. -/
  t : WithTop ℤ
  /-- The variable `x`. -/
  x : ℤ
  /-- The variable `y`. -/
  y : ℤ

namespace Zap

/-- `x:= e`. -/
def assignX (e : ZS → ℤ) : Spec ZS := fun s s' => s' = { s with x := e s }

/-- `y:= e`. -/
def assignY (e : ZS → ℤ) : Spec ZS := fun s s' => s' = { s with y := e s }

/-- `t:= t+1`. -/
def tick : Spec ZS := fun s s' => s' = { s with t := s.t + 1 }

/-- Substitution Law for `x:= e`. -/
theorem assignX_seq (e : ZS → ℤ) (P : Spec ZS) : seq (assignX e) P = fun s s' => P { s with x := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- Substitution Law for `t:= t+1`. -/
theorem tick_seq (P : Spec ZS) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- Time does not decrease: `t′ ≥ t`. -/
def timeNondecreasing : Spec ZS := fun s s' => s.t ≤ s'.t

/-- Implementable with nondecreasing time: `∀σ· ∃σ′· S ∧ t′≥t`. -/
def ImplementableT (S : Spec ZS) : Prop := ∀ s, ∃ s', S s s' ∧ s.t ≤ s'.t

/-! ### The constructor and its solutions (aPToP §6.1) -/

/-- The constructor `Z ↦ if x=0 then y:= 0 else x:= x–1. t:= t+1. Z`. -/
def zapC (Z : Spec ZS) : Spec ZS :=
  cond (fun s => s.x = 0) (assignY fun _ => 0) (seq (assignX fun s => s.x - 1) (seq tick Z))

/-- The state after `x:= x–1. t:= t+1`. -/
def step (s : ZS) : ZS := ⟨s.t + 1, s.x - 1, s.y⟩

@[simp] theorem step_t (s : ZS) : (step s).t = s.t + 1 := rfl
@[simp] theorem step_x (s : ZS) : (step s).x = s.x - 1 := rfl
@[simp] theorem step_y (s : ZS) : (step s).y = s.y := rfl

/-- Unfolding the constructor. -/
theorem zapC_apply (Z : Spec ZS) (s s' : ZS) :
    zapC Z s s' ↔ (s.x = 0 ∧ s' = { s with y := 0 }) ∨ (s.x ≠ 0 ∧ Z (step s) s') := by
  simp only [zapC, Spec.cond, assignX_seq, tick_seq, assignY]
  rfl

/-- `x′ = y′ = 0`. -/
def XY (s' : ZS) : Prop := s'.x = 0 ∧ s'.y = 0

/-- `t′ = t + x`. -/
def T (s s' : ZS) : Prop := s'.t = s.t + (s.x : WithTop ℤ)

/-- `t′ = t + x` is unaffected by one step `x:= x–1. t:= t+1`. -/
theorem T_step (s s' : ZS) : T (step s) s' ↔ T s s' := by
  simp only [T, step]
  rw [add_assoc]
  congr! 3
  norm_cast; omega

/-- (a) `x≥0 ⇒ x′=y′=0 ∧ t′=t+x`, the weakest solution. -/
def solA : Spec ZS := fun s s' => 0 ≤ s.x → XY s' ∧ T s s'

/-- (b) `if x≥0 then x′=y′=0 ∧ t′=t+x else t′=∞`. -/
def solB : Spec ZS := cond (fun s => 0 ≤ s.x) (fun s s' => XY s' ∧ T s s') fun _ s' => s'.t = ⊤

/-- (c) `x′=y′=0 ∧ (x≥0 ⇒ t′=t+x)`. -/
def solC : Spec ZS := fun s s' => XY s' ∧ (0 ≤ s.x → T s s')

/-- (d) `x′=y′=0 ∧ if x≥0 then t′=t+x else t′=∞`, "a strongest implementable solution". -/
def solD : Spec ZS := and (fun _ s' => XY s') (cond (fun s => 0 ≤ s.x) T fun _ s' => s'.t = ⊤)

/-- (e) `x′=y′=0 ∧ t′=t+x`. -/
def solE : Spec ZS := fun s s' => XY s' ∧ T s s'

/-- (f) `x≥0 ∧ x′=y′=0 ∧ t′=t+x`, the strongest solution. -/
def solF : Spec ZS := fun s s' => 0 ≤ s.x ∧ XY s' ∧ T s s'

/-- The base case `x = 0`: `y:= 0` gives `x′=y′=0 ∧ t′=t+x`. -/
theorem base_iff {s s' : ZS} (hx : s.x = 0) : s' = { s with y := 0 } ↔ XY s' ∧ T s s' := by
  constructor
  · rintro rfl; exact ⟨⟨hx, rfl⟩, by simp [T, hx]⟩
  · rintro ⟨⟨hx', hy'⟩, ht⟩
    ext
    · simpa [T, hx] using ht
    · exact hx'.trans hx.symm
    · exact hy'

/-- (a) is a fixed point of the constructor. -/
theorem zapC_solA : zapC solA = solA := Spec.ext fun s s' => by
  rw [zapC_apply]
  by_cases hx : s.x = 0
  · rw [base_iff hx]
    simp only [hx, ne_eq, not_true_eq_false, false_and, or_false, true_and, solA, le_refl, true_implies]
  · simp only [hx, false_and, false_or, ne_eq, not_false_eq_true, true_and, solA, step_x, T_step]
    exact ⟨fun h h0 => h (by omega), fun h h0 => h (by omega)⟩

/-- (b) is a fixed point of the constructor. -/
theorem zapC_solB : zapC solB = solB := Spec.ext fun s s' => by
  rw [zapC_apply]
  by_cases hx : s.x = 0
  · rw [base_iff hx]
    simp only [hx, ne_eq, not_true_eq_false, false_and, or_false, true_and, solB, Spec.cond, le_refl,
      not_true_eq_false]
  · simp only [hx, false_and, false_or, ne_eq, not_false_eq_true, true_and, solB, Spec.cond, step_x, T_step]
    constructor
    · rintro (⟨h0, h⟩ | ⟨h0, h⟩)
      · exact Or.inl ⟨by omega, h⟩
      · exact Or.inr ⟨by omega, h⟩
    · rintro (⟨h0, h⟩ | ⟨h0, h⟩)
      · exact Or.inl ⟨by omega, h⟩
      · exact Or.inr ⟨by omega, h⟩

/-- (c) is a fixed point of the constructor. -/
theorem zapC_solC : zapC solC = solC := Spec.ext fun s s' => by
  rw [zapC_apply]
  by_cases hx : s.x = 0
  · rw [base_iff hx]
    simp only [hx, ne_eq, not_true_eq_false, false_and, or_false, true_and, solC, le_refl, true_implies]
  · simp only [hx, false_and, false_or, ne_eq, not_false_eq_true, true_and, solC, step_x, T_step]
    exact ⟨fun ⟨hxy, h⟩ => ⟨hxy, fun h0 => h (by omega)⟩, fun ⟨hxy, h⟩ => ⟨hxy, fun h0 => h (by omega)⟩⟩

/-- (d) is a fixed point of the constructor. -/
theorem zapC_solD : zapC solD = solD := Spec.ext fun s s' => by
  rw [zapC_apply]
  by_cases hx : s.x = 0
  · rw [base_iff hx]
    simp only [hx, ne_eq, not_true_eq_false, false_and, or_false, true_and, solD, Spec.and, Spec.cond, le_refl,
      not_true_eq_false]
  · simp only [hx, false_and, false_or, ne_eq, not_false_eq_true, true_and, solD, Spec.and, Spec.cond, step_x,
      T_step]
    constructor
    · rintro ⟨hxy, ⟨h0, h⟩ | ⟨h0, h⟩⟩
      · exact ⟨hxy, Or.inl ⟨by omega, h⟩⟩
      · exact ⟨hxy, Or.inr ⟨by omega, h⟩⟩
    · rintro ⟨hxy, ⟨h0, h⟩ | ⟨h0, h⟩⟩
      · exact ⟨hxy, Or.inl ⟨by omega, h⟩⟩
      · exact ⟨hxy, Or.inr ⟨by omega, h⟩⟩

/-- (e) is a fixed point of the constructor. -/
theorem zapC_solE : zapC solE = solE := Spec.ext fun s s' => by
  rw [zapC_apply]
  by_cases hx : s.x = 0
  · rw [base_iff hx]
    simp only [hx, ne_eq, not_true_eq_false, false_and, or_false, true_and, solE]
  · simp only [hx, false_and, false_or, ne_eq, not_false_eq_true, true_and, solE, T_step]

/-- (f) is a fixed point of the constructor. -/
theorem zapC_solF : zapC solF = solF := Spec.ext fun s s' => by
  rw [zapC_apply]
  by_cases hx : s.x = 0
  · rw [base_iff hx]
    simp only [hx, ne_eq, not_true_eq_false, false_and, or_false, true_and, solF, le_refl]
  · simp only [hx, false_and, false_or, ne_eq, not_false_eq_true, true_and, solF, step_x, T_step]
    exact ⟨fun ⟨h0, h⟩ => ⟨by omega, h⟩, fun ⟨h0, h⟩ => ⟨by omega, h⟩⟩

/-! #### The refinement order among the solutions -/

/-- (a) ⇐ (b). -/
theorem solA_refines_solB : Refines solA solB := by
  rintro s s' (⟨h0, h⟩ | ⟨h0, -⟩) hx
  · exact h
  · exact absurd hx h0

/-- (a) ⇐ (c). -/
theorem solA_refines_solC : Refines solA solC := fun _ _ ⟨hxy, h⟩ hx => ⟨hxy, h hx⟩

/-- (b) ⇐ (d). -/
theorem solB_refines_solD : Refines solB solD := by
  rintro s s' ⟨hxy, ⟨h0, h⟩ | ⟨h0, h⟩⟩
  · exact Or.inl ⟨h0, hxy, h⟩
  · exact Or.inr ⟨h0, h⟩

/-- (c) ⇐ (d). -/
theorem solC_refines_solD : Refines solC solD := by
  rintro s s' ⟨hxy, ⟨h0, h⟩ | ⟨h0, h⟩⟩
  · exact ⟨hxy, fun _ => h⟩
  · exact ⟨hxy, fun hx => absurd hx h0⟩

/-- (c) ⇐ (e). -/
theorem solC_refines_solE : Refines solC solE := fun _ _ ⟨hxy, h⟩ => ⟨hxy, fun _ => h⟩

/-- (d) ⇐ (f). -/
theorem solD_refines_solF : Refines solD solF := fun _ _ ⟨h0, hxy, h⟩ => ⟨hxy, Or.inl ⟨h0, h⟩⟩

/-- (e) ⇐ (f). -/
theorem solE_refines_solF : Refines solE solF := fun _ _ ⟨_, hxy, h⟩ => ⟨hxy, h⟩

/-- (b) and (c) are not comparable: (b) is not refined by (c) ... -/
theorem not_solB_refines_solC : ¬ Refines solB solC := fun h => by
  have := h ⟨0, -1, 0⟩ ⟨0, 0, 0⟩ ⟨⟨rfl, rfl⟩, fun h0 => absurd h0 (by decide)⟩
  rcases this with ⟨h0, -⟩ | ⟨-, ht⟩
  · exact absurd h0 (by decide)
  · exact absurd ht (by decide)

/-- ... and (c) is not refined by (b): "the solutions are not totally ordered". -/
theorem not_solC_refines_solB : ¬ Refines solC solB := fun h => by
  have := h ⟨0, -1, 0⟩ ⟨⊤, 5, 5⟩ (Or.inr ⟨by decide, rfl⟩)
  exact absurd this.1.1 (by decide)

/-- (d) and (e) are not comparable either: (d) is not refined by (e) ... -/
theorem not_solD_refines_solE : ¬ Refines solD solE := fun h => by
  have := h ⟨0, -1, 0⟩ ⟨-1, 0, 0⟩ ⟨⟨rfl, rfl⟩, by simp [T]⟩
  rcases this.2 with ⟨h0, -⟩ | ⟨-, ht⟩
  · exact absurd h0 (by decide)
  · exact absurd ht (by decide)

/-- ... and (e) is not refined by (d). -/
theorem not_solE_refines_solD : ¬ Refines solE solD := fun h => by
  have := h ⟨0, -1, 0⟩ ⟨⊤, 0, 0⟩ ⟨⟨rfl, rfl⟩, Or.inr ⟨by decide, rfl⟩⟩
  have h2 := this.2
  simp only [T] at h2
  rw [zero_add] at h2
  exact WithTop.top_ne_coe h2

/-! #### Implementability and determinism -/

/-- (a) is implementable with nondecreasing time. -/
theorem implementableT_solA : ImplementableT solA := fun s => by
  by_cases hx : 0 ≤ s.x
  · exact ⟨⟨s.t + s.x, 0, 0⟩, fun _ => ⟨⟨rfl, rfl⟩, rfl⟩, le_add_of_nonneg_right (by exact_mod_cast hx)⟩
  · exact ⟨s, fun h => absurd h hx, le_rfl⟩

/-- (b) is implementable with nondecreasing time. -/
theorem implementableT_solB : ImplementableT solB := fun s => by
  by_cases hx : 0 ≤ s.x
  · exact ⟨⟨s.t + s.x, 0, 0⟩, Or.inl ⟨hx, ⟨rfl, rfl⟩, rfl⟩, le_add_of_nonneg_right (by exact_mod_cast hx)⟩
  · exact ⟨⟨⊤, s.x, s.y⟩, Or.inr ⟨hx, rfl⟩, le_top⟩

/-- (c) is implementable with nondecreasing time. -/
theorem implementableT_solC : ImplementableT solC := fun s => by
  by_cases hx : 0 ≤ s.x
  · exact ⟨⟨s.t + s.x, 0, 0⟩, ⟨⟨rfl, rfl⟩, fun _ => rfl⟩, le_add_of_nonneg_right (by exact_mod_cast hx)⟩
  · exact ⟨⟨⊤, 0, 0⟩, ⟨⟨rfl, rfl⟩, fun h => absurd h hx⟩, le_top⟩

/-- (d) is implementable with nondecreasing time. -/
theorem implementableT_solD : ImplementableT solD := fun s => by
  by_cases hx : 0 ≤ s.x
  · exact ⟨⟨s.t + s.x, 0, 0⟩, ⟨⟨rfl, rfl⟩, Or.inl ⟨hx, rfl⟩⟩, le_add_of_nonneg_right (by exact_mod_cast hx)⟩
  · exact ⟨⟨⊤, 0, 0⟩, ⟨⟨rfl, rfl⟩, Or.inr ⟨hx, rfl⟩⟩, le_top⟩

/-- (e) is not implementable with nondecreasing time: for `x < 0` it requires
`t′ = t + x < t`. -/
theorem not_implementableT_solE : ¬ ImplementableT solE := fun h => by
  obtain ⟨s', ⟨-, ht⟩, hle⟩ := h ⟨0, -1, 0⟩
  simp only [T] at ht
  rw [ht] at hle
  exact absurd hle (by decide)

/-- (f) is not even implementable: for `x < 0` it has no satisfactory poststate. -/
theorem not_implementable_solF : ¬ Implementable solF := fun h => by
  obtain ⟨_, h0, -⟩ := h ⟨0, -1, 0⟩
  exact absurd h0 (by decide)

/-- (d) is deterministic for each prestate. -/
theorem deterministic_solD (s : ZS) : Deterministic solD s := by
  rintro s' s'' ⟨⟨hx', hy'⟩, h'⟩ ⟨⟨hx'', hy''⟩, h''⟩
  ext
  · rcases h' with ⟨h0, ht'⟩ | ⟨h0, ht'⟩ <;> rcases h'' with ⟨h0', ht''⟩ | ⟨h0', ht''⟩
    · exact ht'.trans ht''.symm
    · exact absurd h0 h0'
    · exact absurd h0' h0
    · exact ht'.trans ht''.symm
  · exact hx'.trans hx''.symm
  · exact hy'.trans hy''.symm

/-! #### Fixed-point induction: (a) is the weakest solution -/

/-- Every pre-fixed point of the constructor (`constructor Z ⇐ Z`) refines (a):
the book's induction axiom `∀σ,σ′· (constructor Z ⇐ Z) ⇒ ∀σ,σ′· zap ⇐ Z`
holds with `zap := (a)`. -/
theorem solA_refines_of_prefixed {Z : Spec ZS} (h : Refines (zapC Z) Z) : Refines solA Z := by
  suffices key : ∀ n : ℕ, ∀ s s', s.x = (n : ℤ) → Z s s' → XY s' ∧ T s s' by
    intro s s' hZ hx
    exact key s.x.toNat s s' (by omega) hZ
  intro n
  induction n with
  | zero =>
    intro s s' hx hZ
    have := (zapC_apply Z s s').1 (h s s' hZ)
    rcases this with ⟨_, rfl⟩ | ⟨hne, _⟩
    · exact (base_iff (by simpa using hx)).1 rfl
    · exact absurd (by simpa using hx) hne
  | succ n ih =>
    intro s s' hx hZ
    have := (zapC_apply Z s s').1 (h s s' hZ)
    rcases this with ⟨h0, _⟩ | ⟨_, hZ'⟩
    · omega
    · have := ih (step s) s' (by simp [step]; omega) hZ'
      exact ⟨this.1, (T_step s s').1 this.2⟩

/-- A specification refines an equal one. -/
theorem refines_of_eq {P Q : Spec ZS} (h : P = Q) : Refines P Q := fun _ _ hq => h ▸ hq

/-- Fixed-point induction: every solution `Z = constructor Z` refines (a). -/
theorem solA_refines_of_fixedPoint {Z : Spec ZS} (h : zapC Z = Z) : Refines solA Z :=
  solA_refines_of_prefixed (refines_of_eq h)

/-- (a) is the weakest fixed point of the constructor: a fixed point refined by
every fixed point. -/
theorem solA_weakest : zapC solA = solA ∧ ∀ Z, zapC Z = Z → Refines solA Z :=
  ⟨zapC_solA, fun _ h => solA_refines_of_fixedPoint h⟩

/-- Any `zap` defined by the fixed-point equation "refines the weakest solution
`(a) ⇐ zap`, so we can use it to solve problems, and it is refined by its
constructor `zap ⇐ constructor zap`, so we can execute it". -/
theorem zap_use_and_execute {zap : Spec ZS} (h : zapC zap = zap) :
    Refines solA zap ∧ Refines zap (zapC zap) :=
  ⟨solA_refines_of_fixedPoint h, refines_of_eq h.symm⟩

/-! ### Recursive program construction (aPToP §6.1.0) -/

/-- `zap₀ = ⊤`, `zapₙ₊₁ = constructor zapₙ`: "we obtain the next description of
zap by substituting `zapₙ` for zap in the constructor". -/
def zapN : ℕ → Spec ZS
  | 0 => top
  | n + 1 => zapC (zapN n)

/-- `zapₙ = 0≤x<n ⇒ x′=y′=0 ∧ t′=t+x`: "describes the computation as well as
possible after `n` uses of the constructor", "proved using nat induction". -/
theorem zapN_eq (n : ℕ) : zapN n = fun s s' => 0 ≤ s.x ∧ s.x < (n : ℤ) → XY s' ∧ T s s' := by
  induction n with
  | zero =>
    exact Spec.ext fun s s' => ⟨fun _ h => absurd h.2 (by omega), fun _ => trivial⟩
  | succ n ih =>
    refine Spec.ext fun s s' => ?_
    rw [zapN, zapC_apply, ih]
    by_cases hx : s.x = 0
    · rw [base_iff hx]
      simp only [hx, ne_eq, not_true_eq_false, false_and, or_false, true_and]
      constructor
      · intro h _; exact h
      · intro h; exact h ⟨le_rfl, by push_cast; omega⟩
    · simp only [hx, false_and, false_or, ne_eq, not_false_eq_true, true_and, step_x, T_step]
      constructor
      · intro h ⟨h0, hn⟩; exact h ⟨by omega, by push_cast at hn ⊢; omega⟩
      · intro h ⟨h0, hn⟩; exact h ⟨by omega, by push_cast at hn ⊢; omega⟩

/-- `zap₁ = 0≤x<1 ⇒ x′=y′=0 ∧ t′=t`, the book's first step. -/
theorem zapN_one : zapN 1 = fun s s' => 0 ≤ s.x ∧ s.x < 1 → XY s' ∧ T s s' := by
  rw [zapN_eq]; push_cast; rfl

/-- Each `zapₙ` is refined by (a): the `zapₙ` approximate `zap∞ = (a)` from above. -/
theorem zapN_refines_solA (n : ℕ) : Refines (zapN n) solA := by
  rw [zapN_eq]
  intro s s' h ⟨h0, _⟩
  exact h h0

/-- "The next step is to replace `n` with `∞`": (a) is the intersection of all
the `zapₙ`. -/
theorem solA_eq_iInf_zapN : solA = fun s s' => ∀ n, zapN n s s' := by
  refine Spec.ext fun s s' => ⟨fun h n => zapN_refines_solA n s s' h, fun h hx => ?_⟩
  have := h (s.x.toNat + 1)
  rw [zapN_eq] at this
  exact this ⟨hx, by push_cast; omega⟩

end Zap

/-! ### Loop definition (aPToP §6.1.1) -/

namespace LoopDefinition

open Zap

/-- The while-loop constructor with recursive timing:
`W ↦ t′≥t ∧ if b then P. t:= t+1. W else ok`. -/
def whileC (b : ZS → Prop) (P W : Spec ZS) : Spec ZS :=
  and timeNondecreasing (cond b (seq P (seq tick W)) ok)

/-- The three axioms for `while b do P od` (recursive timing):
`t′≥t ⇐ while b do P od`; `if b then P. t:= t+1. while b do P od else ok ⇐ while b do P od`;
and induction `∀σ,σ′· (t′≥t ∧ if b then P. t:= t+1. W else ok ⇐ W) ⇒ ∀σ,σ′· while b do P od ⇐ W`.
"These three axioms are closely analogous to the axioms `0: nat`, `nat+1: nat`,
`0, B+1: B ⇒ nat: B` that define nat." -/
structure WhileAxioms (Wh : Spec ZS) (b : ZS → Prop) (P : Spec ZS) : Prop where
  /-- "A base case saying that at least time does not decrease." -/
  time : Refines timeNondecreasing Wh
  /-- "Takes a single step, saying that `while b do P od` refines (implements) its first unrolling." -/
  unroll : Refines (cond b (seq P (seq tick Wh)) ok) Wh
  /-- "Induction, says that it is the weakest specification that satisfies the first two axioms." -/
  induction : ∀ W, Refines (whileC b P W) W → Refines Wh W

variable {Wh : Spec ZS} {b : ZS → Prop} {P : Spec ZS}

/-- The constructor is monotonic. -/
theorem whileC_mono {W W' : Spec ZS} (h : Refines W W') : Refines (whileC b P W) (whileC b P W') :=
  refines_and_mono (refines_refl _) (refines_cond_mono b (refines_seq_mono (refines_refl _)
    (refines_seq_mono (refines_refl _) h)) (refines_refl _))

/-- The first two axioms say that `while b do P od` is a pre-fixed point of the constructor. -/
theorem WhileAxioms.prefixed (h : WhileAxioms Wh b P) : Refines (whileC b P Wh) Wh :=
  fun s s' hW => ⟨h.time s s' hW, h.unroll s s' hW⟩

/-- Fixed-point construction: `while b do P od = t′≥t ∧ if b then P. t:= t+1. while b do P od else ok`. -/
theorem WhileAxioms.fixedPoint (h : WhileAxioms Wh b P) : whileC b P Wh = Wh :=
  refines_antisymm _ _ h.prefixed (h.induction _ (whileC_mono h.prefixed))

/-- Fixed-point induction: `∀σ,σ′· (W = t′≥t ∧ if b then P. t:= t+1. W else ok) ⇒ ∀σ,σ′· while b do P od ⇐ W`. -/
theorem WhileAxioms.fixedPoint_induction (h : WhileAxioms Wh b P) (W : Spec ZS) (hW : whileC b P W = W) :
    Refines Wh W :=
  h.induction W (refines_of_eq hW)

/-- The axioms are consistent: the union of all specifications `W` with
`t′≥t ∧ if b then P. t:= t+1. W else ok ⇐ W` satisfies them. -/
theorem exists_whileAxioms (b : ZS → Prop) (P : Spec ZS) : ∃ Wh, WhileAxioms Wh b P := by
  refine ⟨fun s s' => ∃ W : Spec ZS, Refines (whileC b P W) W ∧ W s s', ?_, ?_, ?_⟩
  · rintro s s' ⟨W, hW, hWs⟩
    exact (hW s s' hWs).1
  · rintro s s' ⟨W, hW, hWs⟩
    rcases (hW s s' hWs).2 with ⟨hb, u, hPu, v, hv, hWv⟩ | ⟨hb, hok⟩
    · exact Or.inl ⟨hb, u, hPu, v, hv, W, hW, hWv⟩
    · exact Or.inr ⟨hb, hok⟩
  · intro W hW s s' hWs
    exact ⟨W, hW, hWs⟩

/-- Two specifications satisfying the axioms are equal. -/
theorem WhileAxioms.unique {Wh' : Spec ZS} (h : WhileAxioms Wh b P) (h' : WhileAxioms Wh' b P) : Wh = Wh' :=
  refines_antisymm _ _ (h.induction _ h'.prefixed) (h'.induction _ h.prefixed)

/-! #### The contrast with Section 5.2

"From this least fixed-point definition, we cannot prove `x′≥x ⇐ while b do x′≥x od`,
which was easily proved according to Section 5.2." -/

/-- `x′ ≥ x`. -/
def xGe : Spec ZS := fun s s' => s.x ≤ s'.x

/-- In the refinement-notation reading of Section 5.2, `x′≥x ⇐ while b do x′≥x od`
is a theorem, for any `b`. -/
theorem whileRefines_xGe (b : ZS → Prop) : WhileRefines xGe b xGe := by
  rintro s s' (⟨-, u, hu, hu'⟩ | ⟨-, hok⟩)
  · exact hu.trans hu'
  · exact hok ▸ le_rfl

/-- In the least-fixed-point reading, `while ⊤ do x′≥x od` allows every final
state at time `∞`: any `Wh` satisfying the axioms is refined by `t′ = ∞`. -/
theorem WhileAxioms.refines_top_time (h : WhileAxioms Wh (fun _ => True) xGe) :
    Refines Wh fun _ s' => s'.t = ⊤ := by
  refine h.induction _ fun s s' hW => ?_
  exact ⟨show s.t ≤ s'.t from hW ▸ le_top, Or.inl ⟨trivial, s, le_rfl, _, rfl, hW⟩⟩

/-- Hence `x′≥x ⇐ while ⊤ do x′≥x od` is *not* derivable from the axioms: the
loop may end with `x′ < x` (at time `∞`). -/
theorem not_xGe_refines_while (h : WhileAxioms Wh (fun _ => True) xGe) : ¬ Refines xGe Wh := fun hx => by
  have := hx ⟨0, 0, 0⟩ ⟨⊤, -1, 0⟩ (h.refines_top_time ⟨0, 0, 0⟩ ⟨⊤, -1, 0⟩ rfl)
  simp [xGe] at this

end LoopDefinition

end LaPToP.RecursiveDefinition
