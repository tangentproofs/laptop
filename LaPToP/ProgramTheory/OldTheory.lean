import LaPToP.ProgramTheory.Time
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Old program theory

This module formalizes Section 4.4 (Old Program Theory) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), pp. 65–67.

"The original method of proving properties of a computation was to place
assertions at strategic points within a program to describe the state of the
computation at those points. ... An assertion situated at the start of a
program is called a precondition for that program; an assertion situated at
the end of a program is called a postcondition ... An assertion situated at the
start and end of a program (often a loop) is called an invariant ... If we
have a precondition `P` and postcondition `R` for a program, we can form a
specification `P ⇒ R′` for the program. But specifications are not necessarily
implications with only unprimed variables in the antecedent and only primed
variables in the consequent, and they are not necessarily decomposable into a
precondition and postcondition. ... For examples, the specifications `P=R′`,
`P⧧R′`, `(P⇒R′) ∧ (Q⇒S′)` cannot be written as precondition-postcondition
pairs. ... Let `P` and `S` be specifications. The exact precondition for `P` to
be refined by `S` is `∀σ′· P⇐S`. The exact postcondition for `P` to be refined
by `S` is `∀σ· P⇐S`. ... Any assertion that implies the exact precondition is
called a sufficient precondition. Any assertion implied by the exact
precondition is called a necessary precondition. Any assertion that implies
the exact postcondition is called a sufficient postcondition. Any assertion
implied by the exact postcondition is called a necessary postcondition. ...
The old theory ... used the words “weakest precondition” to mean “exact
precondition”, and the words “strongest postcondition” to mean “exact
postcondition”. ... Let `S` be a specification, let `I` be an assertion with
all nonlocal variables unprimed, and let `I′` be the same as `I` but with primes
on all nonlocal variables. Then `I` is an invariant for `S` if `I ⇒ I′` is
refined by `S`. ... Here are two equivalent definitions. `∀σ, σ′· I∧S ⇒ I′`,
`∀σ, σ′· I ⇒ (S ⇒ I′)`. ... A variant is a natural-valued expression whose
value decreases each iteration. A variant is really just a time bound, using
the recursive measure, with a clock that runs backward."

## The model

Everything is stated for `Spec σ` of Chapter 4; the examples use one integer
variable (`Spec ℤ`), two variables (`XY`, Exercise 304(f)) and the timed state
`TSt` of Section 4.2 for the variant. The three non-decomposable
specifications are `x′=x`, `x′⧧x` and `(x=0 ⇒ x′=0) ∧ (x=1 ⇒ x′=1)` (the book's
schematic `P`, `Q`, `R`, `S` instantiated). "A variant is really just a time
bound" is proved as: for a loop `L ⇐ if b then S. t:= t+1. L else ok` whose
body `S` decreases the variant `v` (and does not touch `t`), the time bound
`t′ ≤ t+v` is refined by the loop body with the bound itself as the recursive
call. The remark that variants cannot prove nontermination is prose.
-/

namespace LaPToP.ProgramTheory

namespace OldTheory

open Spec

universe u

variable {σ : Type u}

/-! ### Precondition-postcondition pairs -/

/-- The specification `P ⇒ R′` formed from a precondition `P` and a postcondition `R`. -/
def prePost (P R : σ → Prop) : Spec σ := fun s s' => P s → R s'

/-- `x′=x` (the book's `P=R′`) "cannot be written as a precondition-postcondition pair". -/
theorem ok_not_prePost : ¬ ∃ P R : ℤ → Prop, (ok : Spec ℤ) = prePost P R := by
  rintro ⟨P, R, h⟩
  have e : ∀ x x' : ℤ, x' = x ↔ (P x → R x') := fun x x' => by
    have := congrFun (congrFun h x) x'
    simpa [Spec.ok, prePost] using this
  have h01 := e 0 1
  have h00 := e 0 0
  have h11 := e 1 1
  have h10 := e 1 0
  by_cases hP0 : P 0
  · have hR0 : R 0 := (h00.1 rfl) hP0
    have hR1 : ¬ R 1 := fun hR1 => absurd (h01.2 fun _ => hR1) (by norm_num)
    by_cases hP1 : P 1
    · exact hR1 ((h11.1 rfl) hP1)
    · exact absurd (h10.2 fun h => absurd h hP1) (by norm_num)
  · exact absurd (h01.2 fun h => absurd h hP0) (by norm_num)

/-- `x′⧧x` (the book's `P⧧R′`) cannot be written as a precondition-postcondition pair. -/
theorem ne_not_prePost : ¬ ∃ P R : ℤ → Prop, (fun x x' : ℤ => x' ≠ x) = prePost P R := by
  rintro ⟨P, R, h⟩
  have e : ∀ x x' : ℤ, x' ≠ x ↔ (P x → R x') := fun x x' => by
    have := congrFun (congrFun h x) x'
    simpa [prePost] using this
  have hR1 : R 1 := (e 0 1).1 (by norm_num) ((Classical.not_imp.1 fun hi => (e 0 0).2 hi rfl).1)
  exact (Classical.not_imp.1 fun hi => (e 1 1).2 hi rfl).2 hR1

/-- `(x=0 ⇒ x′=0) ∧ (x=1 ⇒ x′=1)` (the book's `(P⇒R′) ∧ (Q⇒S′)`) cannot be written as a
precondition-postcondition pair. -/
theorem and_not_prePost :
    ¬ ∃ P R : ℤ → Prop, (fun x x' : ℤ => (x = 0 → x' = 0) ∧ (x = 1 → x' = 1)) = prePost P R := by
  rintro ⟨P, R, h⟩
  have e : ∀ x x' : ℤ, ((x = 0 → x' = 0) ∧ (x = 1 → x' = 1)) ↔ (P x → R x') := fun x x' => by
    have := congrFun (congrFun h x) x'
    simpa [prePost] using this
  have hP0 : P 0 := (Classical.not_imp.1 fun hi => absurd ((e 0 1).2 hi).1 (by norm_num)).1
  have hP1 : P 1 := (Classical.not_imp.1 fun hi => absurd ((e 1 0).2 hi).2 (by norm_num)).1
  have hR0 : R 0 := (e 0 0).1 (by norm_num) hP0
  have hR1 : R 1 := (e 1 1).1 (by norm_num) hP1
  exact absurd ((e 0 1).2 fun _ => hR1).1 (by norm_num)

/-! ### Exact preconditions and postconditions -/

/-- "The exact precondition for `P` to be refined by `S` is `∀σ′· P⇐S`." -/
def exactPre (P S : Spec σ) : σ → Prop := fun s => ∀ s', S s s' → P s s'

/-- "The exact postcondition for `P` to be refined by `S` is `∀σ· P⇐S`." -/
def exactPost (P S : Spec σ) : σ → Prop := fun s' => ∀ s, S s s' → P s s'

variable (P S : Spec σ)

/-- "These are the same as refinement except that the quantification is over only one state." -/
theorem refines_iff_exactPre : Refines P S ↔ ∀ s, exactPre P S s := Iff.rfl

theorem refines_iff_exactPost : Refines P S ↔ ∀ s', exactPost P S s' :=
  ⟨fun h s' s hS => h s s' hS, fun h s s' hS => h s' s hS⟩

/-- "We should weaken our problem specification with that antecedent": `exactPre ⇒ P ⇐ S`. -/
theorem refines_weaken_pre : Refines (fun s s' => exactPre P S s → P s s') S :=
  fun _ s' hS h => h s' hS

/-- ... and likewise with the exact postcondition: `exactPost′ ⇒ P ⇐ S`. -/
theorem refines_weaken_post : Refines (fun s s' => exactPost P S s' → P s s') S :=
  fun s _ hS h => h s hS

/-- "Any assertion that implies the exact precondition is called a sufficient precondition." -/
def SufficientPre (A : σ → Prop) : Prop := ∀ s, A s → exactPre P S s
/-- "Any assertion implied by the exact precondition is called a necessary precondition." -/
def NecessaryPre (A : σ → Prop) : Prop := ∀ s, exactPre P S s → A s
/-- "Any assertion that implies the exact postcondition is called a sufficient postcondition." -/
def SufficientPost (A : σ → Prop) : Prop := ∀ s', A s' → exactPost P S s'
/-- "Any assertion implied by the exact postcondition is called a necessary postcondition." -/
def NecessaryPost (A : σ → Prop) : Prop := ∀ s', exactPost P S s' → A s'

/-- "The exact precondition is the necessary and sufficient precondition." -/
theorem exactPre_sufficient_necessary : SufficientPre P S (exactPre P S) ∧ NecessaryPre P S (exactPre P S) :=
  ⟨fun _ h => h, fun _ h => h⟩

/-- "The exact postcondition is the necessary and sufficient postcondition." -/
theorem exactPost_sufficient_necessary : SufficientPost P S (exactPost P S) ∧ NecessaryPost P S (exactPost P S) :=
  ⟨fun _ h => h, fun _ h => h⟩

/-! ### One integer variable (aPToP p. 66) -/

/-- `x:= e` in one integer variable. -/
def assignX (e : ℤ → ℤ) : Spec ℤ := fun x x' => x' = e x

/-- `x′>5`. -/
def gt5 : Spec ℤ := fun _ x' => x' > 5
/-- `x>4` — "unimplementable" as a specification. -/
def pre4 : Spec ℤ := fun x _ => x > 4

/-- "Although `x′>5` is not refined by `x:= x+1`". -/
theorem not_refines_gt5 : ¬ Refines gt5 (assignX (· + 1)) := fun h => by
  have := h 0 1 rfl
  simp [gt5] at this

/-- "`x>4` is unimplementable". -/
theorem not_implementable_pre4 : ¬ Implementable pre4 := fun h => by
  obtain ⟨_, hx⟩ := h 0
  simp [pre4] at hx

/-- "(the exact precondition for `x′>5` to be refined by `x:= x+1`) = ∀x′· x′>5 ⇐ x′=x+1 = x+1 > 5
= x>4". -/
theorem exactPre_gt5 : exactPre gt5 (assignX (· + 1)) = fun x => x > 4 := by
  funext x
  apply propext
  simp only [exactPre, assignX, gt5]
  constructor
  · intro h; have := h (x + 1) rfl; omega
  · rintro h _ rfl; omega

/-- "(the exact postcondition for `x>4` to be refined by `x:= x+1`) = ∀x· x>4 ⇐ x′=x+1 = x′–1 > 4
= x′>5". -/
theorem exactPost_pre4 : exactPost pre4 (assignX (· + 1)) = fun x' => x' > 5 := by
  funext x'
  apply propext
  simp only [exactPost, assignX, pre4]
  constructor
  · intro h; have := h (x' - 1) (by omega); omega
  · rintro h x rfl; omega

/-- The refinement `x>4 ⇒ x′>5 ⇐ x:= x+1`. -/
theorem refines_pre4_gt5 : Refines (fun x x' => x > 4 → x' > 5) (assignX (· + 1)) := by
  have := refines_weaken_pre gt5 (assignX (· + 1))
  rwa [exactPre_gt5] at this

/-- The refinement `x′>5 ⇒ x>4 ⇐ x:= x+1`. -/
theorem refines_gt5_pre4 : Refines (fun x x' => x' > 5 → x > 4) (assignX (· + 1)) := by
  have := refines_weaken_post pre4 (assignX (· + 1))
  rwa [exactPost_pre4] at this

/-- "Use the Contrapositive Law to rewrite the specification `x′>5 ⇒ x>4` as the equivalent
specification `x≤4 ⇒ x′≤5`." -/
theorem contrapositive_form : (fun x x' : ℤ => x' > 5 → x > 4) = fun x x' => x ≤ 4 → x' ≤ 5 := by
  funext x x'; apply propext; omega

/-- "`x>2` is a necessary (but not sufficient) precondition for `x:= x+1` to refine `x′>5`." -/
theorem necessary_not_sufficient_pre :
    NecessaryPre gt5 (assignX (· + 1)) (fun x => x > 2) ∧ ¬ SufficientPre gt5 (assignX (· + 1)) (fun x => x > 2) := by
  simp only [NecessaryPre, SufficientPre, exactPre_gt5]
  refine ⟨fun x h => by omega, fun h => ?_⟩
  have := h 3 (by norm_num); omega

/-- "`x>6` is a sufficient (but not necessary) precondition for `x:= x+1` to refine `x′>5`." -/
theorem sufficient_not_necessary_pre :
    SufficientPre gt5 (assignX (· + 1)) (fun x => x > 6) ∧ ¬ NecessaryPre gt5 (assignX (· + 1)) (fun x => x > 6) := by
  simp only [NecessaryPre, SufficientPre, exactPre_gt5]
  refine ⟨fun x h => by omega, fun h => ?_⟩
  have := h 5 (by norm_num); omega

/-- "`x>4` is the exact (necessary and sufficient) precondition for `x:= x+1` to refine `x′>5`." -/
theorem exact_pre :
    SufficientPre gt5 (assignX (· + 1)) (fun x => x > 4) ∧ NecessaryPre gt5 (assignX (· + 1)) (fun x => x > 4) := by
  rw [← exactPre_gt5]; exact exactPre_sufficient_necessary _ _

/-- "For `x>4` to be refined by `x:= x+1`, a necessary (but not sufficient) postcondition is `x′>3`." -/
theorem necessary_not_sufficient_post :
    NecessaryPost pre4 (assignX (· + 1)) (fun x' => x' > 3) ∧ ¬ SufficientPost pre4 (assignX (· + 1)) (fun x' => x' > 3) := by
  simp only [NecessaryPost, SufficientPost, exactPost_pre4]
  refine ⟨fun x h => by omega, fun h => ?_⟩
  have := h 4 (by norm_num); omega

/-- "... a sufficient (but not necessary) postcondition is `x′>7`." -/
theorem sufficient_not_necessary_post :
    SufficientPost pre4 (assignX (· + 1)) (fun x' => x' > 7) ∧ ¬ NecessaryPost pre4 (assignX (· + 1)) (fun x' => x' > 7) := by
  simp only [NecessaryPost, SufficientPost, exactPost_pre4]
  refine ⟨fun x h => by omega, fun h => ?_⟩
  have := h 6 (by norm_num); omega

/-- "... the exact (necessary and sufficient) postcondition is `x′>5`." -/
theorem exact_post :
    SufficientPost pre4 (assignX (· + 1)) (fun x' => x' > 5) ∧ NecessaryPost pre4 (assignX (· + 1)) (fun x' => x' > 5) := by
  rw [← exactPost_pre4]; exact exactPost_sufficient_necessary _ _

/-! ### Exercise 301(c): `x:= x²` moves `x` farther from zero (aPToP pp. 66–67) -/

/-- `abs x′ > abs x`: "what it means to move `x` farther from zero". -/
def farther : Spec ℤ := fun x x' => |x'| > |x|

/-- `abs (x²) > abs x = x⧧–1 ∧ x⧧0 ∧ x⧧1`, "by the arithmetic properties of `abs x` and `x²`". -/
theorem abs_sq_gt_iff (x : ℤ) : |x ^ 2| > |x| ↔ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> norm_num at h
  · rintro ⟨h1, h0, h2⟩
    have h2le : 2 ≤ |x| := by
      rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx]; omega
      · rw [abs_of_neg hx]; omega
    rw [abs_of_nonneg (sq_nonneg x)]
    nlinarith [sq_abs x]

/-- "(the exact precondition for `abs x′ > abs x` to be refined by `x:= x²`) = ∀x′· abs x′ > abs x ⇐
x′ = x² = abs (x²) > abs x = x⧧–1 ∧ x⧧0 ∧ x⧧1. If `x` starts anywhere but `–1`, `0`, or `1`, it will
move farther from zero." -/
theorem exactPre_farther : exactPre farther (assignX fun x => x ^ 2) = fun x => x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 := by
  funext x
  apply propext
  simp only [exactPre, assignX, farther]
  rw [← abs_sq_gt_iff]
  exact ⟨fun h => h _ rfl, fun h _ hx => hx ▸ h⟩

/-- "(the exact postcondition for `abs x′ > abs x` to be refined by `x:= x²`) = ∀x· abs x′ > abs x ⇐
x′ = x² = x′⧧0 ∧ x′⧧1. If `x` ends anywhere but `0` or `1`, it did move farther from zero." -/
theorem exactPost_farther : exactPost farther (assignX fun x => x ^ 2) = fun x' => x' ≠ 0 ∧ x' ≠ 1 := by
  funext x'
  apply propext
  simp only [exactPost, assignX, farther]
  constructor
  · intro h
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · have := h 0 (by rw [h0]; norm_num); rw [h0] at this; simp at this
    · have := h 1 (by rw [h1]; norm_num); rw [h1] at this; simp at this
  · rintro ⟨h0, h1⟩ x rfl
    rw [abs_sq_gt_iff]
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp at h0 h1

/-! ### Invariants (aPToP p. 67) -/

/-- "`I` is an invariant for `S` if `I ⇒ I′` is refined by `S`." -/
def IsInvariant (I : σ → Prop) (S : Spec σ) : Prop := Refines (fun s s' => I s → I s') S

variable (I : σ → Prop)

/-- The first equivalent definition: `∀σ, σ′· I∧S ⇒ I′`. -/
theorem isInvariant_iff₁ : IsInvariant I S ↔ ∀ s s', I s ∧ S s s' → I s' :=
  ⟨fun h s s' ⟨hI, hS⟩ => h s s' hS hI, fun h s s' hS hI => h s s' ⟨hI, hS⟩⟩

/-- The second equivalent definition: `∀σ, σ′· I ⇒ (S ⇒ I′)`. -/
theorem isInvariant_iff₂ : IsInvariant I S ↔ ∀ s s', I s → (S s s' → I s') :=
  ⟨fun h s s' hI hS => h s s' hS hI, fun h s s' hS hI => h s s' hI hS⟩

/-- A state with two integer variables `x`, `y` (Exercise 304(f)). -/
structure XY where
  /-- The variable `x`. -/
  x : ℤ
  /-- The variable `y`. -/
  y : ℤ

/-- `x:= e`. -/
def XY.assignX (e : XY → ℤ) : Spec XY := fun s s' => s' = { s with x := e s }
/-- `y:= e`. -/
def XY.assignY (e : XY → ℤ) : Spec XY := fun s s' => s' = { s with y := e s }

/-- Substitution Law for `x:= e`. -/
theorem XY.assignX_seq (e : XY → ℤ) (P : Spec XY) : seq (XY.assignX e) P = fun s s' => P { s with x := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- "Exercise 304(f) asks us to prove that `y=x²` is an invariant for `(x:= x+1. y:= y + 2×x – 1)`." -/
theorem invariant_304f :
    IsInvariant (fun s : XY => s.y = s.x ^ 2)
      (seq (XY.assignX fun s => s.x + 1) (XY.assignY fun s => s.y + 2 * s.x - 1)) := by
  rw [IsInvariant, XY.assignX_seq]
  rintro s s' rfl hI
  show s.y + 2 * (s.x + 1) - 1 = (s.x + 1) ^ 2
  rw [hI]; ring

/-! ### Variants (aPToP p. 67) -/

open Time

/-- "A variant is a natural-valued expression whose value decreases each iteration." -/
def IsVariant (v : σ → ℕ) (S : Spec σ) : Prop := ∀ s s', S s s' → v s' < v s

/-- "A variant is really just a time bound, using the recursive measure, with a clock that runs
backward": one iteration, charging `1`, decreases `v` and increases `t`, keeping `t + v` bounded. -/
theorem backward_clock {t t' : ℕ∞} {v v' : ℕ} (hv : v' < v) (ht : t' = t + 1) : t' + v' ≤ t + v := by
  subst ht
  have : ((1 + v' : ℕ) : ℕ∞) ≤ (v : ℕ∞) := by exact_mod_cast (by omega : 1 + v' ≤ v)
  calc t + 1 + (v' : ℕ∞) = t + ((1 + v' : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ t + v := add_le_add le_rfl this

/-- The time bound `t′ ≤ t + v`, for a variant `v` of the memory variable `x`. -/
def timeBound (v : ℤ → ℕ) : Spec TSt := fun s s' => s'.t ≤ s.t + v s.x

/-- The variant as a time bound: for the loop `L ⇐ if b then S. t:= t+1. L else ok`, if the body `S`
decreases the variant `v` (of the memory variable) when `b` holds and does not touch `t`, then
`t′ ≤ t+v` is refined by the loop body with the bound itself as the recursive call. -/
theorem timeBound_refines (b : TSt → Prop) (S : Spec TSt) (v : ℤ → ℕ)
    (hv : ∀ s s', b s → S s s' → v s'.x < v s.x) (ht : ∀ s s', S s s' → s'.t = s.t) :
    Refines (timeBound v) (cond b (seq S (seq tick (timeBound v))) ok) := by
  rintro s s' (⟨hb, s₁, hS, h⟩ | ⟨-, hok⟩)
  · rw [tick_seq] at h
    simp only [timeBound] at h ⊢
    have h1 := hv s s₁ hb hS
    have h2 := ht s s₁ hS
    calc s'.t ≤ s₁.t + 1 + v s₁.x := h
      _ ≤ s.t + v s.x := by rw [h2]; exact backward_clock h1 rfl
  · rw [Spec.ok] at hok
    subst hok
    exact le_self_add

end OldTheory

end LaPToP.ProgramTheory
