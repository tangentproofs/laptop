import LaPToP.ProgramTheory.Programs
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENNReal.Operations

/-!
# Time and space dependence

This module formalizes Section 5.3 (Time and Space Dependence) of Eric
Hehner's *A Practical Theory of Programming* (aPToP).

"Our examples have used the time variable `t` as a ghost, or auxiliary
variable, never affecting the course of a computation. ... But if there is a
readable clock available as a time source during a computation, it can be
used to affect the computation. The assignment `deadline:= t+5` is allowed, as
is `if t≤deadline then...else...`. But the assignment `t:= 5` is not allowed.
We can look at the clock, but not reset it arbitrarily; all assignments to
`t` must correspond to the passage of time (according to some measure);
otherwise `t` would not represent the time. ... We may occasionally want to
specify the passage of time. For example, we may want the computation to
“wait until time `w`”. Let us invent a notation for it, and define it formally
as `wait until w = t:= t↑w`. Because we are not allowed to reset the clock,
`t:= t↑w` is not acceptable as a program until we refine it by a program.
Letting time be an extended natural and using recursive time,
`wait until w ⇐ if t≥w then ok else t:= t+1. wait until w` and we obtain a
busy-wait loop. We can prove this refinement by cases."

## The model

The state has the clock `t : ℕ∞`, a time-valued variable `deadline`, and an
integer variable `x`. "All assignments to `t` must correspond to the passage
of time": a specification *respects the clock* when it never decreases `t`
(`RespectsClock`). `wait until w`, `deadline:= t+5`, `t:= t+1` and the
clock-dependent conditional respect the clock; `t:= 5` does not (from `t = 7`
it would turn the clock back), which is the book's "not allowed". The
busy-wait refinement is proved by cases exactly as the book calculates it,
using `t < w ⇒ t+1 ≤ w` in `xnat` ("use `t: xnat`") and the Substitution Law.

Exercise 333(b) — "Now suppose that `t` is a nonnegative extended real time
variable, and `w` is a nonnegative extended real expression. Redefine
`wait until w` appropriately, and refine it using the real time measure (assume
any positive operation time you need)" — is formalized in the section
`RealTime` below, with the clock in `ℝ≥0∞` and an operation time `δ > 0` per
iteration of the busy-wait loop: the redefined `wait until w` says that the
computation ends at the first test after `w`, `w ≤ t′ ≤ w + δ` (and `t′ = t` if
`t ≥ w` already), which the busy-wait loop `if t≥w then ok else t:= t+δ. wait
until w` refines. The exact `t′ = t↑w` of the recursive measure is not
implementable with positive operation times; the tolerance `δ` is the honest
content of "redefine appropriately". The space variable `s` of this section —
"if a program has space usage information available to it, there is no harm in
using that information. Like `t`, `s` can be read but not written arbitrarily.
All changes to `s` must correspond to changes in space usage" — is the section
`SpaceDependence`: since space, unlike time, goes up and down, the discipline is
not a monotonicity property but a closure property, `RespectsSpace`: a
specification may read `s` freely and change it only by the space-measure
steps `s:= s+k`, `s:= s–k` with a constant `k` (the declared size of what is
allocated or released), and is closed under `if` and sequential composition.
Its semantic content, the analogue of `t ≤ t′`, is that the change of `s` is
bounded independently of the initial state (`RespectsSpace.bounded`), which an
arbitrary `s:= 5` violates (`not_respectsSpace_const`). Recursion is not
included in the closure (the recursive space analyses of Section 4.3 bound `s`
by other means).
-/

namespace LaPToP.ProgramTheory

namespace TimeDependence

open Spec

/-- The state: the clock `t`, a time-valued variable `deadline`, and an integer
variable `x`. -/
structure TD where
  /-- The clock. -/
  t : ℕ∞
  /-- A time-valued program variable. -/
  deadline : ℕ∞
  /-- An ordinary variable. -/
  x : ℤ

/-- `t:= e`. -/
def assignT (e : TD → ℕ∞) : Spec TD := fun s s' => s' = { s with t := e s }

/-- `deadline:= e`. -/
def assignDeadline (e : TD → ℕ∞) : Spec TD := fun s s' => s' = { s with deadline := e s }

/-- `t:= t+1`. -/
def tick : Spec TD := assignT fun s => s.t + 1

/-- Substitution Law for `t:= e`. -/
theorem assignT_seq (e : TD → ℕ∞) (P : Spec TD) : seq (assignT e) P = fun s s' => P { s with t := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- "All assignments to `t` must correspond to the passage of time": a
specification respects the clock if it never decreases `t`. -/
def RespectsClock (S : Spec TD) : Prop := ∀ s s', S s s' → s.t ≤ s'.t

/-- `deadline:= t+5` is allowed. -/
theorem respectsClock_assignDeadline (e : TD → ℕ∞) : RespectsClock (assignDeadline e) := by
  rintro s _ rfl
  exact le_rfl

/-- `t:= t+1` is allowed. -/
theorem respectsClock_tick : RespectsClock tick := by
  rintro s _ rfl
  exact le_self_add

/-- `if t≤deadline then S else R` is allowed when its branches are. -/
theorem respectsClock_cond {S R : Spec TD} (hS : RespectsClock S) (hR : RespectsClock R) :
    RespectsClock (cond (fun s => s.t ≤ s.deadline) S R) := by
  rintro s s' (⟨-, h⟩ | ⟨-, h⟩)
  · exact hS s s' h
  · exact hR s s' h

/-- Sequential composition of clock-respecting specifications respects the clock. -/
theorem respectsClock_seq {S R : Spec TD} (hS : RespectsClock S) (hR : RespectsClock R) :
    RespectsClock (seq S R) :=
  fun s s' ⟨u, h₁, h₂⟩ => le_trans (hS s u h₁) (hR u s' h₂)

/-- "The assignment `t:= 5` is not allowed": from `t = 7` it would turn the clock back. -/
theorem not_respectsClock_assignT_const : ¬ RespectsClock (assignT fun _ => 5) := by
  intro h
  have : (7 : ℕ∞) ≤ 5 := h ⟨7, 0, 0⟩ ⟨5, 0, 0⟩ rfl
  exact absurd this (by decide)

/-! ### `wait until w` -/

/-- `wait until w = t:= t↑w`. -/
def waitUntil (w : ℕ∞) : Spec TD := assignT fun s => max s.t w

/-- Waiting respects the clock. -/
theorem respectsClock_waitUntil (w : ℕ∞) : RespectsClock (waitUntil w) := by
  rintro s _ rfl
  exact le_max_left _ _

/-- First case: `t≥w ∧ ok = t≥w ∧ (t:= t) ⇒ t:= t↑w`. -/
theorem waitUntil_case_ge (w : ℕ∞) : Refines (waitUntil w) (and (fun s _ => w ≤ s.t) ok) := by
  rintro s s' ⟨hw, rfl⟩
  simp only [waitUntil, assignT, max_eq_left hw]

/-- Second case: `t<w ∧ (t:= t+1. t:= t↑w) = t+1 ≤ w ∧ (t:= (t+1)↑w) = t+1 ≤ w ∧ (t:= w)
= t<w ∧ (t:= t↑w) ⇒ t:= t↑w`, "in the left conjunct, use `t: xnat`; in the right
conjunct, use the Substitution Law". -/
theorem waitUntil_case_lt (w : ℕ∞) :
    Refines (waitUntil w) (and (fun s _ => ¬ w ≤ s.t) (seq tick (waitUntil w))) := by
  rintro s s' ⟨hw, h⟩
  have hlt : s.t < w := not_le.mp hw
  rw [tick, assignT_seq] at h
  simp only [waitUntil, assignT] at h ⊢
  rw [h, max_eq_right (Order.add_one_le_of_lt hlt), max_eq_right (le_of_lt hlt)]

/-- `wait until w ⇐ if t≥w then ok else t:= t+1. wait until w`, "a busy-wait loop",
by Refinement by Cases. -/
theorem waitUntil_refines (w : ℕ∞) :
    Refines (waitUntil w) (cond (fun s => w ≤ s.t) ok (seq tick (waitUntil w))) :=
  (refines_cond_iff _).mpr ⟨waitUntil_case_ge w, waitUntil_case_lt w⟩

/-- The busy-wait loop is a while-loop: `wait until w ⇐ while t<w do t:= t+1 od`. -/
theorem waitUntil_whileRefines (w : ℕ∞) :
    Refines (waitUntil w) (cond (fun s => s.t < w) (seq tick (waitUntil w)) ok) := by
  rw [cond_not]
  simpa [not_lt] using waitUntil_refines w

/-! ### Real time (Exercise 333(b)) -/

namespace RealTime

open scoped ENNReal

/-- A state with a nonnegative extended real clock `t` and an ordinary variable `x`. -/
structure RS where
  /-- The clock, a nonnegative extended real. -/
  t : ℝ≥0∞
  /-- An ordinary variable. -/
  x : ℤ

/-- `t:= e`. -/
def assignT (e : RS → ℝ≥0∞) : Spec RS := fun s s' => s' = { s with t := e s }

/-- Substitution Law for `t:= e`. -/
theorem assignT_seq (e : RS → ℝ≥0∞) (P : Spec RS) : seq (assignT e) P = fun s s' => P { s with t := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (δ : ℝ≥0∞) (w : ℝ≥0∞)

/-- One iteration of the busy-wait loop takes the operation time `δ`: `t:= t+δ`. -/
def tick : Spec RS := assignT fun s => s.t + δ

/-- `wait until w` redefined for real time: if `t ≥ w` nothing happens; otherwise the computation
ends at the first test after `w`, within one operation time: `w ≤ t′ ≤ w + δ`. Other variables
are unchanged. -/
def waitUntil : Spec RS := fun s s' =>
  s'.x = s.x ∧ (w ≤ s.t → s'.t = s.t) ∧ (s.t < w → w ≤ s'.t ∧ s'.t ≤ w + δ)

/-- Waiting respects the clock. -/
theorem waitUntil_le {s s' : RS} (h : waitUntil δ w s s') : s.t ≤ s'.t := by
  obtain ⟨-, hge, hlt⟩ := h
  rcases le_or_gt w s.t with hw | hw
  · exact (hge hw).ge
  · exact (hw.le.trans (hlt hw).1)

/-- The exact `t′ = t↑w` is a special case of the redefined specification: it satisfies it. -/
theorem waitUntil_of_max {s s' : RS} (hx : s'.x = s.x) (ht : s'.t = max s.t w) : waitUntil δ w s s' := by
  refine ⟨hx, fun hw => by rw [ht, max_eq_left hw], fun hw => ?_⟩
  rw [ht, max_eq_right hw.le]
  exact ⟨le_rfl, le_self_add⟩

/-- `wait until w ⇐ if t≥w then ok else t:= t+δ. wait until w`: the busy-wait loop with operation
time `δ` per iteration refines the redefined `wait until w` (the refinement holds for any `δ`;
positivity of `δ` is what makes the loop terminate for finite `w`, which is not part of this
refinement, as with the book's recursive-time loops). -/
theorem waitUntil_refines :
    Refines (waitUntil δ w) (cond (fun s => w ≤ s.t) ok (seq (tick δ) (waitUntil δ w))) := by
  rintro s s' (⟨hw, hok⟩ | ⟨hw, h⟩)
  · rw [Spec.ok] at hok
    subst hok
    exact ⟨rfl, fun _ => rfl, fun hlt => absurd hw (not_le.mpr hlt)⟩
  · rw [tick, assignT_seq] at h
    obtain ⟨hx, hge, hlt⟩ := h
    simp only at hx hge hlt
    have hw' : s.t < w := not_le.mp hw
    refine ⟨hx, fun h => absurd h hw, fun _ => ?_⟩
    rcases le_or_gt w (s.t + δ) with h1 | h1
    · -- the next test is already past `w`: the loop exits at time `t + δ ≤ w + δ`
      rw [hge h1]
      exact ⟨h1, add_le_add hw'.le le_rfl⟩
    · exact hlt h1

/-- The recursive-time definition `t:= t↑w` is *not* refined by the real-time loop: with a
positive operation time the loop may overshoot `w` (start at `t = 0`, `w = 1`, `δ = 2`). -/
theorem not_exact_refines :
    ¬ Refines (assignT fun s => max s.t (1 : ℝ≥0∞))
      (cond (fun s => (1 : ℝ≥0∞) ≤ s.t) ok (seq (tick 2) (assignT fun s => max s.t 1))) := by
  intro h
  have := h ⟨0, 0⟩ ⟨2, 0⟩ (Or.inr ⟨by norm_num, ⟨2, 0⟩, by simp [tick, assignT], by
    simp only [assignT]
    congr 1
    exact (max_eq_left (by norm_num : (1 : ℝ≥0∞) ≤ 2)).symm⟩)
  simp [assignT] at this

end RealTime

/-! ### Space dependence: the read-only space variable -/

namespace SpaceDependence

/-- A state with the space variable `s` (an extended natural, as in Section 4.3) and an ordinary
variable `x`. -/
structure SD where
  /-- The space variable. -/
  s : ℕ∞
  /-- An ordinary variable. -/
  x : ℤ

/-- `s:= e`. -/
def assignS (e : SD → ℕ∞) : Spec SD := fun st st' => st' = { st with s := e st }

/-- `x:= e`. -/
def assignX (e : SD → ℤ) : Spec SD := fun st st' => st' = { st with x := e st }

/-- `s:= s+k`, the space-measure step for allocating `k` units. -/
def grow (k : ℕ) : Spec SD := assignS fun st => st.s + k

/-- `s:= s–k`, the space-measure step for releasing `k` units. -/
def shrink (k : ℕ) : Spec SD := assignS fun st => st.s - k

/-- "Like `t`, `s` can be read but not written arbitrarily. All changes to `s` must correspond to
changes in space usage": a specification respects space if it is built from specifications that
do not change `s` (they may read it), the space-measure steps `s:= s+k` and `s:= s–k` for constant
`k`, conditionals (whose conditions may read `s`) and sequential compositions. -/
inductive RespectsSpace : Spec SD → Prop
  /-- Anything that leaves `s` unchanged — including reading `s` into other variables. -/
  | keep {S : Spec SD} (h : ∀ st st', S st st' → st'.s = st.s) : RespectsSpace S
  /-- Allocation of a constant amount of space. -/
  | grow (k : ℕ) : RespectsSpace (grow k)
  /-- Release of a constant amount of space. -/
  | shrink (k : ℕ) : RespectsSpace (shrink k)
  /-- `if b then P else Q`; the condition may read `s`. -/
  | cond (b : SD → Prop) {P Q : Spec SD} (hP : RespectsSpace P) (hQ : RespectsSpace Q) :
      RespectsSpace (Spec.cond b P Q)
  /-- `P. Q`. -/
  | seq {P Q : Spec SD} (hP : RespectsSpace P) (hQ : RespectsSpace Q) : RespectsSpace (Spec.seq P Q)

/-- Reading `s` into an ordinary variable respects space. -/
theorem respectsSpace_assignX (e : SD → ℤ) : RespectsSpace (assignX e) :=
  .keep fun _ _ h => by subst h; rfl

/-- `ok` respects space. -/
theorem respectsSpace_ok : RespectsSpace ok := .keep fun _ _ h => by subst h; rfl

/-- "There is no harm in using that information": `if s ≤ limit then x:= 1 else x:= 0` respects space. -/
theorem respectsSpace_read_example (limit : ℕ∞) :
    RespectsSpace (Spec.cond (fun st => st.s ≤ limit) (assignX fun _ => 1) (assignX fun _ => 0)) :=
  .cond _ (respectsSpace_assignX _) (respectsSpace_assignX _)

/-- Allocating and then releasing the same amount respects space. -/
theorem respectsSpace_grow_shrink (k : ℕ) : RespectsSpace (Spec.seq (grow k) (shrink k)) :=
  .seq (.grow k) (.shrink k)

/-- The semantic content of the discipline — the analogue of "time does not decrease": a
specification that respects space changes `s` by at most a bound `B` fixed in advance,
independently of the initial state. -/
theorem RespectsSpace.bounded {S : Spec SD} (h : RespectsSpace S) :
    ∃ B : ℕ, ∀ st st', S st st' → st'.s ≤ st.s + B ∧ st.s ≤ st'.s + B := by
  induction h with
  | keep h => exact ⟨0, fun st st' hS => by rw [h st st' hS]; simp⟩
  | grow k => exact ⟨k, fun st st' hS => by
      simp only [SpaceDependence.grow, assignS] at hS; subst hS
      exact ⟨le_rfl, le_trans le_self_add le_self_add⟩⟩
  | shrink k => exact ⟨k, fun st st' hS => by
      simp only [SpaceDependence.shrink, assignS] at hS; subst hS
      exact ⟨le_trans tsub_le_self le_self_add, le_tsub_add⟩⟩
  | cond b _ _ ihP ihQ =>
    obtain ⟨B₁, h₁⟩ := ihP
    obtain ⟨B₂, h₂⟩ := ihQ
    refine ⟨max B₁ B₂, fun st st' hS => ?_⟩
    have hm₁ : (B₁ : ℕ∞) ≤ (max B₁ B₂ : ℕ) := by exact_mod_cast le_max_left B₁ B₂
    have hm₂ : (B₂ : ℕ∞) ≤ (max B₁ B₂ : ℕ) := by exact_mod_cast le_max_right B₁ B₂
    rcases hS with ⟨-, hP⟩ | ⟨-, hQ⟩
    · obtain ⟨a, b⟩ := h₁ st st' hP
      exact ⟨a.trans (add_le_add le_rfl hm₁), b.trans (add_le_add le_rfl hm₁)⟩
    · obtain ⟨a, b⟩ := h₂ st st' hQ
      exact ⟨a.trans (add_le_add le_rfl hm₂), b.trans (add_le_add le_rfl hm₂)⟩
  | seq _ _ ihP ihQ =>
    obtain ⟨B₁, h₁⟩ := ihP
    obtain ⟨B₂, h₂⟩ := ihQ
    refine ⟨B₁ + B₂, fun st st' hS => ?_⟩
    obtain ⟨st₁, hP, hQ⟩ := hS
    obtain ⟨a₁, b₁⟩ := h₁ st st₁ hP
    obtain ⟨a₂, b₂⟩ := h₂ st₁ st' hQ
    constructor
    · calc st'.s ≤ st₁.s + B₂ := a₂
        _ ≤ st.s + B₁ + B₂ := add_le_add a₁ le_rfl
        _ = st.s + ((B₁ + B₂ : ℕ) : ℕ∞) := by push_cast; ring
    · calc st.s ≤ st₁.s + B₁ := b₁
        _ ≤ st'.s + B₂ + B₁ := add_le_add b₂ le_rfl
        _ = st'.s + ((B₁ + B₂ : ℕ) : ℕ∞) := by push_cast; ring

/-- "`s` can be read but not written arbitrarily": `s:= 5` does not respect space — from a large
enough initial space it releases an unbounded amount. -/
theorem not_respectsSpace_const : ¬ RespectsSpace (assignS fun _ => 5) := by
  intro h
  obtain ⟨B, hB⟩ := h.bounded
  have h1 := (hB ⟨((B + 6 : ℕ) : ℕ∞), 0⟩ ⟨5, 0⟩ rfl).2
  simp only at h1
  have h2 : ((B + 6 : ℕ) : ℕ∞) ≤ ((5 + B : ℕ) : ℕ∞) := by exact_mod_cast h1
  have h3 := ENat.natCast_le_natCast.mp h2
  omega

end SpaceDependence

end TimeDependence

end LaPToP.ProgramTheory
