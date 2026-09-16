import LaPToP.ProgramTheory.Programs
import Mathlib.Data.ENat.Basic

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

Not formalized: the remark that time-dependent programs should use the real
time measure and the modified `wait until` of Exercise 333(b); and the space
variable `s` — space (Section 4.3) is not modelled in this development, so
"like `t`, `s` can be read but not written arbitrarily" is prose only.
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

end TimeDependence

end LaPToP.ProgramTheory
