import LaPToP.ProgramTheory.Time
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Fast exponentiation

This module formalizes Subsection 4.2.6 (Fast Exponentiation) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), Exercise 180.

"Given rational variables `x` and `z` and natural variable `y`, write a
program for `z′ = x^y` that runs fast without using exponentiation. ... The
idea is to accumulate a product, using variable `z` as accumulator. Define
`P = z′ = z×x^y`. We can solve the problem as follows, though this solution
does not give the fastest possible computation. `z′=x^y ⇐ z:= 1. P`,
`P ⇐ if y=0 then ok else y>0 ⇒ P`, `y>0 ⇒ P ⇐ z:= z×x. y:= y–1. P`. To speed up
the computation, we change our refinement of `y>0 ⇒ P` to test whether `y`
is even or odd; in the odd case we make no improvement but in the even case
we can cut `y` in half. ... Before we consider time, here is the fast
exponentiation program again.

    z′=x^y ⇐ z:= 1. P
    P ⇐ if even y then even y ⇒ P else odd y ⇒ P
    even y ⇒ P ⇐ if y=0 then ok else even y ∧ y>0 ⇒ P
    odd y ⇒ P ⇐ z:= z×x. y:= y–1. even y ⇒ P
    even y ∧ y>0 ⇒ P ⇐ x:= x×x. y:= y/2. y>0 ⇒ P
    y>0 ⇒ P ⇐ if even y then even y ∧ y>0 ⇒ P else odd y ⇒ P

In the recursive time measure, every loop of calls must include a time
increment. In this program, a single time increment charged to the call
`y>0 ⇒ P` does the trick. ... it is easier to prove the less precise
specification `T` defined as `T = if y=0 then t′=t else t′ ≤ t + log y`. To do
so, we need to refine `T` with exactly the same refinement structure that we
used to refine the result `z′=x^y` so that we can conjoin the result and
timing specifications according to Refinement by Parts."

## The model

The state has `x z : ℚ`, `y : ℕ` and the time in `xnat`; the recursive calls
are the specifications being refined. `log y` is `Nat.log 2 y` (the floor of
the binary logarithm; `T` only bounds the time, so this is the book's `T`).
Proved: the simple solution's three refinements, the six refinements of the
fast program, and the six timing refinements with the same structure.
-/

namespace LaPToP.ProgramTheory

namespace FastExp

open Spec

/-- The state: rational `x`, `z`, natural `y`, and the time. -/
structure ES where
  /-- The base `x`. -/
  x : ℚ
  /-- The accumulator `z`. -/
  z : ℚ
  /-- The exponent `y`. -/
  y : ℕ
  /-- The time. -/
  t : ℕ∞

def assignX (e : ES → ℚ) : Spec ES := fun s s' => s' = { s with x := e s }
def assignZ (e : ES → ℚ) : Spec ES := fun s s' => s' = { s with z := e s }
def assignY (e : ES → ℕ) : Spec ES := fun s s' => s' = { s with y := e s }
def tick : Spec ES := fun s s' => s' = { s with t := s.t + 1 }

theorem assignX_seq (e : ES → ℚ) (P : Spec ES) : seq (assignX e) P = fun s s' => P { s with x := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignZ_seq (e : ES → ℚ) (P : Spec ES) : seq (assignZ e) P = fun s s' => P { s with z := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignY_seq (e : ES → ℕ) (P : Spec ES) : seq (assignY e) P = fun s s' => P { s with y := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem tick_seq (P : Spec ES) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- `b ⇒ S`. -/
def guard (b : ES → Prop) (S : Spec ES) : Spec ES := fun s s' => b s → S s s'

/-- `z′ = x^y`. -/
def Z : Spec ES := fun s s' => s'.z = s.x ^ s.y

/-- `P = z′ = z×x^y`. -/
def P : Spec ES := fun s s' => s'.z = s.z * s.x ^ s.y

/-- `(x×x)^(y/2) = x^y` for even `y`. -/
theorem mul_self_pow_div_two (x : ℚ) {y : ℕ} (h : Even y) : (x * x) ^ (y / 2) = x ^ y := by
  obtain ⟨k, rfl⟩ := h
  rw [← two_mul, Nat.mul_div_cancel_left k (by norm_num), ← pow_two, ← pow_mul]

/-! ### The simple solution -/

/-- `z′=x^y ⇐ z:= 1. P`. -/
theorem simple₁ : Refines Z (seq (assignZ fun _ => 1) P) := by
  intro s s' h
  rw [assignZ_seq] at h
  simpa [Z, P] using h

/-- `P ⇐ if y=0 then ok else y>0 ⇒ P`. -/
theorem simple₂ : Refines P (cond (fun s => s.y = 0) ok (guard (fun s => 0 < s.y) P)) := by
  rintro s s' (⟨hy, rfl⟩ | ⟨hy, h⟩)
  · simp [P, hy]
  · exact h (Nat.pos_of_ne_zero hy)

/-- `y>0 ⇒ P ⇐ z:= z×x. y:= y–1. P`. -/
theorem simple₃ : Refines (guard (fun s => 0 < s.y) P) (seq (assignZ fun s => s.z * s.x) (seq (assignY fun s => s.y - 1) P)) := by
  intro s s' h hy
  rw [assignZ_seq, assignY_seq] at h
  simp only [P] at h ⊢
  rw [h, show s.y = (s.y - 1) + 1 by omega, pow_succ]
  simp only [Nat.add_sub_cancel]
  ring

/-! ### The fast program -/

/-- `P ⇐ if even y then even y ⇒ P else odd y ⇒ P`. -/
theorem fast₂ : Refines P (cond (fun s => Even s.y) (guard (fun s => Even s.y) P) (guard (fun s => Odd s.y) P)) := by
  rintro s s' (⟨he, h⟩ | ⟨he, h⟩)
  · exact h he
  · exact h (Nat.not_even_iff_odd.mp he)

/-- `even y ⇒ P ⇐ if y=0 then ok else even y ∧ y>0 ⇒ P`. -/
theorem fast₃ :
    Refines (guard (fun s => Even s.y) P) (cond (fun s => s.y = 0) ok (guard (fun s => Even s.y ∧ 0 < s.y) P)) := by
  rintro s s' (⟨hy, rfl⟩ | ⟨hy, h⟩) he
  · simp [P, hy]
  · exact h ⟨he, Nat.pos_of_ne_zero hy⟩

/-- `odd y ⇒ P ⇐ z:= z×x. y:= y–1. even y ⇒ P`: "if `y` is initially odd and `1` is
subtracted, then it must become even". -/
theorem fast₄ :
    Refines (guard (fun s => Odd s.y) P)
      (seq (assignZ fun s => s.z * s.x) (seq (assignY fun s => s.y - 1) (guard (fun s => Even s.y) P))) := by
  intro s s' h ho
  rw [assignZ_seq, assignY_seq] at h
  obtain ⟨k, hk⟩ := ho
  have h' := h (by simp only; rw [hk, Nat.add_sub_cancel]; exact even_two_mul k)
  simp only [P] at h' ⊢
  rw [h', hk, Nat.add_sub_cancel, pow_succ]
  ring

/-- `even y ∧ y>0 ⇒ P ⇐ x:= x×x. y:= y/2. y>0 ⇒ P`: "if `y` is even and greater than `0`,
it is at least `2`; after cutting it in half, it is at least `1`". -/
theorem fast₅ :
    Refines (guard (fun s => Even s.y ∧ 0 < s.y) P)
      (seq (assignX fun s => s.x * s.x) (seq (assignY fun s => s.y / 2) (guard (fun s => 0 < s.y) P))) := by
  intro s s' h ⟨he, hy⟩
  rw [assignX_seq, assignY_seq] at h
  have h2 : 2 ≤ s.y := by obtain ⟨k, hk⟩ := he; omega
  have h' := h (by simp only; omega)
  simp only [P] at h' ⊢
  rw [h', mul_self_pow_div_two s.x he]

/-- `y>0 ⇒ P ⇐ if even y then even y ∧ y>0 ⇒ P else odd y ⇒ P`. -/
theorem fast₆ :
    Refines (guard (fun s => 0 < s.y) P)
      (cond (fun s => Even s.y) (guard (fun s => Even s.y ∧ 0 < s.y) P) (guard (fun s => Odd s.y) P)) := by
  rintro s s' (⟨he, h⟩ | ⟨he, h⟩) hy
  · exact h ⟨he, hy⟩
  · exact h (Nat.not_even_iff_odd.mp he)

/-! ### Timing -/

/-- `T = if y=0 then t′=t else t′ ≤ t + log y`. -/
def T : Spec ES := fun s s' => if s.y = 0 then s'.t = s.t else s'.t ≤ s.t + (Nat.log 2 s.y : ℕ∞)

/-- `T ⇐ z:= 1. T`. -/
theorem time₁ : Refines T (seq (assignZ fun _ => 1) T) := by
  intro s s' h
  rw [assignZ_seq] at h
  exact h

/-- `T ⇐ if even y then even y ⇒ T else odd y ⇒ T`. -/
theorem time₂ : Refines T (cond (fun s => Even s.y) (guard (fun s => Even s.y) T) (guard (fun s => Odd s.y) T)) := by
  rintro s s' (⟨he, h⟩ | ⟨he, h⟩)
  · exact h he
  · exact h (Nat.not_even_iff_odd.mp he)

/-- `even y ⇒ T ⇐ if y=0 then ok else even y ∧ y>0 ⇒ T`. -/
theorem time₃ :
    Refines (guard (fun s => Even s.y) T) (cond (fun s => s.y = 0) ok (guard (fun s => Even s.y ∧ 0 < s.y) T)) := by
  rintro s s' (⟨hy, rfl⟩ | ⟨hy, h⟩) he
  · simp [T, hy]
  · exact h ⟨he, Nat.pos_of_ne_zero hy⟩

/-- `odd y ⇒ T ⇐ z:= z×x. y:= y–1. even y ⇒ T`. -/
theorem time₄ :
    Refines (guard (fun s => Odd s.y) T)
      (seq (assignZ fun s => s.z * s.x) (seq (assignY fun s => s.y - 1) (guard (fun s => Even s.y) T))) := by
  intro s s' h ho
  rw [assignZ_seq, assignY_seq] at h
  obtain ⟨k, hk⟩ := ho
  have h' := h (by simp only; rw [hk, Nat.add_sub_cancel]; exact even_two_mul k)
  simp only [T] at h' ⊢
  rw [if_neg (by omega)]
  split_ifs at h' with h0
  · rw [h']; exact le_self_add
  · exact le_trans h' (by gcongr; exact Nat.sub_le _ _)

/-- `even y ∧ y>0 ⇒ T ⇐ x:= x×x. y:= y/2. t:= t+1. y>0 ⇒ T`: the single time increment,
`log (y/2) + 1 = log y` for `y ≥ 2`. -/
theorem time₅ :
    Refines (guard (fun s => Even s.y ∧ 0 < s.y) T)
      (seq (assignX fun s => s.x * s.x) (seq (assignY fun s => s.y / 2) (seq tick (guard (fun s => 0 < s.y) T)))) := by
  intro s s' h ⟨he, hy⟩
  rw [assignX_seq, assignY_seq, tick_seq] at h
  have h2 : 2 ≤ s.y := by obtain ⟨k, hk⟩ := he; omega
  have h' := h (by simp only; omega)
  simp only [T] at h' ⊢
  rw [if_neg (by omega)]
  rw [if_neg (by omega)] at h'
  refine le_trans h' (le_of_eq ?_)
  have hpos := Nat.log_pos (b := 2) one_lt_two h2
  have hlog : Nat.log 2 (s.y / 2) + 1 = Nat.log 2 s.y := by rw [Nat.log_div_base]; omega
  rw [add_assoc, add_comm (1 : ℕ∞), ← Nat.cast_one, ← Nat.cast_add, hlog]

/-- `y>0 ⇒ T ⇐ if even y then even y ∧ y>0 ⇒ T else odd y ⇒ T`. -/
theorem time₆ :
    Refines (guard (fun s => 0 < s.y) T)
      (cond (fun s => Even s.y) (guard (fun s => Even s.y ∧ 0 < s.y) T) (guard (fun s => Odd s.y) T)) := by
  rintro s s' (⟨he, h⟩ | ⟨he, h⟩) hy
  · exact h ⟨he, hy⟩
  · exact h (Nat.not_even_iff_odd.mp he)

end FastExp

end LaPToP.ProgramTheory
