import LaPToP.ProgramTheory.Time
import Mathlib.Data.Nat.Fib.Basic

/-!
# Fibonacci numbers

This module formalizes the first part of Subsection 4.2.7 (Fibonacci
Numbers) of Eric Hehner's *A Practical Theory of Programming* (aPToP),
Exercise 256: the linear-time solution and its timing.

"The definition of the Fibonacci numbers `fib 0 = 0`, `fib 1 = 1`,
`fib (n+2) = fib n + fib (n+1)` immediately suggests a recursive function
definition ... We did not include functions in our programming language, so
we still have some work to do. Also, the functional solution we have just
given has exponential execution time, and we can do much better. For `n≥2`,
we can find a Fibonacci number if we know the previous pair of Fibonacci
numbers. That suggests we keep track of a pair of numbers. Let `x`, `y`, and
`n` be natural variables. We refine `x′ = fib n ⇐ P` where `P` is the problem
of finding a pair of Fibonacci numbers. `P = x′ = fib n ∧ y′ = fib (n+1)`. When
`n=0`, the solution is easy. When `n≥1`, we can decrease it by `1`, find a
pair of Fibonacci numbers at that previous argument, and then move `x` and
`y` along one place. `P ⇐ if n=0 then x:= 0. y:= 1 else n:= n–1. P. x′=y ∧
y′ = x+y`. To move `x` and `y` along we need another variable. We could use a
new variable, but we already have `n`; is it safe to use `n` for this
purpose? The specification `x′=y ∧ y′ = x+y` allows `n` to change, so we can
use it if we want. `x′=y ∧ y′ = x+y ⇐ n:= x. x:= y. y:= n+y`. The time for this
solution is linear. To prove it, we keep the same refinement structure, but
we replace the specifications with new ones concerning time. We replace `P`
by `t′ = t+n` and add `t:= t+1` in front of its use; we also change `x′=y ∧
y′ = x+y` into `t′=t`. `t′ = t+n ⇐ if n=0 then x:= 0. y:= 1 else n:= n–1.
t:= t+1. t′ = t+n. t′=t`, `t′=t ⇐ n:= x. x:= y. y:= n+y`."

## The model

`fib` is Mathlib's `Nat.fib`; the state has natural `x`, `y`, `n` and the time;
the recursive call `P` is the specification. The logarithmic-time solution
with the doubling identities is the next part.
-/

namespace LaPToP.ProgramTheory

namespace Fibonacci

open Spec

/-- The state: natural `x`, `y`, `n` and the time. -/
structure FS where
  /-- `x`. -/
  x : ℕ
  /-- `y`. -/
  y : ℕ
  /-- `n`. -/
  n : ℕ
  /-- The time. -/
  t : ℕ∞

def assignX (e : FS → ℕ) : Spec FS := fun s s' => s' = { s with x := e s }
def assignY (e : FS → ℕ) : Spec FS := fun s s' => s' = { s with y := e s }
def assignN (e : FS → ℕ) : Spec FS := fun s s' => s' = { s with n := e s }
def tick : Spec FS := fun s s' => s' = { s with t := s.t + 1 }

theorem assignX_seq (e : FS → ℕ) (P : Spec FS) : seq (assignX e) P = fun s s' => P { s with x := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignY_seq (e : FS → ℕ) (P : Spec FS) : seq (assignY e) P = fun s s' => P { s with y := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignN_seq (e : FS → ℕ) (P : Spec FS) : seq (assignN e) P = fun s s' => P { s with n := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem tick_seq (P : Spec FS) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- `x′ = fib n`, the problem. -/
def Goal : Spec FS := fun s s' => s'.x = Nat.fib s.n

/-- `P = x′ = fib n ∧ y′ = fib (n+1)`, "the problem of finding a pair of Fibonacci numbers". -/
def P : Spec FS := fun s s' => s'.x = Nat.fib s.n ∧ s'.y = Nat.fib (s.n + 1)

/-- `x′=y ∧ y′ = x+y`, moving the pair along; "allows `n` to change". -/
def Shift : Spec FS := fun s s' => s'.x = s.y ∧ s'.y = s.x + s.y

/-- `x′ = fib n ⇐ P`. -/
theorem goal_refines : Refines Goal P := fun _ _ h => h.1

/-- `P ⇐ if n=0 then x:= 0. y:= 1 else n:= n–1. P. x′=y ∧ y′ = x+y`. -/
theorem P_refines :
    Refines P (cond (fun s => s.n = 0) (seq (assignX fun _ => 0) (assignY fun _ => 1))
      (seq (assignN fun s => s.n - 1) (seq P Shift))) := by
  rintro s s' (⟨hn, h⟩ | ⟨hn, h⟩)
  · rw [assignX_seq, assignY] at h
    subst h
    simp [P, hn]
  · rw [assignN_seq] at h
    obtain ⟨u, ⟨hx, hy⟩, hsx, hsy⟩ := h
    simp only at hx hy
    refine ⟨?_, ?_⟩
    · rw [hsx, hy]
      congr 1
      omega
    · rw [hsy, hx, hy, show s.n + 1 = (s.n - 1) + 2 by omega, Nat.fib_add_two]

/-- `x′=y ∧ y′ = x+y ⇐ n:= x. x:= y. y:= n+y`. -/
theorem shift_refines : Refines Shift (seq (assignN fun s => s.x) (seq (assignX fun s => s.y) (assignY fun s => s.n + s.y))) := by
  intro s s' h
  rw [assignN_seq, assignX_seq, assignY] at h
  subst h
  exact ⟨rfl, rfl⟩

/-! ### Linear time -/

/-- `t′ = t+n`. -/
def TL : Spec FS := fun s s' => s'.t = s.t + s.n

/-- `t′=t`. -/
def TS : Spec FS := fun s s' => s'.t = s.t

/-- `t′ = t+n ⇐ if n=0 then x:= 0. y:= 1 else n:= n–1. t:= t+1. t′ = t+n. t′=t`. -/
theorem time_refines :
    Refines TL (cond (fun s => s.n = 0) (seq (assignX fun _ => 0) (assignY fun _ => 1))
      (seq (assignN fun s => s.n - 1) (seq tick (seq TL TS)))) := by
  rintro s s' (⟨hn, h⟩ | ⟨hn, h⟩)
  · rw [assignX_seq, assignY] at h
    subst h
    simp [TL, hn]
  · rw [assignN_seq, tick_seq] at h
    obtain ⟨u, hu, hs⟩ := h
    simp only [TL] at hu ⊢
    rw [TS] at hs
    have hn' : (s.n - 1) + 1 = s.n := by simp only at hn; omega
    rw [hs, hu, add_assoc, add_comm (1 : ℕ∞), ← Nat.cast_succ, Nat.succ_eq_add_one, hn']

/-- `t′=t ⇐ n:= x. x:= y. y:= n+y`. -/
theorem shift_time : Refines TS (seq (assignN fun s => s.x) (seq (assignX fun s => s.y) (assignY fun s => s.n + s.y))) := by
  intro s s' h
  rw [assignN_seq, assignX_seq, assignY] at h
  subst h
  rfl

end Fibonacci

end LaPToP.ProgramTheory
