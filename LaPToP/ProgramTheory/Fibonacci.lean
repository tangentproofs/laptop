import LaPToP.ProgramTheory.Time
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Fibonacci numbers

This module formalizes Subsection 4.2.7 (Fibonacci Numbers) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), Exercise 256: the
linear-time solution and its timing, and the logarithmic-time solution and
its timing.

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

"Exercise 256 asks for a solution with logarithmic time. To get it, we need
to take the hint offered in the exercise and use the equations
`fib(2×k + 1) = (fib k)² + (fib(k+1))²`, `fib(2×k + 2) = 2 × fib k × fib(k+1) +
(fib(k+1))²`. ... `P ⇐ if n=0 then x:= 0. y:= 1 else if even n then even n ∧ n>0 ⇒ P
else odd n ⇒ P`; `odd n ⇒ P ⇐ n:= (n–1)/2. P. x′ = x² + y² ∧ y′ = 2×x×y + y²`; ...
`even n ∧ n>0 ⇒ P ⇐ n:= n/2 – 1. P. x′ = 2×x×y + y² ∧ y′ = x² + y² + x′`. The
remaining two problems ... require another variable as before, and as
before, we can use `n`. ... To prove that this program is now logarithmic
time, we define time specification `T = t′ ≤ t + log (n+1)` and we put
`t:= t+1` before calls to `T`."

## The model

`fib` is Mathlib's `Nat.fib`; the state has natural `x`, `y`, `n` and the time;
the recursive call `P` is the specification. The doubling identities are
Mathlib's `Nat.fib_two_mul_add_one` and `Nat.fib_two_mul_add_two`, restated in
the book's form; `log` is `Nat.log 2` (floor), for which the book's
"logarithm law" steps `1 + log ((n–1)/2 + 1) = log (n+1)` (odd `n`) and
`1 + log (n/2) = log n ≤ log (n+1)` (even `n > 0`) hold exactly.
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

/-! ### The logarithmic solution -/

/-- `fib(2×k + 1) = (fib k)² + (fib(k+1))²`. -/
theorem fib_odd (k : ℕ) : Nat.fib (2 * k + 1) = Nat.fib k ^ 2 + Nat.fib (k + 1) ^ 2 := by
  rw [Nat.fib_two_mul_add_one]; ring

/-- `fib(2×k + 2) = 2 × fib k × fib(k+1) + (fib(k+1))²`. -/
theorem fib_even (k : ℕ) : Nat.fib (2 * k + 2) = 2 * Nat.fib k * Nat.fib (k + 1) + Nat.fib (k + 1) ^ 2 := by
  rw [Nat.fib_two_mul_add_two]; ring

/-- `b ⇒ S`. -/
def guard (b : FS → Prop) (S : Spec FS) : Spec FS := fun s s' => b s → S s s'

/-- `x′ = x² + y² ∧ y′ = 2×x×y + y²`. -/
def Sq₁ : Spec FS := fun s s' => s'.x = s.x ^ 2 + s.y ^ 2 ∧ s'.y = 2 * s.x * s.y + s.y ^ 2

/-- `x′ = 2×x×y + y² ∧ y′ = x² + y² + x′`. -/
def Sq₂ : Spec FS := fun s s' => s'.x = 2 * s.x * s.y + s.y ^ 2 ∧ s'.y = s.x ^ 2 + s.y ^ 2 + s'.x

/-- `P ⇐ if n=0 then x:= 0. y:= 1 else if even n then even n ∧ n>0 ⇒ P else odd n ⇒ P`. -/
theorem P_log :
    Refines P (cond (fun s => s.n = 0) (seq (assignX fun _ => 0) (assignY fun _ => 1))
      (cond (fun s => Even s.n) (guard (fun s => Even s.n ∧ 0 < s.n) P) (guard (fun s => Odd s.n) P))) := by
  rintro s s' (⟨hn, h⟩ | ⟨hn, (⟨he, h⟩ | ⟨he, h⟩)⟩)
  · rw [assignX_seq, assignY] at h
    subst h
    simp [P, hn]
  · exact h ⟨he, Nat.pos_of_ne_zero hn⟩
  · exact h (Nat.not_even_iff_odd.mp he)

/-- `odd n ⇒ P ⇐ n:= (n–1)/2. P. x′ = x² + y² ∧ y′ = 2×x×y + y²`. -/
theorem odd_refines : Refines (guard (fun s => Odd s.n) P) (seq (assignN fun s => (s.n - 1) / 2) (seq P Sq₁)) := by
  intro s s' h ho
  rw [assignN_seq] at h
  obtain ⟨u, ⟨hx, hy⟩, hsx, hsy⟩ := h
  obtain ⟨k, hk⟩ := ho
  simp only at hx hy
  have hk' : (s.n - 1) / 2 = k := by omega
  rw [hk'] at hx hy
  refine ⟨?_, ?_⟩
  · rw [hsx, hx, hy, hk, fib_odd]
  · rw [hsy, hx, hy, hk, show 2 * k + 1 + 1 = 2 * k + 2 by omega, fib_even]

/-- `even n ∧ n>0 ⇒ P ⇐ n:= n/2 – 1. P. x′ = 2×x×y + y² ∧ y′ = x² + y² + x′`: "we can get
`fib(2×k + 3)` as the sum of `fib(2×k + 1)` and `fib(2×k + 2)`". -/
theorem even_refines :
    Refines (guard (fun s => Even s.n ∧ 0 < s.n) P) (seq (assignN fun s => s.n / 2 - 1) (seq P Sq₂)) := by
  intro s s' h ⟨he, hpos⟩
  rw [assignN_seq] at h
  obtain ⟨u, ⟨hx, hy⟩, hsx, hsy⟩ := h
  obtain ⟨m, hm⟩ := he
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hn : s.n = 2 * k + 2 := by omega
  simp only at hx hy
  have hk' : s.n / 2 - 1 = k := by omega
  rw [hk'] at hx hy
  refine ⟨?_, ?_⟩
  · rw [hsx, hx, hy, hn, fib_even]
  · rw [hsy, hsx, hx, hy, hn, show 2 * k + 2 + 1 = (2 * k + 1) + 2 by omega, Nat.fib_add_two, fib_odd,
      show 2 * k + 1 + 1 = 2 * k + 2 by omega, fib_even]

/-- `x′ = x² + y² ∧ y′ = 2×x×y + y² ⇐ n:= x. x:= x² + y². y:= 2×n×y + y²`. -/
theorem sq₁_refines :
    Refines Sq₁ (seq (assignN fun s => s.x) (seq (assignX fun s => s.x ^ 2 + s.y ^ 2) (assignY fun s => 2 * s.n * s.y + s.y ^ 2))) := by
  intro s s' h
  rw [assignN_seq, assignX_seq, assignY] at h
  subst h
  exact ⟨rfl, rfl⟩

/-- `x′ = 2×x×y + y² ∧ y′ = x² + y² + x′ ⇐ n:= x. x:= 2×x×y + y². y:= n² + y² + x`. -/
theorem sq₂_refines :
    Refines Sq₂ (seq (assignN fun s => s.x) (seq (assignX fun s => 2 * s.x * s.y + s.y ^ 2) (assignY fun s => s.n ^ 2 + s.y ^ 2 + s.x))) := by
  intro s s' h
  rw [assignN_seq, assignX_seq, assignY] at h
  subst h
  exact ⟨rfl, rfl⟩

/-! ### Logarithmic time -/

/-- `T = t′ ≤ t + log (n+1)`. -/
def TLog : Spec FS := fun s s' => s'.t ≤ s.t + (Nat.log 2 (s.n + 1) : ℕ∞)

/-- `T ⇐ if n=0 then x:= 0. y:= 1 else if even n then even n ∧ n>0 ⇒ T else odd n ⇒ T`. -/
theorem tlog₁ :
    Refines TLog (cond (fun s => s.n = 0) (seq (assignX fun _ => 0) (assignY fun _ => 1))
      (cond (fun s => Even s.n) (guard (fun s => Even s.n ∧ 0 < s.n) TLog) (guard (fun s => Odd s.n) TLog))) := by
  rintro s s' (⟨hn, h⟩ | ⟨hn, (⟨he, h⟩ | ⟨he, h⟩)⟩)
  · rw [assignX_seq, assignY] at h
    subst h
    exact le_self_add
  · exact h ⟨he, Nat.pos_of_ne_zero hn⟩
  · exact h (Nat.not_even_iff_odd.mp he)

/-- `odd n ⇒ T ⇐ n:= (n–1)/2. t:= t+1. T. t′=t`: "`1 + log ((n–1)/2+1) ≤ log (n+1)`,
logarithm law ... `= log (n–1+2) ≤ log (n+1)`". -/
theorem tlog_odd : Refines (guard (fun s => Odd s.n) TLog) (seq (assignN fun s => (s.n - 1) / 2) (seq tick (seq TLog TS))) := by
  intro s s' h ho
  rw [assignN_seq, tick_seq] at h
  obtain ⟨u, hu, hs⟩ := h
  obtain ⟨k, hk⟩ := ho
  simp only [TLog] at hu ⊢
  rw [TS] at hs
  have hk' : (s.n - 1) / 2 + 1 = (s.n + 1) / 2 := by omega
  have hlog : Nat.log 2 ((s.n + 1) / 2) + 1 = Nat.log 2 (s.n + 1) := by
    rw [Nat.log_div_base]
    have := Nat.log_pos (b := 2) one_lt_two (show 2 ≤ s.n + 1 by omega)
    omega
  rw [hk', add_assoc, add_comm (1 : ℕ∞), ← Nat.cast_succ, Nat.succ_eq_add_one, hlog] at hu
  rw [hs]
  exact hu

/-- `even n ∧ n>0 ⇒ T ⇐ n:= n/2 – 1. t:= t+1. T. t′=t`: "`1 + log (n/2 – 1+1) ≤ log (n+1) =
log n ≤ log (n+1)`". -/
theorem tlog_even :
    Refines (guard (fun s => Even s.n ∧ 0 < s.n) TLog) (seq (assignN fun s => s.n / 2 - 1) (seq tick (seq TLog TS))) := by
  intro s s' h ⟨he, hpos⟩
  rw [assignN_seq, tick_seq] at h
  obtain ⟨u, hu, hs⟩ := h
  simp only [TLog] at hu ⊢
  rw [TS] at hs
  have h2 : 2 ≤ s.n := by obtain ⟨m, hm⟩ := he; omega
  have hk' : s.n / 2 - 1 + 1 = s.n / 2 := by omega
  have hlog : Nat.log 2 (s.n / 2) + 1 = Nat.log 2 s.n := by
    rw [Nat.log_div_base]
    have := Nat.log_pos (b := 2) one_lt_two h2
    omega
  rw [hk', add_assoc, add_comm (1 : ℕ∞), ← Nat.cast_succ, Nat.succ_eq_add_one, hlog] at hu
  rw [hs]
  exact le_trans hu (by gcongr; exact Nat.le_succ _)

/-- `t′=t ⇐ n:= x. x:= x² + y². y:= 2×n×y + y²`. -/
theorem sq₁_time :
    Refines TS (seq (assignN fun s => s.x) (seq (assignX fun s => s.x ^ 2 + s.y ^ 2) (assignY fun s => 2 * s.n * s.y + s.y ^ 2))) := by
  intro s s' h
  rw [assignN_seq, assignX_seq, assignY] at h
  subst h
  rfl

/-- `t′=t ⇐ n:= x. x:= 2×x×y + y². y:= n² + y² + x`. -/
theorem sq₂_time :
    Refines TS (seq (assignN fun s => s.x) (seq (assignX fun s => 2 * s.x * s.y + s.y ^ 2) (assignY fun s => s.n ^ 2 + s.y ^ 2 + s.x))) := by
  intro s s' h
  rw [assignN_seq, assignX_seq, assignY] at h
  subst h
  rfl

end Fibonacci

end LaPToP.ProgramTheory
