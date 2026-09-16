import LaPToP.ProgramTheory.ExitLoop
import LaPToP.ProgramTheory.Time
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Two-dimensional search

This module formalizes Section 5.2.2 (Two-Dimensional Search) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), Exercise 191.

"Write a program to find a given item in a given 2-dimensional array. The
execution time must be linear in the product of the dimensions. Let the array
be `A`, let its dimensions be `n` by `m`, and let the item we seek be `x`. We
will indicate the position of `x` in `A` by the final values of natural
variables `i` and `j`. If `x` occurs more than once, any of its positions will
do. If it does not occur, we will indicate that by `i′=n`. The problem, except
for time, is `P`:

    P = if x: A (0,..n) (0,..m) then x = A i′ j′ else i′=n
    Q = if x: A (i,..n) (0,..m) then x = A i′ j′ else i′=n
    R = if x: A i (j,..m), A (i+1,..n) (0,..m) then x = A i′ j′ else i′=n

We now solve the problem in five easy pieces.

    P             ⇐ i:= 0. i≤n ⇒ Q
    i≤n ⇒ Q       ⇐ if i=n then ok else i<n ⇒ Q
    i<n ⇒ Q       ⇐ j:= 0. i<n ∧ j≤m ⇒ R
    i<n ∧ j≤m ⇒ R ⇐ if j=m then i:= i+1. i≤n ⇒ Q else i<n ∧ j<m ⇒ R
    i<n ∧ j<m ⇒ R ⇐ if A i j = x then ok else j:= j+1. i<n ∧ j≤m ⇒ R"

## The model

The array is a function `A : ℕ → ℕ → α`; the state has the natural variables
`i`, `j` and the time `t : ℕ∞`. The bunch membership `x: A (i,..n) (0,..m)`
is the predicate "some `A a b = x` with `i ≤ a < n` and `b < m`", and
`x: A i (j,..m), A (i+1,..n) (0,..m)` likewise. The five refinements are
proved as stated, and the compiler's view `P ⇐ i:= 0. L0`,
`L0 ⇐ if i=n then ok else j:= 0. L1`, `L1 ⇐ if j=m then i:= i+1. L0 else if A i j = x
then ok else j:= j+1. L1` is derived by Refinement by Steps.

## Timing — a correction to the book

"To add recursive time, ... we can get away with a single time increment
placed just before the test `j=m`. ... The time remaining is at most the area
remaining to be searched." The book then refines with the bounds
`t′ ≤ t + n×m`, `i≤n ⇒ t′ ≤ t + (n–i)×m`, `i<n ∧ j≤m ⇒ t′ ≤ t + (n–i)×m – j`
(before and after the increment). With one increment per iteration of `L1`,
each row costs `m+1` increments (the tests `j = 0, …, m`), so the total is
`n×(m+1)`, not `n×m`: for `n = 1`, `m = 0` and `x` absent the program takes
one increment while the book's bound allows none. The book's fourth timed
refinement is false in both branches (`book_timed_R_fails` gives the
counterexample). The corrected bounds are proved:
`t′ ≤ t + n×(m+1)`, `i≤n ⇒ t′ ≤ t + (n–i)×(m+1)`,
`i<n ∧ j≤m ⇒ t′ ≤ t + (n–i)×(m+1) – j` before the increment and
`i<n ∧ j<m ⇒ t′ ≤ t + (n–i)×(m+1) – j – 1` after it. The execution time is
still linear in the product of the dimensions.
-/

namespace LaPToP.ProgramTheory

universe u

namespace TwoDimSearch

open Spec

/-- The state: natural variables `i`, `j` and the time `t`. -/
structure S2 where
  /-- The time variable. -/
  t : ℕ∞
  /-- The row index `i`. -/
  i : ℕ
  /-- The column index `j`. -/
  j : ℕ

/-- `i:= e`. -/
def assignI (e : S2 → ℕ) : Spec S2 := fun s s' => s' = { s with i := e s }

/-- `j:= e`. -/
def assignJ (e : S2 → ℕ) : Spec S2 := fun s s' => s' = { s with j := e s }

/-- `t:= t+1`. -/
def tick : Spec S2 := fun s s' => s' = { s with t := s.t + 1 }

theorem assignI_seq (e : S2 → ℕ) (P : Spec S2) : seq (assignI e) P = fun s s' => P { s with i := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

theorem assignJ_seq (e : S2 → ℕ) (P : Spec S2) : seq (assignJ e) P = fun s s' => P { s with j := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

theorem tick_seq (P : Spec S2) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- `b ⇒ S`, a specification guarded by a condition on the initial state. -/
def guard (b : S2 → Prop) (S : Spec S2) : Spec S2 := fun s s' => b s → S s s'

variable {α : Type u} (A : ℕ → ℕ → α) (n m : ℕ) (x : α)

/-- `x: A (i,..n) (0,..m)`: `x` occurs in rows `i,..n`. -/
def memRows (i : ℕ) : Prop := ∃ a b, i ≤ a ∧ a < n ∧ b < m ∧ A a b = x

/-- `x: A i (j,..m), A (i+1,..n) (0,..m)`: `x` occurs in row `i` from column `j`,
or in a later row. -/
def memFrom (i j : ℕ) : Prop := (∃ b, j ≤ b ∧ b < m ∧ A i b = x) ∨ memRows A n m x (i + 1)

/-- `x = A i′ j′`. -/
def found : Spec S2 := fun _ s' => A s'.i s'.j = x

/-- `i′=n`. -/
def notFound : Spec S2 := fun _ s' => s'.i = n

/-- `P = if x: A (0,..n) (0,..m) then x = A i′ j′ else i′=n`. -/
def P : Spec S2 := cond (fun _ => memRows A n m x 0) (found A x) (notFound n)

/-- `Q = if x: A (i,..n) (0,..m) then x = A i′ j′ else i′=n`. -/
def Q : Spec S2 := cond (fun s => memRows A n m x s.i) (found A x) (notFound n)

/-- `R = if x: A i (j,..m), A (i+1,..n) (0,..m) then x = A i′ j′ else i′=n`. -/
def R : Spec S2 := cond (fun s => memFrom A n m x s.i s.j) (found A x) (notFound n)

/-- No row from `n` on: `x: A (n,..n) (0,..m)` is `⊥`. -/
theorem not_memRows_self : ¬ memRows A n m x n := by
  rintro ⟨a, b, h1, h2, -, -⟩
  omega

/-- `x: A i (0,..m), A (i+1,..n) (0,..m) = x: A (i,..n) (0,..m)` for `i < n`. -/
theorem memFrom_zero {i : ℕ} (hi : i < n) : memFrom A n m x i 0 ↔ memRows A n m x i := by
  constructor
  · rintro (⟨b, -, hb, hx⟩ | ⟨a, b, h1, h2, hb, hx⟩)
    · exact ⟨i, b, le_rfl, hi, hb, hx⟩
    · exact ⟨a, b, by omega, h2, hb, hx⟩
  · rintro ⟨a, b, h1, h2, hb, hx⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact Or.inl ⟨b, Nat.zero_le _, hb, hx⟩
    · exact Or.inr ⟨a, b, hlt, h2, hb, hx⟩

/-- `x: A i (m,..m), A (i+1,..n) (0,..m) = x: A (i+1,..n) (0,..m)`. -/
theorem memFrom_m (i : ℕ) : memFrom A n m x i m ↔ memRows A n m x (i + 1) := by
  constructor
  · rintro (⟨b, h1, h2, -⟩ | h)
    · omega
    · exact h
  · exact Or.inr

/-- Removing an item that is not `x` does not change membership. -/
theorem memFrom_succ {i j : ℕ} (hx : A i j ≠ x) : memFrom A n m x i (j + 1) ↔ memFrom A n m x i j := by
  constructor
  · rintro (⟨b, h1, h2, h3⟩ | h)
    · exact Or.inl ⟨b, by omega, h2, h3⟩
    · exact Or.inr h
  · rintro (⟨b, h1, h2, h3⟩ | h)
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact absurd h3 hx
      · exact Or.inl ⟨b, hlt, h2, h3⟩
    · exact Or.inr h

/-! ### The five easy pieces -/

/-- `P ⇐ i:= 0. i≤n ⇒ Q`. -/
theorem refine₁ : Refines (P A n m x) (seq (assignI fun _ => 0) (guard (fun s => s.i ≤ n) (Q A n m x))) := by
  intro s s' h
  rw [assignI_seq] at h
  exact h (Nat.zero_le n)

/-- `i≤n ⇒ Q ⇐ if i=n then ok else i<n ⇒ Q`. -/
theorem refine₂ :
    Refines (guard (fun s => s.i ≤ n) (Q A n m x))
      (cond (fun s => s.i = n) ok (guard (fun s => s.i < n) (Q A n m x))) := by
  rintro s s' (⟨hi, rfl⟩ | ⟨hi, h⟩) hle
  · exact Or.inr ⟨hi ▸ not_memRows_self A n m x, hi⟩
  · exact h (lt_of_le_of_ne hle hi)

/-- `i<n ⇒ Q ⇐ j:= 0. i<n ∧ j≤m ⇒ R`. -/
theorem refine₃ :
    Refines (guard (fun s => s.i < n) (Q A n m x))
      (seq (assignJ fun _ => 0) (guard (fun s => s.i < n ∧ s.j ≤ m) (R A n m x))) := by
  intro s s' h hi
  rw [assignJ_seq] at h
  have h' := h ⟨hi, Nat.zero_le m⟩
  simp only [R, Q, Spec.cond, memFrom_zero A n m x hi] at h' ⊢
  exact h'

/-- `i<n ∧ j≤m ⇒ R ⇐ if j=m then i:= i+1. i≤n ⇒ Q else i<n ∧ j<m ⇒ R`. -/
theorem refine₄ :
    Refines (guard (fun s => s.i < n ∧ s.j ≤ m) (R A n m x))
      (cond (fun s => s.j = m)
        (seq (assignI fun s => s.i + 1) (guard (fun s => s.i ≤ n) (Q A n m x)))
        (guard (fun s => s.i < n ∧ s.j < m) (R A n m x))) := by
  rintro s s' (⟨hj, h⟩ | ⟨hj, h⟩) ⟨hi, hjm⟩
  · rw [assignI_seq] at h
    have h' := h (by simp only; omega)
    simp only [R, Q, Spec.cond, hj, memFrom_m] at h' ⊢
    exact h'
  · exact h ⟨hi, lt_of_le_of_ne hjm hj⟩

/-- `i<n ∧ j<m ⇒ R ⇐ if A i j = x then ok else j:= j+1. i<n ∧ j≤m ⇒ R`. -/
theorem refine₅ :
    Refines (guard (fun s => s.i < n ∧ s.j < m) (R A n m x))
      (cond (fun s => A s.i s.j = x) ok
        (seq (assignJ fun s => s.j + 1) (guard (fun s => s.i < n ∧ s.j ≤ m) (R A n m x)))) := by
  rintro s s' (⟨hx, rfl⟩ | ⟨hx, h⟩) ⟨hi, hj⟩
  · exact Or.inl ⟨Or.inl ⟨_, le_rfl, hj, hx⟩, hx⟩
  · rw [assignJ_seq] at h
    have h' := h ⟨hi, by simp only; omega⟩
    simp only [R, Spec.cond, memFrom_succ A n m x hx] at h' ⊢
    exact h'

/-! ### The compiler's view: `L0`, `L1` -/

/-- `L0 = (i≤n ⇒ Q)`. -/
def L0 : Spec S2 := guard (fun s => s.i ≤ n) (Q A n m x)

/-- `L1 = (i<n ∧ j≤m ⇒ R)`. -/
def L1 : Spec S2 := guard (fun s => s.i < n ∧ s.j ≤ m) (R A n m x)

/-- `P ⇐ i:= 0. L0`. -/
theorem compiled₀ : Refines (P A n m x) (seq (assignI fun _ => 0) (L0 A n m x)) := refine₁ A n m x

/-- `L0 ⇐ if i=n then ok else j:= 0. L1` (Refinement by Steps). -/
theorem compiled₁ : Refines (L0 A n m x) (cond (fun s => s.i = n) ok (seq (assignJ fun _ => 0) (L1 A n m x))) :=
  steps_cond _ (refine₂ A n m x) (refines_refl _) (refine₃ A n m x)

/-- `L1 ⇐ if j=m then i:= i+1. L0 else if A i j = x then ok else j:= j+1. L1`. -/
theorem compiled₂ :
    Refines (L1 A n m x)
      (cond (fun s => s.j = m) (seq (assignI fun s => s.i + 1) (L0 A n m x))
        (cond (fun s => A s.i s.j = x) ok (seq (assignJ fun s => s.j + 1) (L1 A n m x)))) :=
  steps_cond _ (refine₄ A n m x) (refines_refl _) (refine₅ A n m x)

/-! ### Timing -/

/-- `t′ ≤ t + k`, for a natural bound `k`. -/
def within (k : S2 → ℕ) : Spec S2 := fun s s' => s'.t ≤ s.t + (k s : ℕ∞)

theorem within_mono {k k' : S2 → ℕ} (h : ∀ s, k s ≤ k' s) : Refines (within k') (within k) :=
  fun s _ hs => le_trans hs (by gcongr; exact h s)

/-- The book's bound before the increment, `i<n ∧ j≤m ⇒ t′ ≤ t + (n–i)×m – j`. -/
def bookTR : Spec S2 := guard (fun s => s.i < n ∧ s.j ≤ m) (within fun s => (n - s.i) * m - s.j)

/-- The book's bound `i≤n ⇒ t′ ≤ t + (n–i)×m`. -/
def bookTQ : Spec S2 := guard (fun s => s.i ≤ n) (within fun s => (n - s.i) * m)

/-- The book's fourth timed refinement
`i<n ∧ j≤m ⇒ t′ ≤ t + (n–i)×m – j ⇐ t:= t+1. if j=m then i:= i+1. i≤n ⇒ t′ ≤ t + (n–i)×m else …`
is false: with `n = 1`, `m = 0`, from `i = j = 0` the right side takes one time
unit but the left side allows none. -/
theorem book_timed_R_fails :
    ¬ Refines (bookTR 1 0)
      (seq tick (cond (fun s => s.j = 0)
        (seq (assignI fun s => s.i + 1) (bookTQ 1 0))
        (guard (fun s => s.i < 1 ∧ s.j < 0) (within fun s => (1 - s.i) * 0 - s.j)))) := by
  intro h
  have := h ⟨0, 0, 0⟩ ⟨1, 1, 0⟩ ⟨⟨1, 0, 0⟩, rfl, Or.inl ⟨rfl, ⟨1, 1, 0⟩, rfl, fun _ => by simp [within]⟩⟩
    ⟨Nat.zero_lt_one, le_rfl⟩
  simp [within] at this

/-- The corrected bound before the increment: `i<n ∧ j≤m ⇒ t′ ≤ t + (n–i)×(m+1) – j`. -/
def TR : Spec S2 := guard (fun s => s.i < n ∧ s.j ≤ m) (within fun s => (n - s.i) * (m + 1) - s.j)

/-- The corrected bound after the increment: `i<n ∧ j<m ⇒ t′ ≤ t + (n–i)×(m+1) – j – 1`. -/
def TR' : Spec S2 := guard (fun s => s.i < n ∧ s.j < m) (within fun s => (n - s.i) * (m + 1) - s.j - 1)

/-- `i≤n ⇒ t′ ≤ t + (n–i)×(m+1)`. -/
def TQ : Spec S2 := guard (fun s => s.i ≤ n) (within fun s => (n - s.i) * (m + 1))

/-- `i<n ⇒ t′ ≤ t + (n–i)×(m+1)`. -/
def TQ' : Spec S2 := guard (fun s => s.i < n) (within fun s => (n - s.i) * (m + 1))

/-- `t′ ≤ t + n×(m+1) ⇐ i:= 0. i≤n ⇒ t′ ≤ t + (n–i)×(m+1)`. -/
theorem timed₁ : Refines (within fun _ => n * (m + 1)) (seq (assignI fun _ => 0) (TQ n m)) := by
  intro s s' h
  rw [assignI_seq] at h
  simpa [within] using h (Nat.zero_le n)

/-- `i≤n ⇒ t′ ≤ t + (n–i)×(m+1) ⇐ if i=n then ok else i<n ⇒ t′ ≤ t + (n–i)×(m+1)`. -/
theorem timed₂ : Refines (TQ n m) (cond (fun s => s.i = n) ok (TQ' n m)) := by
  rintro s s' (⟨-, rfl⟩ | ⟨hi, h⟩) hle
  · exact le_self_add
  · exact h (lt_of_le_of_ne hle hi)

/-- `i<n ⇒ t′ ≤ t + (n–i)×(m+1) ⇐ j:= 0. i<n ∧ j≤m ⇒ t′ ≤ t + (n–i)×(m+1) – j`. -/
theorem timed₃ : Refines (TQ' n m) (seq (assignJ fun _ => 0) (TR n m)) := by
  intro s s' h hi
  rw [assignJ_seq] at h
  simpa [within] using h ⟨hi, Nat.zero_le m⟩

/-- `t + 1 + a = t + b` in `ℕ∞` when `1 + a = b`. -/
theorem add_one_add_cast (t : ℕ∞) {a b : ℕ} (h : 1 + a = b) : t + 1 + (a : ℕ∞) = t + (b : ℕ∞) := by
  rw [← h, Nat.cast_add, Nat.cast_one, add_assoc]

/-- `i<n ∧ j≤m ⇒ t′ ≤ t + (n–i)×(m+1) – j ⇐ t:= t+1. if j=m then i:= i+1. i≤n ⇒ t′ ≤ t + (n–i)×(m+1)
else i<n ∧ j<m ⇒ t′ ≤ t + (n–i)×(m+1) – j – 1` — the corrected fourth piece. -/
theorem timed₄ :
    Refines (TR n m)
      (seq tick (cond (fun s => s.j = m) (seq (assignI fun s => s.i + 1) (TQ n m)) (TR' n m))) := by
  intro s s' h ⟨hi, hj⟩
  rw [tick_seq] at h
  rcases h with ⟨hjm, h⟩ | ⟨hjm, h⟩
  · rw [assignI_seq] at h
    have h' := h (by simp only; omega)
    simp only [within] at h' ⊢
    refine le_trans h' (le_of_eq ?_)
    simp only at hjm
    rw [add_one_add_cast]
    rw [hjm]
    have : n - s.i = (n - (s.i + 1)) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
    generalize (n - (s.i + 1)) * (m + 1) = X
    omega
  · have h' := h ⟨hi, lt_of_le_of_ne hj hjm⟩
    simp only [within] at h' ⊢
    refine le_trans h' (le_of_eq ?_)
    rw [add_one_add_cast]
    have hlt : s.j < m := lt_of_le_of_ne hj hjm
    have h1 : 1 ≤ n - s.i := by omega
    have : m + 1 ≤ (n - s.i) * (m + 1) := Nat.le_mul_of_pos_left _ h1
    generalize (n - s.i) * (m + 1) = X at *
    omega

/-- `i<n ∧ j<m ⇒ t′ ≤ t + (n–i)×(m+1) – j – 1 ⇐ if A i j = x then ok else j:= j+1. i<n ∧ j≤m ⇒ t′ ≤ t + (n–i)×(m+1) – j`. -/
theorem timed₅ :
    Refines (TR' n m)
      (cond (fun s => A s.i s.j = x) ok (seq (assignJ fun s => s.j + 1) (TR n m))) := by
  rintro s s' (⟨-, rfl⟩ | ⟨-, h⟩) ⟨hi, hj⟩
  · exact le_self_add
  · rw [assignJ_seq] at h
    have h' := h ⟨hi, by simp only; omega⟩
    simp only [within] at h' ⊢
    refine le_trans h' (le_of_eq ?_)
    congr 1

end TwoDimSearch

end LaPToP.ProgramTheory
