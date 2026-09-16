import LaPToP.ProgramTheory.Assertions
import LaPToP.FunctionTheory.Functions

/-!
# Data structures: arrays and records

This module formalizes Section 5.1 (Data Structures) of Eric Hehner's *A
Practical Theory of Programming* (aPToP): array element assignment (§5.1.0)
and records (§5.1.1).

"Let `A` be an array name, let `i` be any expression of the index type, and
let `e` be any expression of the element type. Then
`A i:= e = A′i=e ∧ (∀j· j⧧i ⇒ A′j = A j) ∧ x′=x ∧ y′=y ∧ ...` ... The
Substitution Law `x:= e. P = (for x substitute e in P)` is very useful, but
unfortunately it does not work for array element assignment. For example,
`A 2:= 3. i:= 2. A i:= 4. A i = A 2` should equal `⊤` ... If we try to apply the
Substitution Law, we get ... `A 2:= 3. 4 = A 2`. Here is a second example ...
`A 2:= 2. A(A 2):= 3. A 2 = 2` This should equal `⊥` because `A 2 = 3` just
before the final binary expression. But the Substitution Law says ...
`A 2:= 2. A 2 = 2`. The Substitution Law works only when the assignment has a
simple name to the left of `:=`. Fortunately we can always rewrite an array
element assignment in that form. `A i:= e = A′ = i→e | A ∧ x′=x ∧ y′=y ∧ ... =
A:= i→e | A`. ... The only thing to remember about array element assignment
is this: change `A i:= e` to `A:= i→e | A` before applying any programming
theory. A two-dimensional array element assignment `A i j:= e` must be changed
to `A:= (i; j)→e | A`, and similarly for more dimensions. In program theory,
an array is a list variable, and array element assignment assigns the list
variable to a new list that is like the old list but differs in one item."

"Without inventing anything new, we can already build records ... `person =
“name” → text | “age” → nat` ... a component (or field) is assigned the same
way we make an array element assignment. ... `p “age”:= 18` ... Just as for
array element assignment, the Substitution Law does not work for record
components. And the solution is also the same; just rewrite it like this:
`p:= “age” → 18 | p`. No new theory is needed for records."

## The model

An array is a function `ℕ → ℤ` ("an array is a list variable"); the state has
the array `A`, an index variable `i` and another variable `x`. Element
assignment `A i:= e` is defined literally as the book's binary expression, and
proved equal to the whole-array assignment `A:= i→e | A`, where `i→e | A` is
`Function.update A i e` (and is shown to agree with the selective union
`Fn.orElse (Fn.arrow i e) A` of Function Theory). The two examples are made
precise: `A 2:= 3. i:= 2. A i:= 4. A i = A 2` is the assignments (the final
test holds, `⊤`), whereas the naively substituted `A 2:= 3. 4 = A 2` is `⊥`;
`A 2:= 2. A(A 2):= 3. A 2 = 2` is `⊥`, whereas the naively substituted
`A 2:= 2. A 2 = 2` is `A 2:= 2`, not `⊥`. The corrected calculations with
`A:= i→e | A` go through the Substitution Law for the whole-array assignment.
Two-dimensional arrays and records are the same construction (a definitional
lemma each).
-/

namespace LaPToP.ProgramTheory

namespace Arrays

open Spec LaPToP.FunctionTheory

/-- The state: an array `A`, an index variable `i` and another variable `x`. -/
structure AS where
  /-- The array, "a list variable". -/
  A : ℕ → ℤ
  /-- An index variable. -/
  i : ℕ
  /-- Another variable. -/
  x : ℤ

/-- `A i:= e = A′i=e ∧ (∀j· j⧧i ⇒ A′j = A j) ∧ x′=x ∧ y′=y ∧ ...`, the book's definition
of array element assignment (`i` and `e` any expressions of the initial state). -/
def assignElem (idx : AS → ℕ) (e : AS → ℤ) : Spec AS := fun s s' =>
  s'.A (idx s) = e s ∧ (∀ j, j ≠ idx s → s'.A j = s.A j) ∧ s'.i = s.i ∧ s'.x = s.x

/-- `A:= f`, assignment to the array as a whole — "a simple name to the left of `:=`". -/
def assignA (f : AS → ℕ → ℤ) : Spec AS := fun s s' => s' = { s with A := f s }

/-- `i:= e`. -/
def assignI (e : AS → ℕ) : Spec AS := fun s s' => s' = { s with i := e s }

theorem assignA_seq (f : AS → ℕ → ℤ) (P : Spec AS) : seq (assignA f) P = fun s s' => P { s with A := f s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

theorem assignI_seq (e : AS → ℕ) (P : Spec AS) : seq (assignI e) P = fun s s' => P { s with i := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- `A i:= e = A:= i→e | A`: element assignment is whole-array assignment of the
array "like the old list but differs in one item". -/
theorem assignElem_eq_assignA (idx : AS → ℕ) (e : AS → ℤ) :
    assignElem idx e = assignA fun s => Function.update s.A (idx s) (e s) := by
  refine Spec.ext fun s s' => ?_
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨A', i', x'⟩ := s'
    simp only at h1 h2 h3 h4
    subst h3 h4
    simp only [assignA, AS.mk.injEq, and_true]
    funext j
    by_cases hj : j = idx s
    · subst hj; rw [Function.update_self]; exact h1
    · rw [Function.update_of_ne hj]; exact h2 j hj
  · rintro rfl
    refine ⟨Function.update_self .., fun j hj => Function.update_of_ne hj .., rfl, rfl⟩

/-- `i→e | A` of Function Theory agrees with `Function.update A i e` at every index. -/
theorem orElse_arrow_apply (A : ℕ → ℤ) (i : ℕ) (e : ℤ) (j : ℕ)
    (hj : j ∈ (Fn.orElse (Fn.arrow i e) (Fn.lam Set.univ A)).domain) :
    (Fn.orElse (Fn.arrow i e) (Fn.lam Set.univ A)).apply j hj = Function.update A i e j := by
  have hmem : j ∈ (Fn.arrow i e).domain ↔ j = i := Set.mem_singleton_iff
  rw [Fn.apply_orElse]
  by_cases h : j = i
  · subst h
    rw [dif_pos (hmem.mpr rfl), Function.update_self]
    rfl
  · rw [dif_neg (fun h' => h (hmem.mp h')), Function.update_of_ne h]
    rfl

/-! ### The Substitution Law fails for array elements -/

/-- The first example, `A 2:= 3. i:= 2. A i:= 4. A i = A 2`: the final test always
holds, so the program equals its three assignments. -/
theorem example₁ :
    seq (assignElem (fun _ => 2) fun _ => 3) (seq (assignI fun _ => 2) (seq (assignElem (fun s => s.i) fun _ => 4)
      (ensure fun s => s.A s.i = s.A 2))) =
    seq (assignElem (fun _ => 2) fun _ => 3) (seq (assignI fun _ => 2) (assignElem (fun s => s.i) fun _ => 4)) := by
  simp only [assignElem_eq_assignA, assignA_seq, assignI_seq]
  refine Spec.ext fun s s' => ?_
  simp only [ensure, Spec.and, Spec.ok, assignA, Function.update_self, true_and]

/-- The naive substitution `A 2:= 3. 4 = A 2` is `⊥`: after `A 2:= 3`, `A 2 = 3 ≠ 4`. -/
theorem example₁_naive : seq (assignElem (fun _ => 2) fun _ => 3) (ensure fun s => 4 = s.A 2) = bot := by
  simp only [assignElem_eq_assignA, assignA_seq]
  refine Spec.ext fun s s' => ?_
  simp [ensure, Spec.and, Spec.ok, bot]

/-- The second example, `A 2:= 2. A(A 2):= 3. A 2 = 2`, "should equal `⊥` because
`A 2 = 3` just before the final binary expression". -/
theorem example₂ :
    seq (assignElem (fun _ => 2) fun _ => 2) (seq (assignElem (fun s => (s.A 2).toNat) fun _ => 3)
      (ensure fun s => s.A 2 = 2)) = bot := by
  simp only [assignElem_eq_assignA, assignA_seq]
  refine Spec.ext fun s s' => ?_
  simp [ensure, Spec.and, Spec.ok, bot]

/-- The naive substitution `A 2:= 2. A 2 = 2` is not `⊥` — it is `A 2:= 2`. -/
theorem example₂_naive :
    seq (assignElem (fun _ => 2) fun _ => 2) (ensure fun s => s.A 2 = 2) = assignElem (fun _ => 2) fun _ => 2 := by
  simp only [assignElem_eq_assignA, assignA_seq]
  refine Spec.ext fun s s' => ?_
  simp [ensure, Spec.and, Spec.ok, assignA]

/-! ### Two-dimensional arrays and records -/

/-- A two-dimensional array with two index variables. -/
structure AS2 where
  /-- The array. -/
  A : ℕ → ℕ → ℤ
  /-- Index variables. -/
  i : ℕ
  /-- Index variables. -/
  j : ℕ

/-- `A i j:= e = A′i j = e ∧ (∀k, l· (k; l) ⧧ (i; j) ⇒ A′k l = A k l) ∧ i′=i ∧ j′=j`. -/
def assignElem2 (e : AS2 → ℤ) : Spec AS2 := fun s s' =>
  s'.A s.i s.j = e s ∧ (∀ k l, (k, l) ≠ (s.i, s.j) → s'.A k l = s.A k l) ∧ s'.i = s.i ∧ s'.j = s.j

/-- `A i j:= e = A:= (i; j)→e | A`. -/
theorem assignElem2_eq (e : AS2 → ℤ) :
    assignElem2 e = fun s s' => s' = { s with A := Function.update s.A s.i (Function.update (s.A s.i) s.j (e s)) } := by
  refine Spec.ext fun s s' => ?_
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨A', i', j'⟩ := s'
    simp only at h1 h2 h3 h4
    subst h3 h4
    simp only [AS2.mk.injEq, and_true]
    funext k l
    by_cases hk : k = s.i
    · subst hk
      rw [Function.update_self]
      by_cases hl : l = s.j
      · subst hl; rw [Function.update_self]; exact h1
      · rw [Function.update_of_ne hl]; exact h2 _ _ (by simp [hl])
    · rw [Function.update_of_ne hk]; exact h2 _ _ (by simp [hk])
  · rintro rfl
    refine ⟨by simp, fun k l hkl => ?_, rfl, rfl⟩
    by_cases hk : k = s.i
    · subst hk
      have hl : l ≠ s.j := fun h => hkl (by rw [h])
      simp [Function.update_of_ne hl]
    · simp [Function.update_of_ne hk]

/-- `person = “name” → text | “age” → nat`. -/
structure Person where
  /-- The field `“name”`. -/
  name : String
  /-- The field `“age”`. -/
  age : ℕ

/-- The state with a record variable `p`. -/
structure RS where
  /-- The record variable `p`. -/
  p : Person

/-- `p “age”:= 18`, component assignment as the book defines element assignment:
the component gets the value, the other components and variables are unchanged. -/
def assignAge (e : RS → ℕ) : Spec RS := fun s s' => s'.p.age = e s ∧ s'.p.name = s.p.name

/-- `p “age”:= 18 = p:= “age” → 18 | p`: "no new theory is needed for records". -/
theorem assignAge_eq (e : RS → ℕ) : assignAge e = fun s s' => s' = ⟨{ s.p with age := e s }⟩ := by
  refine Spec.ext fun s s' => ?_
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨⟨name, age⟩⟩ := s'
    simp only at h1 h2
    subst h1 h2
    rfl
  · rintro rfl
    exact ⟨rfl, rfl⟩

end Arrays

end LaPToP.ProgramTheory
