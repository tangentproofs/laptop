import Mathlib.Order.MinMax
import Mathlib.Order.Basic

/-!
# Generic laws

This module formalizes the Generic table of the Reference chapter (Section
11.3.0) of Eric Hehner's *A Practical Theory of Programming* (aPToP), p. 235.

"The operators `= ⧧ if then else` apply to every type of expression (but the
first operand of `if then else` must be binary), with the laws `x=x`
Reflexivity, `x=y = y=x` Symmetry, `x=y ∧ y=z ⇒ x=z` Transitivity,
`x=y ⇒ f x = f y` Transparency, `x⧧y = ¬(x=y)` Unequality,
`if ⊤ then x else y = x` and `if ⊥ then x else y = y` Case Base,
`if a then x else x = x` Case Idempotent,
`if a then x else y = if ¬a then y else x` Case Reversal.
The operators `↑ ↓ < ≤ > ≥` apply to numbers, characters, strings, and lists,
with the laws" — the order and minimum/maximum laws below.

## The model

The `=`/`if` laws are stated for an arbitrary type, with a `Decidable`
condition for `if` (the book's "binary" first operand). The order laws are
stated for an arbitrary `LinearOrder`: this covers the numbers of this
formalization (`ℤ`, `ℕ`, `ℚ`, `ℝ`, `ℕ∞`, the extended integers), and
characters; the book's lexicographic order on strings and lists is the `LT`
instance of `Str`/`HList` (`List.lt`), for which no `LinearOrder` instance is
declared here, so those instances of the laws are not asserted. `↑` and `↓` are
`max` and `min`.
-/

namespace LaPToP.BasicTheories

namespace Generic

universe u v

section Equality

variable {α : Sort u} {β : Sort v} (x y z : α) (f : α → β)

/-- `x=x` Reflexivity. -/
theorem eq_refl' : x = x := rfl

/-- `x=y = y=x` Symmetry. -/
theorem eq_symm_iff : (x = y) ↔ (y = x) := eq_comm

/-- `x=y ∧ y=z ⇒ x=z` Transitivity. -/
theorem eq_trans_of : x = y ∧ y = z → x = z := fun ⟨h₁, h₂⟩ => h₁.trans h₂

/-- `x=y ⇒ f x = f y` Transparency. -/
theorem transparency : x = y → f x = f y := fun h => h ▸ rfl

/-- `x⧧y = ¬(x=y)` Unequality. -/
theorem ne_iff_not_eq : x ≠ y ↔ ¬ (x = y) := Iff.rfl

end Equality

section Case

variable {α : Sort u} (x y : α)

/-- `if ⊤ then x else y = x` Case Base. -/
theorem ite_true_base : (if True then x else y) = x := if_pos trivial

/-- `if ⊥ then x else y = y` Case Base. -/
theorem ite_false_base : (if False then x else y) = y := if_neg id

variable (a : Prop) [Decidable a]

/-- `if a then x else x = x` Case Idempotent. -/
theorem ite_idem : (if a then x else x) = x := ite_self x

/-- `if a then x else y = if ¬a then y else x` Case Reversal. -/
theorem ite_reversal : (if a then x else y) = if ¬ a then y else x := (ite_not a y x).symm

end Case

section Order

variable {α : Type u} [LinearOrder α] (x y z : α)

/-- `x≤y = x = x↓y`. -/
theorem le_iff_eq_min : x ≤ y ↔ x = min x y := (min_eq_left_iff).symm.trans eq_comm

/-- `x↓y ≤ x ≤ x↑y`. -/
theorem min_le_self_le_max : min x y ≤ x ∧ x ≤ max x y := ⟨min_le_left x y, le_max_left x y⟩

/-- `x≤y = y = x↑y`. -/
theorem le_iff_eq_max : x ≤ y ↔ y = max x y := (max_eq_right_iff).symm.trans eq_comm

/-- `x≤x` Reflexivity. -/
theorem le_refl' : x ≤ x := le_refl x

/-- `¬ x<x` Irreflexivity. -/
theorem not_lt_self : ¬ x < x := lt_irrefl x

/-- `¬(x<y ∧ x=y)` Exclusivity. -/
theorem not_lt_and_eq : ¬ (x < y ∧ x = y) := fun ⟨h, e⟩ => h.ne e

/-- `¬(x>y ∧ x=y)` Exclusivity. -/
theorem not_gt_and_eq : ¬ (x > y ∧ x = y) := fun ⟨h, e⟩ => h.ne e.symm

/-- `¬(x<y ∧ x>y)` Exclusivity. -/
theorem not_lt_and_gt : ¬ (x < y ∧ x > y) := fun ⟨h₁, h₂⟩ => lt_asymm h₁ h₂

/-- `x≤y = x<y ∨ x=y` Inclusivity. -/
theorem le_iff_lt_or_eq' : x ≤ y ↔ x < y ∨ x = y := le_iff_lt_or_eq

/-- `x≤y ∧ y≤z ⇒ x≤z` Transitivity. -/
theorem le_le_trans : x ≤ y ∧ y ≤ z → x ≤ z := fun ⟨h₁, h₂⟩ => h₁.trans h₂

/-- `x<y ∧ y≤z ⇒ x<z` Transitivity. -/
theorem lt_le_trans : x < y ∧ y ≤ z → x < z := fun ⟨h₁, h₂⟩ => h₁.trans_le h₂

/-- `x<y ∧ y<z ⇒ x<z` Transitivity. -/
theorem lt_lt_trans : x < y ∧ y < z → x < z := fun ⟨h₁, h₂⟩ => h₁.trans h₂

/-- `x≤y ∧ y<z ⇒ x<z` Transitivity. -/
theorem le_lt_trans : x ≤ y ∧ y < z → x < z := fun ⟨h₁, h₂⟩ => h₁.trans_lt h₂

/-- `x>y = y<x` Mirror. -/
theorem gt_iff_lt' : x > y ↔ y < x := Iff.rfl

/-- `x≥y = y≤x` Mirror. -/
theorem ge_iff_le' : x ≥ y ↔ y ≤ x := Iff.rfl

/-- `¬ x<y = x≥y` Totality. -/
theorem not_lt_iff_ge : ¬ x < y ↔ x ≥ y := not_lt

/-- `¬ x≤y = x>y` Totality. -/
theorem not_le_iff_gt : ¬ x ≤ y ↔ x > y := not_le

/-- `x≤y ∧ y≤x = x=y` Antisymmetry. -/
theorem le_antisymm_iff' : x ≤ y ∧ y ≤ x ↔ x = y := le_antisymm_iff.symm

/-- `x<y ∨ x=y ∨ x>y` Totality, Trichotomy. -/
theorem trichotomy' : x < y ∨ x = y ∨ x > y := lt_trichotomy x y

/-- `x↑x = x` Idempotence. -/
theorem max_idem : max x x = x := max_self x

/-- `x↓x = x` Idempotence. -/
theorem min_idem : min x x = x := min_self x

/-- `x↑y = y↑x` Symmetry. -/
theorem max_symm : max x y = max y x := max_comm x y

/-- `x↓y = y↓x` Symmetry. -/
theorem min_symm : min x y = min y x := min_comm x y

/-- `x↑(y↑z) = (x↑y)↑z` Associativity. -/
theorem max_assoc' : max x (max y z) = max (max x y) z := (max_assoc x y z).symm

/-- `x↓(y↓z) = (x↓y)↓z` Associativity. -/
theorem min_assoc' : min x (min y z) = min (min x y) z := (min_assoc x y z).symm

/-- `x↑(y↓z) = (x↑y)↓(x↑z)` Distributivity. -/
theorem max_min_distrib : max x (min y z) = min (max x y) (max x z) := max_min_distrib_left x y z

/-- `x↓(y↑z) = (x↓y)↑(x↓z)` Distributivity. -/
theorem min_max_distrib : min x (max y z) = max (min x y) (min x z) := min_max_distrib_left x y z

/-- `x↑y ≤ z = x≤z ∧ y≤z` Connection. -/
theorem max_le_iff' : max x y ≤ z ↔ x ≤ z ∧ y ≤ z := max_le_iff

/-- `x↓y ≤ z = x≤z ∨ y≤z` Connection. -/
theorem min_le_iff' : min x y ≤ z ↔ x ≤ z ∨ y ≤ z := min_le_iff

/-- `x ≤ y↑z = x≤y ∨ x≤z` Connection. -/
theorem le_max_iff' : x ≤ max y z ↔ x ≤ y ∨ x ≤ z := le_max_iff

/-- `x ≤ y↓z = x≤y ∧ x≤z` Connection. -/
theorem le_min_iff' : x ≤ min y z ↔ x ≤ y ∧ x ≤ z := le_min_iff

/-- `x↑y = if x≥y then x else y`. -/
theorem max_eq_ite : max x y = if x ≥ y then x else y := by
  rcases le_total y x with h | h
  · rw [max_eq_left h, if_pos h]
  · rcases eq_or_lt_of_le h with rfl | h'
    · simp
    · rw [max_eq_right h, if_neg (not_le.mpr h')]

/-- `x↓y = if x≤y then x else y`. -/
theorem min_eq_ite : min x y = if x ≤ y then x else y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, if_pos h]
  · rcases eq_or_lt_of_le h with rfl | h'
    · simp
    · rw [min_eq_right h, if_neg (not_le.mpr h')]

end Order

end Generic

end LaPToP.BasicTheories
