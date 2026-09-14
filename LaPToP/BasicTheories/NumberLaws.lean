import VersoBlueprint
import Mathlib.Data.EReal.Inv

/-!
# Number Theory

This module formalizes the laws of Section 1.1 (Number Theory) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), as listed under
"Numbers" in the reference section (§11.3.2).

## The model

Hehner's numbers are the extended reals `xreal = –∞, real, ∞` (§2.0). We model
them as Mathlib's `EReal` (`= WithBot (WithTop ℝ)`), with `⊥ = –∞` and `⊤ = ∞`.
The book's provisos `–∞ < x < ∞` become the predicate `Number.Finite x`.

Mathlib fixes values that the book leaves unspecified: `⊤ + ⊥ = ⊥`,
`⊤ * 0 = 0`, `x / 0 = 0`, `⊤⁻¹ = 0`. Consequently:

* Laws the book states under a proviso are stated here under the same proviso
  (Mathlib sometimes proves more, e.g. `x × 0 = 0` for all `x`; we state the
  book's version).
* Three laws the book states unconditionally are false in Mathlib's model at
  the unspecified points (`∞ + –∞`, `1/∞`): distributivity of negation over
  `+` and `–`, `x – (y + z) = (x – y) – z`, and `x / (z / y) = (x × y) / z`.
  These are stated with the hypotheses that exclude those points, and the
  docstring says so. Distributivity `x × (y + z) = x × y + x × z` also fails
  there (`(–1) × (∞ + –∞)`) and is stated for finite numbers.

The Counting laws about decimal numerals (`d9+1 = (d+1)0`, …) are about
notation and are not formalized. Hehner's `↑` and `↓` are `max` and `min`.
-/

namespace LaPToP.BasicTheories

/-- A *number* (aPToP §1.1): an extended real, `–∞`, a real, or `∞`. -/
abbrev Number := EReal

namespace Number

open EReal

/-- `–∞ < x < ∞`: the book's proviso that `x` is finite. -/
abbrev Finite (x : Number) : Prop := ⊥ < x ∧ x < ⊤

/-- A finite number is a real number. -/
theorem Finite.exists_coe {x : Number} (hx : Finite x) : ∃ r : ℝ, x = r :=
  ⟨x.toReal, (coe_toReal hx.2.ne hx.1.ne').symm⟩

/-- Real numbers are finite. -/
theorem finite_coe (r : ℝ) : Finite (r : Number) := ⟨bot_lt_coe r, coe_lt_top r⟩

variable (x y z : Number)

/-! ### Addition -/

/-- `x + 0 = x` (Identity). -/
theorem add_zero : x + 0 = x := _root_.add_zero x

/-- `x + y = y + x` (Symmetry). -/
theorem add_comm : x + y = y + x := _root_.add_comm x y

/-- `x + (y + z) = (x + y) + z` (Associativity). -/
theorem add_assoc : x + (y + z) = (x + y) + z := (_root_.add_assoc x y z).symm

/-- `–∞ < x < ∞ ⇒ (x + y = x + z = (y = z))` (Cancellation). -/
theorem add_left_cancel_iff {x : Number} (hx : Finite x) : x + y = x + z ↔ y = z := by
  obtain ⟨r, rfl⟩ := hx.exists_coe
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  calc y = (y + r) - r := EReal.add_sub_cancel_right.symm
    _ = (z + r) - r := by rw [_root_.add_comm y, h, _root_.add_comm (r : Number)]
    _ = z := EReal.add_sub_cancel_right

/-- `–∞ < x ⇒ ∞ + x = ∞` (Absorption). -/
theorem top_add {x : Number} (hx : ⊥ < x) : ⊤ + x = ⊤ := top_add_of_ne_bot hx.ne'

/-- `x < ∞ ⇒ –∞ + x = –∞` (Absorption). Mathlib's `⊥ + x = ⊥` holds for all `x`. -/
theorem bot_add {x : Number} (_hx : x < ⊤) : ⊥ + x = ⊥ := EReal.bot_add x

/-! ### Negation -/

/-- `–x = 0 – x` (Negation). -/
theorem neg_eq_zero_sub : -x = 0 - x := (zero_sub x).symm

/-- `– –x = x` (Self-inverse). -/
theorem neg_neg : - -x = x := _root_.neg_neg x

/-- `–(x + y) = –x + –y` (Distributivity). The book states this for all
numbers; in Mathlib's model `∞ + –∞ = –∞`, so the law fails exactly when
`{x, y} = {∞, –∞}`, and that case is excluded by the hypotheses. -/
theorem neg_add {x y : Number} (h₁ : x ≠ ⊥ ∨ y ≠ ⊤) (h₂ : x ≠ ⊤ ∨ y ≠ ⊥) :
    -(x + y) = -x + -y := by
  rw [EReal.neg_add h₁ h₂, sub_eq_add_neg]

/-- `–(x – y) = y – x` (Antisymmetry), excluding the unspecified case
`{x, y} = {∞, –∞}` as in `neg_add`. -/
theorem neg_sub {x y : Number} (h₁ : x ≠ ⊥ ∨ y ≠ ⊥) (h₂ : x ≠ ⊤ ∨ y ≠ ⊤) :
    -(x - y) = y - x := by
  rw [EReal.neg_sub h₁ h₂, sub_eq_add_neg, _root_.add_comm]

/-- `–x × y = –(x × y)` (Semi-distributivity). -/
theorem neg_mul : -x * y = -(x * y) := EReal.neg_mul x y

/-- `–(x × y) = x × –y` (Semi-distributivity). -/
theorem neg_mul_eq_mul_neg : -(x * y) = x * -y := (mul_neg x y).symm

/-- `–x / y = –(x / y)` (Semi-distributivity). -/
theorem neg_div : -x / y = -(x / y) := EReal.neg_mul x y⁻¹

/-- `–(x / y) = x / –y` (Semi-distributivity). -/
theorem neg_div_eq_div_neg : -(x / y) = x / -y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_neg, mul_neg]

/-! ### Subtraction -/

/-- `x – 0 = x` (Identity). -/
theorem sub_zero : x - 0 = x := _root_.sub_zero x

/-- `x – y = x + –y` (Subtraction). -/
theorem sub_eq_add_neg : x - y = x + -y := _root_.sub_eq_add_neg x y

/-- `x + (y – z) = (x + y) – z` (Addition-Subtraction). -/
theorem add_sub : x + (y - z) = (x + y) - z := by
  rw [_root_.sub_eq_add_neg, _root_.sub_eq_add_neg, _root_.add_assoc]

/-- `x – (y + z) = (x – y) – z` (Addition-Subtraction), excluding the
unspecified case `{y, z} = {∞, –∞}` as in `neg_add`. -/
theorem sub_add {y z : Number} (h₁ : y ≠ ⊥ ∨ z ≠ ⊤) (h₂ : y ≠ ⊤ ∨ z ≠ ⊥) :
    x - (y + z) = (x - y) - z := by
  rw [_root_.sub_eq_add_neg, neg_add h₁ h₂, _root_.sub_eq_add_neg, _root_.sub_eq_add_neg,
    _root_.add_assoc]

/-- `–∞ < x < ∞ ⇒ (x – y = x – z = (y = z))` (Cancellation). -/
theorem sub_left_cancel_iff {x : Number} (hx : Finite x) : x - y = x - z ↔ y = z := by
  rw [_root_.sub_eq_add_neg, _root_.sub_eq_add_neg, add_left_cancel_iff _ _ hx, neg_inj]

/-- `–∞ < x < ∞ ⇒ x – x = 0` (Inverse). -/
theorem sub_self {x : Number} (hx : Finite x) : x - x = 0 := EReal.sub_self hx.2.ne hx.1.ne'

/-- `x < ∞ ⇒ ∞ – x = ∞` (Absorption). -/
theorem top_sub {x : Number} (hx : x < ⊤) : ⊤ - x = ⊤ :=
  top_add_of_ne_bot (neg_eq_bot_iff.not.mpr hx.ne)

/-- `–∞ < x ⇒ –∞ – x = –∞` (Absorption). -/
theorem bot_sub {x : Number} (_hx : ⊥ < x) : ⊥ - x = ⊥ := by
  rw [_root_.sub_eq_add_neg]; exact EReal.bot_add _

/-! ### Multiplication -/

/-- `–∞ < x < ∞ ⇒ x × 0 = 0` (Base). Mathlib's `x * 0 = 0` holds for all `x`. -/
theorem mul_zero {x : Number} (_hx : Finite x) : x * 0 = 0 := MulZeroClass.mul_zero x

/-- `x × 1 = x` (Identity). -/
theorem mul_one : x * 1 = x := _root_.mul_one x

/-- `x × y = y × x` (Symmetry). -/
theorem mul_comm : x * y = y * x := _root_.mul_comm x y

/-- `x × (y + z) = x × y + x × z` (Distributivity), for finite numbers. The
book states this for all numbers; in Mathlib's model it fails at the
unspecified point `∞ + –∞` (e.g. `x = –1`, `y = ∞`, `z = –∞`). -/
theorem mul_add {x y z : Number} (hx : Finite x) (hy : Finite y) (hz : Finite z) :
    x * (y + z) = x * y + x * z := by
  obtain ⟨r, rfl⟩ := hx.exists_coe
  obtain ⟨s, rfl⟩ := hy.exists_coe
  obtain ⟨t, rfl⟩ := hz.exists_coe
  rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, _root_.mul_add]

/-- `x × (y × z) = (x × y) × z` (Associativity). -/
theorem mul_assoc : x * (y * z) = (x * y) * z := (_root_.mul_assoc x y z).symm

/-- `–∞ < x < ∞ ∧ x ⧧ 0 ⇒ (x × y = x × z = (y = z))` (Cancellation). -/
theorem mul_left_cancel_iff {x : Number} (hx : Finite x) (hx0 : x ≠ 0) :
    x * y = x * z ↔ y = z := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hy : (x * y) / x = y := (div_eq_iff hx.1.ne' hx.2.ne hx0).2 (_root_.mul_comm x y)
  have hz : (x * z) / x = z := (div_eq_iff hx.1.ne' hx.2.ne hx0).2 (_root_.mul_comm x z)
  rw [← hy, ← hz, h]

/-- `0 < x ⇒ x × ∞ = ∞` (Absorption). -/
theorem mul_top {x : Number} (hx : 0 < x) : x * ⊤ = ⊤ := by
  rw [_root_.mul_comm]; exact top_mul_of_pos hx

/-- `0 < x ⇒ x × –∞ = –∞` (Absorption). -/
theorem mul_bot {x : Number} (hx : 0 < x) : x * ⊥ = ⊥ := by
  rw [_root_.mul_comm]; exact bot_mul_of_pos hx

/-! ### Division -/

/-- `x / 1 = x` (Identity). -/
theorem div_one : x / 1 = x := _root_.div_one x

/-- `x ⧧ 0 ⇒ 0 / x = 0` (Base). Mathlib's `0 / x = 0` holds for all `x`. -/
theorem zero_div {x : Number} (_hx : x ≠ 0) : 0 / x = 0 := EReal.zero_div

/-- `–∞ < x < ∞ ∧ x ⧧ 0 ⇒ x / x = 1` (Base). -/
theorem div_self {x : Number} (hx : Finite x) (hx0 : x ≠ 0) : x / x = 1 :=
  EReal.div_self hx.1.ne' hx.2.ne hx0

/-- `x × (y / z) = (x × y) / z` (Multiplication-Division). -/
theorem mul_div : x * (y / z) = (x * y) / z := EReal.mul_div x y z

/-- `(x × y) / z = (x / z) × y` (Multiplication-Division). -/
theorem mul_div_eq_div_mul : (x * y) / z = (x / z) * y := (mul_div_right x z y).symm

/-- `(x / z) × y = x / (z / y)` (Multiplication-Division), for finite `y`. The
book states this for all numbers; in Mathlib's model `1/∞ = 0` and `1/0 = 0`,
so it fails at `y = ±∞`. -/
theorem div_mul_eq_div_div {y : Number} (hy : Finite y) : (x / z) * y = x / (z / y) := by
  rw [div_eq_mul_inv x (z / y), div_eq_mul_inv z y, EReal.mul_inv, EReal.inv_inv hy.1.ne' hy.2.ne,
    div_eq_mul_inv, _root_.mul_assoc]

/-- `(x / y) / z = x / (y × z)` (Multiplication-Division). -/
theorem div_div : (x / y) / z = x / (y * z) := EReal.div_div x y z

/-- `–∞ < y < ∞ ∧ y ⧧ 0 ⇒ (x / y) × y = x` (Multiplication-Division). -/
theorem div_mul_cancel {y : Number} (hy : Finite y) (hy0 : y ≠ 0) : (x / y) * y = x :=
  EReal.div_mul_cancel hy.1.ne' hy.2.ne hy0

/-- `–∞ < x < ∞ ⇒ x / ∞ = 0` (Annihilation). Mathlib's `x / ⊤ = 0` holds for all `x`. -/
theorem div_top {x : Number} (_hx : Finite x) : x / ⊤ = 0 := EReal.div_top

/-- `–∞ < x < ∞ ⇒ x / –∞ = 0` (Annihilation). Mathlib's `x / ⊥ = 0` holds for all `x`. -/
theorem div_bot {x : Number} (_hx : Finite x) : x / ⊥ = 0 := EReal.div_bot

/-! ### Exponentiation -/

/-- `–∞ < x < ∞ ⇒ x^0 = 1` (Base). Mathlib's `x ^ 0 = 1` holds for all `x`. -/
theorem pow_zero {x : Number} (_hx : Finite x) : x ^ 0 = 1 := _root_.pow_zero x

/-- `x^1 = x` (Identity). -/
theorem pow_one : x ^ 1 = x := _root_.pow_one x

/-! ### Order -/

/-- `–∞ < 0 < 1 < ∞` (Direction). -/
theorem direction : (⊥ : Number) < 0 ∧ (0 : Number) < 1 ∧ (1 : Number) < ⊤ :=
  ⟨bot_lt_zero, zero_lt_one, coe_lt_top 1⟩

/-- `x < y = –y < –x` (Reflection). -/
theorem lt_iff_neg_lt_neg : x < y ↔ -y < -x := neg_lt_neg_iff.symm

/-- `–∞ < x < ∞ ⇒ (x + y < x + z = (y < z))` (Cancellation, Translation). -/
theorem add_lt_add_iff_left {x : Number} (hx : Finite x) : x + y < x + z ↔ y < z := by
  obtain ⟨r, rfl⟩ := hx.exists_coe
  exact ⟨fun h => lt_of_not_ge fun hzy => h.not_ge (add_le_add_right hzy _),
    fun h => add_lt_add_left_coe h r⟩

/-- Multiplication by a positive real preserves strict order on either side. -/
theorem coe_mul_lt_coe_mul_iff {r : ℝ} (hr : 0 < r) :
    (r : Number) * y < r * z ↔ y < z := by
  induction y using EReal.rec <;> induction z using EReal.rec <;>
    simp [coe_mul_bot_of_pos hr, coe_mul_top_of_pos hr, ← coe_mul, hr]

/-- `0 < x < ∞ ⇒ (x × y < x × z = (y < z))` (Cancellation, Scale). -/
theorem mul_lt_mul_iff_left {x : Number} (hx0 : 0 < x) (hx : x < ⊤) :
    x * y < x * z ↔ y < z := by
  obtain ⟨r, rfl⟩ := Finite.exists_coe (x := x) ⟨bot_lt_zero.trans hx0, hx⟩
  exact coe_mul_lt_coe_mul_iff y z (EReal.coe_pos.1 hx0)

/-- `x < y ∨ x = y ∨ x > y` (Trichotomy). -/
theorem trichotomy : x < y ∨ x = y ∨ x > y := lt_trichotomy x y

/-- `–∞ ≤ x ≤ ∞` (Extremes). -/
theorem extremes : ⊥ ≤ x ∧ x ≤ ⊤ := ⟨bot_le, le_top⟩

/-- `x ↑ ∞ = ∞` (Base): the maximum with `∞`. -/
theorem max_top : max x ⊤ = ⊤ := max_eq_right le_top

/-- `x ↓ –∞ = –∞` (Base): the minimum with `–∞`. -/
theorem min_bot : min x ⊥ = ⊥ := min_eq_right bot_le

end Number

end LaPToP.BasicTheories
