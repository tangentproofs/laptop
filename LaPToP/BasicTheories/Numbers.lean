import LaPToP.BasicTheories.Bunch
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.Infinite

/-!
# Useful bunches and the interval `x,..y`

This module continues aPToP §2.0 (Bunch Theory) after the axioms: the named
bunches `bin`, `nat`, `int`, `xnat`, `xint`, the interval notation `x,..y`,
and the rule that other operators distribute over bunch union.

## The model

Hehner's numbers all live in one untyped world, so `nat : int : xint`. Here:

| aPToP    | here                                    |
| -------- | --------------------------------------- |
| `bin`    | `Bunch.bin : Bunch Bool` (everything)   |
| `nat`    | `Bunch.nat : Bunch ℤ` (`0 ≤ n`)         |
| `int`    | `Bunch.int : Bunch ℤ` (everything)      |
| `xnat`   | `Bunch.xnat : Bunch XInt` (`0 ≤ n`)     |
| `xint`   | `Bunch.xint : Bunch XInt` (everything)  |
| `x,..y`  | `Bunch.interval x y = Set.Ico x y` on ℤ |
| `–A`     | `-A` (pointwise negation, `Set.neg`)    |
| `A + B`  | `A + B` (pointwise addition, `Set.add`) |

The extended integers `XInt` are `WithBot (WithTop ℤ)`, with `⊥ = –∞` and
`⊤ = ∞`. The interval is taken with integer bounds; Hehner's `0,..∞ = nat`
becomes the statement that `nat` is the union of the intervals `0,..y`.

Hehner says of the other operators that "they distribute over bunch union";
Mathlib's pointwise operations on sets have exactly that meaning, so
`Set.neg` and `Set.add` are used for `–A` and `A+B`.
-/

namespace LaPToP.BasicTheories

/-- The extended integers `–∞, ..., –1, 0, 1, ..., ∞` (`⊥ = –∞`, `⊤ = ∞`). -/
abbrev XInt := WithBot (WithTop ℤ)

namespace Bunch

open scoped Pointwise

/-! ### Named bunches (aPToP §2.0) -/

/-- `bin = ⊤, ⊥`, the binary values. -/
def bin : Bunch Bool := Set.univ

/-- `nat = 0, 1, 2, ...`, the natural numbers, as a bunch of integers. -/
def nat : Bunch ℤ := {n | 0 ≤ n}

/-- `int = ..., –2, –1, 0, 1, 2, ...`, the integer numbers. -/
def int : Bunch ℤ := Set.univ

/-- `xnat = 0, 1, 2, ..., ∞`, the extended natural numbers. -/
def xnat : Bunch XInt := {n | 0 ≤ n}

/-- `xint = –∞, ..., –2, –1, 0, 1, 2, ..., ∞`, the extended integer numbers. -/
def xint : Bunch XInt := Set.univ

/-- The embedding of the integers into the extended integers. -/
def toXInt (n : ℤ) : XInt := ((n : WithTop ℤ) : WithBot (WithTop ℤ))

/-- `bin = ⊤, ⊥` (the defining axiom). -/
theorem bin_eq : bin = elem true ∪ elem false := by
  ext b; cases b <;> simp [bin]

/-- `0, nat+1 : nat` (construction). -/
theorem nat_construction : elem 0 ∪ (nat + elem 1) ⊆ nat := by
  rintro n (h | h)
  · simp_all [nat]
  · obtain ⟨m, hm, -, rfl, rfl⟩ := h
    simp only [nat, Set.mem_ofPred_eq] at hm ⊢
    omega

/-- `0, B+1 : B ⇒ nat : B` (induction): `nat` is the smallest bunch satisfying
the construction axiom. -/
theorem nat_induction (B : Bunch ℤ) (h : elem 0 ∪ (B + elem 1) ⊆ B) : nat ⊆ B := by
  intro n hn
  have h0 : (0 : ℤ) ∈ B := h (Or.inl rfl)
  have hs : ∀ m, m ∈ B → m + 1 ∈ B := fun m hm => h (Or.inr ⟨m, hm, 1, rfl, rfl⟩)
  exact Int.leInduction h0 (fun m _ hm => hs m hm) n hn

/-- `¢nat = ∞`. -/
theorem size_nat : size nat = ⊤ := by
  have : nat = Set.Ici (0 : ℤ) := by ext n; simp [nat]
  rw [this, size, Set.encard_eq_top_iff]
  exact Set.Ici_infinite 0

/-- `int = nat, –nat`. -/
theorem int_eq : int = nat ∪ -nat := by
  ext n
  simp only [int, nat, Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, Set.mem_neg, true_iff]
  omega

/-- `xnat = nat, ∞`. -/
theorem xnat_eq : xnat = toXInt '' nat ∪ elem ⊤ := by
  ext n
  induction n using WithBot.recBotCoe with
  | bot => simp [xnat, toXInt]
  | coe m =>
    induction m using WithTop.recTopCoe with
    | top => simp [xnat]
    | coe k =>
      simp only [xnat, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, elem, nat,
        Set.mem_singleton_iff, toXInt]
      constructor
      · intro hk
        exact Or.inl ⟨k, by exact_mod_cast hk, rfl⟩
      · rintro (⟨j, hj, hjk⟩ | h)
        · have : j = k := by exact_mod_cast hjk
          subst this; exact_mod_cast hj
        · exact absurd h (by simp)

/-- `xint = –∞, int, ∞`. -/
theorem xint_eq : xint = elem ⊥ ∪ toXInt '' int ∪ elem ⊤ := by
  ext n
  induction n using WithBot.recBotCoe with
  | bot => simp [xint]
  | coe m =>
    induction m using WithTop.recTopCoe with
    | top => simp [xint]
    | coe k => simp [xint, int, toXInt]

/-! ### The interval `x,..y` (aPToP §2.0) -/

/-- `x,..y`, "`x` to `y`" (not "`x` through `y`"): the integers `i` with
`x ≤ i < y`. -/
def interval (x y : ℤ) : Bunch ℤ := Set.Ico x y

/-- `i: x,..y = i: xint ∧ x≤i<y` (the defining axiom, with integer bounds). -/
theorem mem_interval (i x y : ℤ) : i ∈ interval x y ↔ x ≤ i ∧ i < y := Iff.rfl

/-- `0,..3 = 0, 1, 2`. -/
theorem interval_zero_three : interval 0 3 = elem 0 ∪ elem 1 ∪ elem 2 := by
  ext i; simp only [interval, Set.mem_Ico, elem, Set.mem_union, Set.mem_singleton_iff]; omega

/-- `5,..5 = null`. -/
theorem interval_five_five : interval 5 5 = null := Set.Ico_self 5

/-- `x,..x = null`, the general form of `5,..5 = null`. -/
theorem interval_self (x : ℤ) : interval x x = null := Set.Ico_self x

/-- `x,..x+1 = x`. -/
theorem interval_succ (x : ℤ) : interval x (x + 1) = elem x := by
  ext i; simp only [interval, Set.mem_Ico, elem, Set.mem_singleton_iff]; omega

/-- `¢(x,..y) = y–x`. The size is a natural number, so the difference is
truncated at `0`; for `x ≤ y` it is exactly `y – x` (see `size_interval_of_le`). -/
theorem size_interval (x y : ℤ) : size (interval x y) = ((y - x).toNat : ℕ∞) := by
  rw [size, interval, ← Finset.coe_Ico, Set.encard_coe_eq_coe_finsetCard, Int.card_Ico]

/-- `¢(x,..y) = y–x` for `x ≤ y`, read back in the integers. -/
theorem size_interval_of_le {x y : ℤ} (h : x ≤ y) :
    ∃ n : ℕ, size (interval x y) = n ∧ (n : ℤ) = y - x :=
  ⟨(y - x).toNat, size_interval x y, Int.toNat_of_nonneg (by omega)⟩

/-- `0,..∞ = nat`: with integer bounds, `nat` is the union of the intervals
`0,..y`. -/
theorem nat_eq_iUnion_interval : nat = ⋃ y : ℤ, interval 0 y := by
  ext n
  simp only [nat, Set.mem_ofPred_eq, Set.mem_iUnion, interval, Set.mem_Ico]
  exact ⟨fun h => ⟨n + 1, h, by omega⟩, fun ⟨_, h, _⟩ => h⟩

/-! ### Operators distribute over bunch union (aPToP §2.0)

"Other operators can be applied to bunches with the understanding that they
apply to the elements of the bunch. In other words, they distribute over bunch
union." -/

section Distribution

variable {α : Type*}

/-- `–null = null`. -/
theorem neg_null [Neg α] : -(null : Bunch α) = null := by
  ext; simp

/-- `–(A, B) = –A, –B`. -/
theorem neg_union [Neg α] (A B : Bunch α) : -(A ∪ B) = -A ∪ -B := by
  ext; simp [Set.mem_neg]

/-- `A+null = null` (first equation). -/
theorem add_null [Add α] (A : Bunch α) : A + null = null := Set.add_empty

/-- `null = null+A` (second equation). -/
theorem null_add [Add α] (A : Bunch α) : null + A = null := Set.empty_add

/-- `(A, B)+(C, D) = A+C, A+D, B+C, B+D`. -/
theorem union_add_union [Add α] (A B C D : Bunch α) :
    (A ∪ B) + (C ∪ D) = (A + C) ∪ (A + D) ∪ (B + C) ∪ (B + D) := by
  rw [Set.union_add, Set.add_union, Set.add_union]
  ac_rfl

/-- An elementary bunch adds like its element: `A+x = {a+x | a: A}`. -/
theorem add_elem [Add α] (A : Bunch α) (x : α) : A + elem x = (· + x) '' A :=
  Set.add_singleton

end Distribution

end Bunch

end LaPToP.BasicTheories
