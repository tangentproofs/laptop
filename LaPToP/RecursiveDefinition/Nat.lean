import LaPToP.BasicTheories.Numbers
import LaPToP.FunctionTheory.Quantifiers

/-!
# Recursive data definition: construction, induction, least fixed points

This module formalizes Section 6.0.0 (Construction and Induction) and Section
6.0.1 (Least Fixed-Points) of Eric Hehner's *A Practical Theory of
Programming* (aPToP), for the natural numbers.

## The model

`nat` is the bunch `Bunch.nat : Bunch ℤ` of Section 2.0, with its construction
axiom `0, nat+1: nat` and induction axiom `0, B+1: B ⇒ nat: B`
(`Bunch.nat_construction`, `Bunch.nat_induction`). The *nat constructor* is the
bunch function `B ↦ 0, B+1` (`natConstructor`).

The book restates construction and induction in *predicate* form for
`P: nat→bin`, and proves the bunch and predicate forms equivalent by taking
`B = §n: nat· P n` in one direction and `P = ⟨n: nat· n: B⟩` in the other. We
take `P : ℤ → Prop` restricted to `nat` (a proposition-valued predicate, as for
`∀p` in Function Theory) and reproduce both derivations *as derivations*: the
bunch form as a hypothesis yields the predicate form and conversely, without
appeal to `nat_induction`.

The book's six versions of induction are stated as `version0` … `version5`.
Each is proved outright, and the book's remarks on how they are obtained from
one another are proved as well: versions 1, 3, 5 are the duals of 0, 2, 4
under `P ↦ ¬P` (pure logic), and versions 2 and 4 are interderivable with
version 0 by changing the predicate.

A *fixed point* of `f` is `x` with `f x = x`; a *least fixed point* is a
smallest one. `nat = 0, nat+1` (fixed-point construction) and
`B = 0, B+1 ⇒ nat: B` (fixed-point induction) make `nat` the least fixed point
of its constructor. The specification-level use of least fixed points
(recursive programs, Section 6.1) is not in this module.
-/

namespace LaPToP.RecursiveDefinition

open LaPToP.BasicTheories
open scoped Pointwise

universe u

/-! ### Fixed points -/

/-- `x` is a *fixed point* of `f`: `f x = x`. -/
def IsFixedPoint {α : Type u} (f : α → α) (x : α) : Prop := f x = x

/-- `x` is a *least fixed point* of `f`: a fixed point below every fixed point. -/
def IsLeastFixedPoint {α : Type u} [LE α] (f : α → α) (x : α) : Prop :=
  IsFixedPoint f x ∧ ∀ y, IsFixedPoint f y → x ≤ y

/-- A least fixed point is unique. -/
theorem IsLeastFixedPoint.unique {α : Type u} [PartialOrder α] {f : α → α} {x y : α}
    (hx : IsLeastFixedPoint f x) (hy : IsLeastFixedPoint f y) : x = y :=
  le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

/-! ### The nat constructor and the bunch forms (aPToP §6.0.0) -/

/-- The *nat constructor* `B ↦ 0, B+1`: "`0` and `nat+1` are called the nat
constructors". -/
def natConstructor (B : Bunch ℤ) : Bunch ℤ := Bunch.elem 0 ∪ (B + Bunch.elem 1)

/-- `0, nat+1: nat` (nat construction), restated with the constructor. -/
theorem natConstructor_subset : natConstructor Bunch.nat ⊆ Bunch.nat := Bunch.nat_construction

/-- `0, B+1: B ⇒ nat: B` (nat induction): "of all these bunches, nat is the smallest". -/
theorem nat_subset_of_natConstructor_subset (B : Bunch ℤ) (h : natConstructor B ⊆ B) : Bunch.nat ⊆ B :=
  Bunch.nat_induction B h

/-- Membership in the constructor's image, unfolded. -/
theorem mem_natConstructor {B : Bunch ℤ} {n : ℤ} : n ∈ natConstructor B ↔ n = 0 ∨ ∃ m ∈ B, m + 1 = n := by
  simp only [natConstructor, Set.mem_union, Bunch.elem, Set.mem_singleton_iff, Set.mem_add]
  constructor
  · rintro (h | ⟨m, hm, k, hk, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨m, hm, by rw [hk]⟩
  · rintro (h | ⟨m, hm, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨m, hm, 1, rfl, rfl⟩

/-! ### Predicate forms (aPToP §6.0.0)

"In predicate notation, the nat induction axiom can be stated as follows: if
`P: nat→bin`, `P 0 ∧ ∀n: nat· P n ⇒ P(n+1) ⇒ ∀n: nat· P n`." -/

/-- Version 0, the nat induction axiom in predicate form:
`P 0 ∧ (∀n: nat· P n ⇒ P(n+1)) ⇒ ∀n: nat· P n`. -/
def Version0 (P : ℤ → Prop) : Prop :=
  (P 0 ∧ ∀ n ∈ Bunch.nat, P n → P (n + 1)) → ∀ n ∈ Bunch.nat, P n

/-- Version 1: `P 0 ∨ (∃n: nat· ¬P n ∧ P(n+1)) ⇐ ∃n: nat· P n`. -/
def Version1 (P : ℤ → Prop) : Prop :=
  (∃ n ∈ Bunch.nat, P n) → P 0 ∨ ∃ n ∈ Bunch.nat, ¬ P n ∧ P (n + 1)

/-- Version 2, "the prettiest": `(∀n: nat· P n ⇒ P(n+1)) ⇒ ∀n: nat· P 0 ⇒ P n` —
"if you can “go” from any natural to the next, then you can “go” from 0 to any natural". -/
def Version2 (P : ℤ → Prop) : Prop :=
  (∀ n ∈ Bunch.nat, P n → P (n + 1)) → ∀ n ∈ Bunch.nat, P 0 → P n

/-- Version 3: `(∃n: nat· ¬P n ∧ P(n+1)) ⇐ ∃n: nat· ¬P 0 ∧ P n`. -/
def Version3 (P : ℤ → Prop) : Prop :=
  (∃ n ∈ Bunch.nat, ¬ P 0 ∧ P n) → ∃ n ∈ Bunch.nat, ¬ P n ∧ P (n + 1)

/-- Version 4 (strong induction): `(∀n: nat· (∀m: nat· m<n ⇒ P m) ⇒ P n) ⇒ ∀n: nat· P n`. -/
def Version4 (P : ℤ → Prop) : Prop :=
  (∀ n ∈ Bunch.nat, (∀ m ∈ Bunch.nat, m < n → P m) → P n) → ∀ n ∈ Bunch.nat, P n

/-- Version 5 (least element): `(∃n: nat· (∀m: nat· m<n ⇒ ¬P m) ∧ P n) ⇐ ∃n: nat· P n`. -/
def Version5 (P : ℤ → Prop) : Prop :=
  (∃ n ∈ Bunch.nat, P n) → ∃ n ∈ Bunch.nat, (∀ m ∈ Bunch.nat, m < n → ¬ P m) ∧ P n

/-- The predicate form of nat construction:
`P 0 ∧ (∀n: nat· P n ⇒ P(n+1)) ⇐ ∀n: nat· P n`. -/
def ConstructionPred (P : ℤ → Prop) : Prop :=
  (∀ n ∈ Bunch.nat, P n) → P 0 ∧ ∀ n ∈ Bunch.nat, P n → P (n + 1)

/-- `n ∈ nat ↔ 0 ≤ n`. -/
theorem mem_nat {n : ℤ} : n ∈ Bunch.nat ↔ 0 ≤ n := Iff.rfl

/-! #### Bunch form ⟹ predicate form, and back (the book's two derivations) -/

/-- "The bunch form implies the predicate form": from nat induction for all
bunches, version 0 for all predicates, taking `B = §n: nat· P n`. -/
theorem version0_of_bunchInduction (h : ∀ B : Bunch ℤ, natConstructor B ⊆ B → Bunch.nat ⊆ B)
    (P : ℤ → Prop) : Version0 P := by
  rintro ⟨h0, hs⟩ n hn
  have := h {m | m ∈ Bunch.nat ∧ P m} (by
    intro k hk
    rcases mem_natConstructor.1 hk with rfl | ⟨m, ⟨hm, hPm⟩, rfl⟩
    · exact ⟨mem_nat.2 le_rfl, h0⟩
    · exact ⟨by simp only [mem_nat] at hm ⊢; omega, hs m hm hPm⟩)
  exact (this hn).2

/-- "The reverse is proved similarly": from version 0 for all predicates, nat
induction for all bunches, taking `P = ⟨n: nat· n: B⟩`. -/
theorem bunchInduction_of_version0 (h : ∀ P : ℤ → Prop, Version0 P) (B : Bunch ℤ)
    (hB : natConstructor B ⊆ B) : Bunch.nat ⊆ B := by
  intro n hn
  refine h (· ∈ B) ⟨hB (mem_natConstructor.2 (Or.inl rfl)), fun m _ hm => ?_⟩ n hn
  exact hB (mem_natConstructor.2 (Or.inr ⟨m, hm, rfl⟩))

/-- "The bunch form implies the predicate form" of construction, from nat
construction. -/
theorem constructionPred_of_bunchConstruction (h : natConstructor Bunch.nat ⊆ Bunch.nat)
    (P : ℤ → Prop) : ConstructionPred P := fun hP =>
  ⟨hP 0 (h (mem_natConstructor.2 (Or.inl rfl))),
    fun n hn _ => hP (n + 1) (h (mem_natConstructor.2 (Or.inr ⟨n, hn, rfl⟩)))⟩

/-- "The predicate form implies the bunch form" of construction, taking
`P = ⟨n: nat· n: nat⟩`. -/
theorem bunchConstruction_of_constructionPred (h : ∀ P : ℤ → Prop, ConstructionPred P) :
    natConstructor Bunch.nat ⊆ Bunch.nat := by
  obtain ⟨h0, hs⟩ := h (· ∈ Bunch.nat) fun _ hn => hn
  intro n hn
  rcases mem_natConstructor.1 hn with rfl | ⟨m, hm, rfl⟩
  · exact h0
  · exact hs m hm hm

/-! #### The six versions hold -/

/-- Version 0 holds. -/
theorem version0 (P : ℤ → Prop) : Version0 P :=
  version0_of_bunchInduction nat_subset_of_natConstructor_subset P

/-- The predicate form of construction holds. -/
theorem constructionPred (P : ℤ → Prop) : ConstructionPred P :=
  constructionPred_of_bunchConstruction natConstructor_subset P

/-- "A corollary is that nat can be defined by the single axiom
`P 0 ∧ (∀n: nat· P n ⇒ P(n+1)) = ∀n: nat· P n`." -/
theorem single_axiom (P : ℤ → Prop) :
    (P 0 ∧ ∀ n ∈ Bunch.nat, P n → P (n + 1)) ↔ ∀ n ∈ Bunch.nat, P n :=
  ⟨version0 P, constructionPred P⟩

/-- Version 2 from version 0, changing the predicate to `P 0 ⇒ P n`. -/
theorem version2_of_version0 (h : ∀ Q : ℤ → Prop, Version0 Q) (P : ℤ → Prop) : Version2 P :=
  fun hs n hn h0 => h (fun n => P 0 → P n) ⟨id, fun n hn ih h0 => hs n hn (ih h0)⟩ n hn h0

/-- Version 0 from version 2 (same predicate). -/
theorem version0_of_version2 {P : ℤ → Prop} (h : Version2 P) : Version0 P :=
  fun ⟨h0, hs⟩ n hn => h hs n hn h0

/-- Version 4 (strong induction) from version 0, changing the predicate to
`∀m: nat· m ≤ n ⇒ P m`. -/
theorem version4_of_version0 (h : ∀ Q : ℤ → Prop, Version0 Q) (P : ℤ → Prop) : Version4 P := by
  intro hstrong n hn
  have key : ∀ n ∈ Bunch.nat, ∀ m ∈ Bunch.nat, m ≤ n → P m := by
    refine h (fun n => ∀ m ∈ Bunch.nat, m ≤ n → P m) ⟨fun m hm hm0 => ?_, fun n hn ih m hm hmn => ?_⟩
    · have : m = 0 := le_antisymm hm0 hm
      subst this
      exact hstrong 0 hm fun k hk hk0 => absurd (hk.trans_lt hk0) (lt_irrefl _)
    · rcases lt_or_eq_of_le hmn with hlt | heq
      · exact ih m hm (by omega)
      · rw [heq] at hm ⊢
        exact hstrong (n + 1) hm fun k hk hkn => ih k hk (by omega)
  exact key n hn n hn le_rfl

/-- Version 0 from version 4 (same predicate). -/
theorem version0_of_version4 {P : ℤ → Prop} (h : Version4 P) : Version0 P := by
  rintro ⟨h0, hs⟩
  refine h fun n hn ih => ?_
  rcases eq_or_lt_of_le (mem_nat.1 hn) with heq | hpos
  · exact heq ▸ h0
  · have := ih (n - 1) (by simp only [mem_nat]; omega) (by omega)
    simpa using hs (n - 1) (by simp only [mem_nat]; omega) this

/-- Version 2 holds. -/
theorem version2 (P : ℤ → Prop) : Version2 P := version2_of_version0 version0 P

/-- Version 4 holds. -/
theorem version4 (P : ℤ → Prop) : Version4 P := version4_of_version0 version0 P

/-- "Version 1 is obtained from version 0 by the duality laws and a renaming":
version 1 for `P` is version 0 for `¬P`. -/
theorem version1_iff_version0_not (P : ℤ → Prop) : Version1 P ↔ Version0 fun n => ¬ P n := by
  simp only [Version1, Version0]
  constructor
  · intro h ⟨h0, hs⟩ n hn hP
    rcases h ⟨n, hn, hP⟩ with h0' | ⟨m, hm, hm1, hm2⟩
    · exact h0 h0'
    · exact hs m hm hm1 hm2
  · intro h ⟨n, hn, hP⟩
    by_contra hc
    push Not at hc
    exact h ⟨hc.1, hc.2⟩ n hn hP

/-- "Version 3 is obtained from version 2 by the duality laws and a renaming". -/
theorem version3_iff_version2_not (P : ℤ → Prop) : Version3 P ↔ Version2 fun n => ¬ P n := by
  simp only [Version3, Version2]
  constructor
  · intro h hs n hn h0 hP
    obtain ⟨m, hm, hm1, hm2⟩ := h ⟨n, hn, h0, hP⟩
    exact hs m hm hm1 hm2
  · intro h ⟨n, hn, h0, hP⟩
    by_contra hc
    push Not at hc
    exact h hc n hn h0 hP

/-- Version 5 is the dual of version 4. -/
theorem version5_iff_version4_not (P : ℤ → Prop) : Version5 P ↔ Version4 fun n => ¬ P n := by
  simp only [Version4, Version5]
  constructor
  · intro h hs n hn hP
    obtain ⟨m, hm, hmin, hPm⟩ := h ⟨n, hn, hP⟩
    exact hs m hm hmin hPm
  · intro h ⟨n, hn, hP⟩
    by_contra hc
    push Not at hc
    exact h (fun m hm hmin hPm => hc m hm hmin hPm) n hn hP

/-- Version 1 holds. -/
theorem version1 (P : ℤ → Prop) : Version1 P := (version1_iff_version0_not P).2 (version0 _)

/-- Version 3 holds. -/
theorem version3 (P : ℤ → Prop) : Version3 P := (version3_iff_version2_not P).2 (version2 _)

/-- Version 5 holds: every nonempty set of naturals has a least element. -/
theorem version5 (P : ℤ → Prop) : Version5 P := (version5_iff_version4_not P).2 (version4 _)

/-- "These six versions are all equivalent to each other, and all equivalent to
the bunch form of induction": each, taken for all predicates, is equivalent to
nat induction for all bunches. -/
theorem versions_equivalent :
    (∀ B : Bunch ℤ, natConstructor B ⊆ B → Bunch.nat ⊆ B) ↔ (∀ P, Version0 P) ∧ (∀ P, Version1 P) ∧
      (∀ P, Version2 P) ∧ (∀ P, Version3 P) ∧ (∀ P, Version4 P) ∧ (∀ P, Version5 P) :=
  ⟨fun h => ⟨version0_of_bunchInduction h,
      fun P => (version1_iff_version0_not P).2 (version0_of_bunchInduction h _),
      version2_of_version0 (version0_of_bunchInduction h),
      fun P => (version3_iff_version2_not P).2 (version2_of_version0 (version0_of_bunchInduction h) _),
      version4_of_version0 (version0_of_bunchInduction h),
      fun P => (version5_iff_version4_not P).2 (version4_of_version0 (version0_of_bunchInduction h) _)⟩,
    fun ⟨h0, _⟩ => bunchInduction_of_version0 h0⟩

/-! ### Least fixed points (aPToP §6.0.1) -/

/-- `nat = 0, nat+1` (nat fixed-point construction): "stronger than nat
construction, so the proof will also have to use nat induction". -/
theorem nat_fixedPoint_construction : natConstructor Bunch.nat = Bunch.nat := by
  refine Set.Subset.antisymm natConstructor_subset fun n hn => ?_
  rcases eq_or_lt_of_le (mem_nat.1 hn) with heq | hpos
  · exact mem_natConstructor.2 (Or.inl heq.symm)
  · exact mem_natConstructor.2 (Or.inr ⟨n - 1, by simp only [mem_nat]; omega, by omega⟩)

/-- `B = 0, B+1 ⇒ nat: B` (nat fixed-point induction), "just by strengthening
the antecedent of nat induction". -/
theorem nat_fixedPoint_induction (B : Bunch ℤ) (h : natConstructor B = B) : Bunch.nat ⊆ B :=
  nat_subset_of_natConstructor_subset B h.le

/-- `nat` is a fixed point of its constructor. -/
theorem nat_isFixedPoint : IsFixedPoint natConstructor Bunch.nat := nat_fixedPoint_construction

/-- "We could have defined nat ... as the least fixed-point of its constructor." -/
theorem nat_isLeastFixedPoint : IsLeastFixedPoint natConstructor Bunch.nat :=
  ⟨nat_isFixedPoint, nat_fixedPoint_induction⟩

/-- The constructor is monotonic. -/
theorem natConstructor_mono {A B : Bunch ℤ} (h : A ⊆ B) : natConstructor A ⊆ natConstructor B :=
  Set.union_subset_union_right _ (Set.add_subset_add_right h)

end LaPToP.RecursiveDefinition
