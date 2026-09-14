import VersoBlueprint
import Mathlib.Data.Set.Card

/-!
# Bunch Theory and Set Theory

This module formalizes Sections 2.0 (Bunch Theory) and 2.1 (Set Theory) of
Eric Hehner's *A Practical Theory of Programming* (aPToP).

## The model

Hehner's bunches are untyped, uncontained collections: `2` is a bunch, and so is
`0, 2, 5, 9`. Lean is typed, so we stratify: a *bunch of `α`* is a predicate on
`α`, i.e. a Mathlib `Set α`. The correspondence with the book's notation is

| aPToP     | here                     | meaning                         |
| --------- | ------------------------ | ------------------------------- |
| `A, B`    | `A ∪ B`                  | union                           |
| `A ‘ B`   | `A ∩ B`                  | intersection                    |
| `A –, B`  | `A \ B`                  | removal                         |
| `¢A`      | `Bunch.size A`           | size, in `ℕ∞` (`¢nat = ∞`)     |
| `x : A`   | `x ∈ A`                  | element `x` is in `A`           |
| `A : B`   | `A ⊆ B`                  | bunch `A` is included in `B`    |
| `A :: B`  | `A ⊇ B`                  | `A` includes `B`                |
| `null`    | `Bunch.null` (`= ∅`)     | the empty bunch                 |
| `x`       | `Bunch.elem x` (`= {x}`) | the elementary bunch of `x`     |
| `{A}`     | `Bunch.pack A : HSet α`  | the set containing `A`          |
| `~S`      | `HSet.contents S`        | contents of the set `S`         |
| `𝒫A`      | `Bunch.power A`          | all sets included in `A`        |
| `$S`      | `HSet.card S`            | size of a set                   |

Because bunches are sets in Lean, the *axioms* of Hehner's Bunch Theory become
*theorems* here; each is stated in the book's form and proved from Mathlib.

Hehner's "structure" axiom `{A} ⧧ A` (a set differs from its contents) is not a
statable equation in this typed model: `Bunch.pack A : HSet α` and
`A : Bunch α` live in different types, which is precisely the distinction the
axiom records.
-/

namespace LaPToP.BasicTheories

universe u

/-- A *bunch* of elements of type `α` (aPToP §2.0), modelled as a Mathlib set.
Hehner's bunches are uncontained collections; here they are predicates on `α`,
and the bunch operators are the usual set operators. -/
abbrev Bunch (α : Type u) := Set α

namespace Bunch

variable {α : Type u}

/-- `null`, the empty bunch (aPToP §2.0). -/
abbrev null : Bunch α := ∅

/-- The elementary bunch consisting of the single element `x`. Hehner writes it
just `x`; in the typed model it is the singleton `{x}`. -/
abbrev elem (x : α) : Bunch α := {x}

/-- `¢A`, the size (cardinality) of a bunch, valued in the extended naturals so
that `¢nat = ∞` as in the book. -/
noncomputable abbrev size (A : Bunch α) : ℕ∞ := A.encard

/-! ### Axioms of Bunch Theory (aPToP §2.0)

In the book, `x` and `y` are elements and `A`, `B`, `C` arbitrary bunches. -/

section Axioms

variable (x y : α) (A B C : Bunch α)

/-- `x: y = x=y` (elementary). -/
theorem elem_subset_elem : elem x ⊆ elem y ↔ x = y :=
  Set.singleton_subset_singleton

/-- An element is in a bunch iff its elementary bunch is included in it. This
bridges the two readings of Hehner's `:`. -/
theorem elem_subset_iff : elem x ⊆ A ↔ x ∈ A :=
  Set.singleton_subset_iff

/-- `x: A, B = x: A ∨ x: B` (union). -/
theorem mem_union : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
  Set.mem_union x A B

/-- `x: A‘B = x: A ∧ x: B` (intersection). -/
theorem mem_inter : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  Set.mem_inter_iff x A B

/-- `x: A–, B = x: A ∧ ¬ x: B` (removal). -/
theorem mem_remove : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B :=
  Set.mem_sdiff x

/-- `A, A = A` (idempotence). -/
theorem union_self : A ∪ A = A := Set.union_self A

/-- `A, B = B, A` (symmetry). -/
theorem union_comm : A ∪ B = B ∪ A := Set.union_comm A B

/-- `A, (B, C) = (A, B), C` (associativity). -/
theorem union_assoc : A ∪ (B ∪ C) = (A ∪ B) ∪ C := (Set.union_assoc A B C).symm

/-- `A‘A = A` (idempotence). -/
theorem inter_self : A ∩ A = A := Set.inter_self A

/-- `A‘B = B‘A` (symmetry). -/
theorem inter_comm : A ∩ B = B ∩ A := Set.inter_comm A B

/-- `A‘(B‘C) = (A‘B)‘C` (associativity). -/
theorem inter_assoc : A ∩ (B ∩ C) = (A ∩ B) ∩ C := (Set.inter_assoc A B C).symm

/-- `A–, (B, C) = (A–, B)–, C` (union removal, first equation). -/
theorem remove_union : A \ (B ∪ C) = (A \ B) \ C := Set.sdiff_sdiff.symm

/-- `(A–, B)–, C = (A–, B)‘(A–, C)` (union removal, second equation). -/
theorem remove_remove : (A \ B) \ C = (A \ B) ∩ (A \ C) := by
  ext; simp; tauto

/-- `A‘(B–, C) = (A‘B)–, C` (intersection removal, first equation). -/
theorem inter_remove : A ∩ (B \ C) = (A ∩ B) \ C := (Set.inter_sdiff_assoc A B C).symm

/-- `(A‘B)–, C = B‘(A–, C)` (intersection removal, second equation). -/
theorem inter_remove_comm : (A ∩ B) \ C = B ∩ (A \ C) := by
  ext; simp; tauto

/-- `A, (B‘C) = (A, B)‘(A, C)` (distributivity). -/
theorem union_inter_distrib : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
  Set.union_inter_distrib_left A B C

/-- `A‘(B, C) = (A‘B), (A‘C)` (distributivity). -/
theorem inter_union_distrib : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
  Set.inter_union_distrib_left A B C

/-- `A: B‘C = A: B ∧ A: C` (distributivity). -/
theorem subset_inter_iff : A ⊆ B ∩ C ↔ A ⊆ B ∧ A ⊆ C := Set.subset_inter_iff

/-- `A, B: C = A: C ∧ B: C` (antidistributivity). -/
theorem union_subset_iff : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := Set.union_subset_iff

/-- `A: A, B` (generalization). -/
theorem subset_union : A ⊆ A ∪ B := Set.subset_union_left

/-- `A‘B: A` (specialization). -/
theorem inter_subset : A ∩ B ⊆ A := Set.inter_subset_left

/-- `A: A` (reflexivity). -/
theorem subset_refl : A ⊆ A := Set.Subset.refl A

/-- `A: B ∧ B: A = A=B` (antisymmetry). -/
theorem subset_antisymm_iff : A ⊆ B ∧ B ⊆ A ↔ A = B := Set.Subset.antisymm_iff.symm

/-- `A: B ∧ B: C ⇒ A: C` (transitivity). -/
theorem subset_trans : A ⊆ B ∧ B ⊆ C → A ⊆ C := fun h => h.1.trans h.2

/-- `A:: B = B: A` (mirror). -/
theorem superset_iff : A ⊇ B ↔ B ⊆ A := Iff.rfl

/-- `¢x = 1` (size). -/
theorem size_elem : size (elem x) = 1 := Set.encard_singleton x

/-- `¢(A, B) + ¢(A‘B) = ¢A + ¢B` (size). -/
theorem size_union_add_size_inter : size (A ∪ B) + size (A ∩ B) = size A + size B :=
  Set.encard_union_add_encard_inter A B

/-- `¬ x: A = ¢(A‘x) = 0` (size). -/
theorem not_mem_iff_size_inter_elem : x ∉ A ↔ size (A ∩ elem x) = 0 := by
  rw [size, Set.encard_eq_zero, Set.inter_singleton_eq_empty]

/-- `A: B ⇒ ¢A ≤ ¢B` (size). -/
theorem size_le_size : A ⊆ B → size A ≤ size B := Set.encard_le_encard

end Axioms

/-! ### The empty bunch `null` (aPToP §2.0) -/

section Null

variable (A : Bunch α)

/-- `null: A`. -/
theorem null_subset : null ⊆ A := Set.empty_subset A

/-- `¢A = 0 = A = null`. -/
theorem size_eq_zero_iff : size A = 0 ↔ A = null := Set.encard_eq_zero

/-- `A, null = A` (identity). -/
theorem union_null : A ∪ null = A := Set.union_empty A

/-- `A‘null = null` (base). -/
theorem inter_null : A ∩ null = null := Set.inter_empty A

/-- `¢null = 0` (size). -/
theorem size_null : size (null : Bunch α) = 0 := Set.encard_empty

end Null

/-! ### Laws provable from the axioms (aPToP §2.0) -/

section Laws

variable (A B C D : Bunch α)

/-- `A, (A‘B) = A` (absorption). -/
theorem union_inter_self : A ∪ (A ∩ B) = A := sup_inf_self

/-- `A‘(A, B) = A` (absorption). -/
theorem inter_union_self : A ∩ (A ∪ B) = A := inf_sup_self

/-- `A: B ⇒ C, A: C, B` (monotonicity). -/
theorem union_subset_union_right : A ⊆ B → C ∪ A ⊆ C ∪ B := Set.union_subset_union_right C

/-- `A: B ⇒ C‘A: C‘B` (monotonicity). -/
theorem inter_subset_inter_right : A ⊆ B → C ∩ A ⊆ C ∩ B := Set.inter_subset_inter_right C

/-- `A: B = A, B = B` (inclusion, first equation). -/
theorem subset_iff_union_eq : A ⊆ B ↔ A ∪ B = B := Set.union_eq_right.symm

/-- `A, B = B = A = A‘B` (inclusion, second equation). -/
theorem union_eq_iff_inter_eq : A ∪ B = B ↔ A = A ∩ B := by
  rw [Set.union_eq_right, eq_comm, Set.inter_eq_left]

/-- `A, (B, C) = (A, B), (A, C)` (distributivity). -/
theorem union_union_distrib : A ∪ (B ∪ C) = (A ∪ B) ∪ (A ∪ C) :=
  Set.union_union_distrib_left A B C

/-- `A‘(B‘C) = (A‘B)‘(A‘C)` (distributivity). -/
theorem inter_inter_distrib : A ∩ (B ∩ C) = (A ∩ B) ∩ (A ∩ C) :=
  Set.inter_inter_distrib_left A B C

/-- `A: B ∧ C: D ⇒ A, C: B, D` (conflation). -/
theorem union_subset_union : A ⊆ B ∧ C ⊆ D → A ∪ C ⊆ B ∪ D :=
  fun h => Set.union_subset_union h.1 h.2

/-- `A: B ∧ C: D ⇒ A‘C: B‘D` (conflation). -/
theorem inter_subset_inter : A ⊆ B ∧ C ⊆ D → A ∩ C ⊆ B ∩ D :=
  fun h => Set.inter_subset_inter h.1 h.2

end Laws

end Bunch

/-! ### Set Theory (aPToP §2.1)

"All sets are elements; not all bunches are elements; that is the difference
between sets and bunches." A Hehner set is a bunch packaged into a single
value, so we model it as a one-field structure around a bunch. -/

/-- A Hehner *set* (aPToP §2.1): a bunch packaged as a single element. The book
writes `{A}` for the set containing the bunch `A` (see `Bunch.pack`) and `~S`
for the contents of the set `S` (see `HSet.contents`). -/
@[ext]
structure HSet (α : Type u) where
  /-- `~S`, the contents of the set `S`. -/
  contents : Bunch α

namespace Bunch

variable {α : Type u}

/-- `{A}`, the set containing the bunch `A` (aPToP §2.1). -/
def pack (A : Bunch α) : HSet α := ⟨A⟩

/-- `𝒫A`, the power operator: all sets that contain only elements of `A`. -/
def power (A : Bunch α) : Bunch (HSet α) := {S | S.contents ⊆ A}

end Bunch

namespace HSet

variable {α : Type u}

/-- `$S`, the size of a set, is the size of its contents. -/
noncomputable def card (S : HSet α) : ℕ∞ := Bunch.size S.contents

/-- `A ∈ S` for an element `A`: membership in the contents. -/
instance : Membership α (HSet α) := ⟨fun S x => x ∈ S.contents⟩

/-- `S ⊆ T`: inclusion of contents. -/
instance : HasSubset (HSet α) := ⟨fun S T => S.contents ⊆ T.contents⟩

/-- `S ∪ T`: union of contents. -/
instance : Union (HSet α) := ⟨fun S T => ⟨S.contents ∪ T.contents⟩⟩

/-- `S ∩ T`: intersection of contents. -/
instance : Inter (HSet α) := ⟨fun S T => ⟨S.contents ∩ T.contents⟩⟩

variable (x : α) (A B : Bunch α) (S : HSet α)

/-! ### Axioms of Set Theory (aPToP §2.1) -/

/-- `{~S} = S` (set formation). -/
theorem pack_contents : Bunch.pack S.contents = S := rfl

/-- `~{A} = A` (contents). -/
theorem contents_pack : (Bunch.pack A).contents = A := rfl

/-- `${A} = ¢A` (size, cardinality). -/
theorem card_pack : (Bunch.pack A).card = Bunch.size A := rfl

/-- `x ∈ {B} = x: B` (elements), for an element `x`. -/
theorem mem_pack : x ∈ Bunch.pack B ↔ x ∈ B := Iff.rfl

/-- `{A} ⊆ {B} = A: B` (subset). -/
theorem pack_subset_pack : Bunch.pack A ⊆ Bunch.pack B ↔ A ⊆ B := Iff.rfl

/-- `{A}: 𝒫B = A: B` (power). -/
theorem pack_mem_power : Bunch.pack A ∈ Bunch.power B ↔ A ⊆ B := Iff.rfl

/-- `{A} ∪ {B} = {A, B}` (union). -/
theorem pack_union_pack : Bunch.pack A ∪ Bunch.pack B = Bunch.pack (A ∪ B) := rfl

/-- `{A} ∩ {B} = {A‘B}` (intersection). -/
theorem pack_inter_pack : Bunch.pack A ∩ Bunch.pack B = Bunch.pack (A ∩ B) := rfl

/-- `{A} = {B} = A = B` (equation). -/
theorem pack_inj : Bunch.pack A = Bunch.pack B ↔ A = B :=
  ⟨fun h => congrArg HSet.contents h, fun h => h ▸ rfl⟩

end HSet

end LaPToP.BasicTheories
