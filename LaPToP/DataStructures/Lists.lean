import LaPToP.DataStructures.Strings
import LaPToP.BasicTheories.Numbers

/-!
# List Theory

This module formalizes Section 2.3 (List Theory) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), for finite lists.

## The model

"A list is a contained string." Just as a Hehner set packages a bunch
(`LaPToP.BasicTheories.HSet`), a Hehner list packages a string: `HList α` is a
one-field structure around a `Str α`. The book's notation translates as

| aPToP        | here                          | meaning                                   |
| ------------ | ----------------------------- | ----------------------------------------- |
| `[S]`        | `Str.pack S : HList α`        | the list containing the string `S`        |
| `~L`         | `HList.contents L`            | the contents of `L`, a string             |
| `#L`         | `HList.length L`              | length, in `ℕ∞` as in the book            |
| `☐L`         | `HList.domain L`              | domain `0,..#L`, a bunch of naturals       |
| `L n`        | `HList.at L n`                | item at index `n`                         |
| `L M`        | `HList.comp L M`              | composition: `L` indexed by the list `M`  |
| `L ;; M`     | `HList.join L M`              | join                                      |
| `n→i \| L`   | `HList.modify n i L`          | "`n` maps to `i` otherwise `L`"           |
| `L < M`      | `L < M`                       | lexicographic order, as for strings       |

Hehner's "structure" axiom `[S] ⧧ S` (a list differs from its contents) is not a
statable equation in the typed model: `Str.pack S : HList α` and `S : Str α`
live in different types, which is precisely the distinction the axiom records.
The same remark applies to `{A} ⧧ A` in Set Theory.
-/

namespace LaPToP.DataStructures

open LaPToP.BasicTheories (Bunch)

universe u

/-- A Hehner *list* (aPToP §2.3): a string packaged as a single item. The book
writes `[S]` for the list containing the string `S` (see `Str.pack`) and `~L`
for the contents of the list `L` (see `HList.contents`). -/
@[ext]
structure HList (α : Type u) where
  /-- `~L`, the contents of the list `L`, a string. -/
  contents : Str α
  deriving DecidableEq

namespace Str

variable {α : Type u}

/-- `[S]`, the list containing the string `S` (aPToP §2.3). -/
def pack (S : Str α) : HList α := ⟨S⟩

/-- Packaging is injective; `[S] = [T] = (S = T)` is `HList.pack_inj`. -/
theorem pack_injective : Function.Injective (pack : Str α → HList α) :=
  fun _ _ h => congrArg HList.contents h

end Str

namespace HList

variable {α : Type u}

/-- `#L`, the length of a list: the number of items it contains. -/
def length (L : HList α) : ℕ∞ := Str.len L.contents

/-- `☐L`, the domain of a list: the bunch of its indexes `0,..#L`. -/
def domain (L : HList α) : Bunch ℕ := Set.Iio L.contents.length

/-- `L n`, the item of `L` at index `n` (indexing from `0`). -/
def «at» [Inhabited α] (L : HList α) (n : ℕ) : α := Str.at L.contents n

/-- `L M`, list composition: the list of items of `L` at the indexes listed in
`M`, e.g. `[3; 5; 7; 4] [2; 1; 2] = [7; 5; 7]`. -/
def comp [Inhabited α] (L : HList α) (M : HList ℕ) : HList α :=
  ⟨Str.sub L.contents M.contents⟩

/-- `L ;; M`, list join. -/
def join (L M : HList α) : HList α := ⟨L.contents ++ M.contents⟩

/-- `n→i | L`, "`n` maps to `i` otherwise `L`": the list like `L` except that
item `n` is `i`. -/
def modify (n : ℕ) (i : α) (L : HList α) : HList α := ⟨Str.update L.contents n i⟩

/-- Lists are ordered lexicographically, like strings. -/
instance [LT α] : LT (HList α) := ⟨fun L M => L.contents < M.contents⟩

/-- When the items are linearly ordered, so are the lists (the order lifted from the strings; its
`<` is the instance above), so the Generic laws of the Reference chapter (§11.3.0) apply to lists. -/
noncomputable instance [LinearOrder α] : LinearOrder (HList α) :=
  LinearOrder.lift' HList.contents fun L M h => by cases L; cases M; cases h; rfl

/-- The linear order's `<` is the lexicographic order of the contents. -/
theorem lt_iff_contents_lt [LinearOrder α] (L M : HList α) : L < M ↔ L.contents < M.contents := Iff.rfl

/-- `L ≤ M = ¬ M < L` (Totality, an instance of the Generic laws for lists). -/
theorem le_iff_not_lt [LinearOrder α] (L M : HList α) : L ≤ M ↔ ¬ M < L := not_lt.symm

/-! ### Axioms of List Theory (aPToP §2.3)

In the book, `L` and `M` are lists, `S` and `T` strings, `n` an index of `S`,
`i` an item, and `A` and `B` bunches of strings. -/

section Axioms

variable (L M : HList α) (S T : Str α) (n : ℕ) (i : α)

/-- `[~L] = L` (list formation). -/
theorem pack_contents : Str.pack L.contents = L := rfl

/-- `~[S] = S` (contents). -/
theorem contents_pack : (Str.pack S).contents = S := rfl

/-- `#[S] = ↔S` (length). -/
theorem length_pack : (Str.pack S).length = Str.len S := rfl

/-- `☐L = 0,..#L` (domain): the indexes of `L` are the naturals below its length. -/
theorem domain_eq : L.domain = {n | n < L.contents.length} := rfl

/-- `#L = ¢☐L`: the length is the size of the domain. -/
theorem length_eq_size_domain : L.length = Bunch.size L.domain := by
  rw [length, Str.len, domain, Bunch.size, ← Finset.coe_range, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]

/-- The domain, read in the integers, is the bunch interval `0,..#L`. -/
theorem image_domain : (Nat.cast '' L.domain : Bunch ℤ) = Bunch.interval 0 L.contents.length := by
  ext k
  simp only [domain, Set.mem_image, Set.mem_Iio, Bunch.interval, Set.mem_Ico]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · intro h; exact ⟨k.toNat, by omega, by omega⟩

/-- `[S];;[T] = [S; T]` (join). -/
theorem pack_join_pack : join (Str.pack S) (Str.pack T) = Str.pack (S ++ T) := rfl

/-- `[S] n = S n` (indexing). -/
theorem at_pack [Inhabited α] : (Str.pack S).at n = Str.at S n := rfl

/-- `[S] [T] = [S T]` (composition). -/
theorem pack_comp_pack [Inhabited α] (T : Str ℕ) :
    comp (Str.pack S) (Str.pack T) = Str.pack (Str.sub S T) := rfl

/-- `n→i | [S] = [S⊲n⊳i]` (modification). -/
theorem modify_pack : modify n i (Str.pack S) = Str.pack (Str.update S n i) := rfl

/-- `[S] = [T] = (S = T)` (equation). -/
theorem pack_inj : Str.pack S = Str.pack T ↔ S = T :=
  ⟨fun h => congrArg HList.contents h, fun h => h ▸ rfl⟩

/-- `[S] < [T] = (S < T)` (order). -/
theorem pack_lt_pack [LT α] : Str.pack S < Str.pack T ↔ S < T := Iff.rfl

/-- `[A]: [B] = A: B` (inclusion), for bunches of strings `A`, `B`; list brackets
distribute over bunch union, so `[A]` is the bunch of lists `[S]` for `S : A`. -/
theorem image_pack_subset_image_pack (A B : Bunch (Str α)) :
    Str.pack '' A ⊆ Str.pack '' B ↔ A ⊆ B :=
  Set.image_subset_image_iff Str.pack_injective

end Axioms

/-! ### Theorems provable from the axioms (aPToP §2.3) -/

section Laws

variable [Inhabited α] (L : HList α) (M N : HList ℕ)

/-- `(L M) n = L (M n)` (composition), for `n` an index of `M`. -/
theorem comp_at {n : ℕ} (hn : n < M.contents.length) : (comp L M).at n = L.at (M.at n) :=
  Str.at_map_of_lt _ _ hn

/-- `(L M) N = L (M N)` (associativity), for `N` a list of indexes of `M`. -/
theorem comp_assoc (hN : ∀ k ∈ N.contents, k < M.contents.length) :
    comp (comp L M) N = comp L (comp M N) :=
  HList.ext (Str.sub_sub L.contents M.contents N.contents hN).symm

/-- `L (M;;N) = L M ;; L N` (distributivity). -/
theorem comp_join : comp L (join M N) = join (comp L M) (comp L N) :=
  HList.ext (Str.sub_append L.contents M.contents N.contents)

end Laws

/-! ### The book's examples (aPToP §2.3) -/

section Examples

/-- `~[3; 5; 7; 4] = 3; 5; 7; 4`. -/
theorem contents_example : (Str.pack [3, 5, 7, 4]).contents = [3, 5, 7, 4] := rfl

/-- `#[3; 5; 7; 4] = 4`. -/
theorem length_example : (Str.pack [3, 5, 7, 4]).length = 4 := rfl

/-- `[3; 5; 7; 4] 2 = 7`. -/
theorem at_example : (Str.pack [3, 5, 7, 4]).at 2 = 7 := rfl

/-- `[3; 5; 7; 4] [2; 1; 2] = [7; 5; 7]`. -/
theorem comp_example : comp (Str.pack [3, 5, 7, 4]) (Str.pack [2, 1, 2]) = Str.pack [7, 5, 7] := rfl

/-- `[3; 5; 7; 4];;[2; 1; 2] = [3; 5; 7; 4; 2; 1; 2]`. -/
theorem join_example :
    join (Str.pack [3, 5, 7, 4]) (Str.pack [2, 1, 2]) = Str.pack [3, 5, 7, 4, 2, 1, 2] := rfl

/-- `2→22 | [10;..15] = [10; 11; 22; 13; 14]`. -/
theorem modify_example :
    modify 2 22 (Str.pack (Str.interval 10 15)) = Str.pack [10, 11, 22, 13, 14] := by decide

/-- `2→22 | 3→33 | [10;..15] = [10; 11; 22; 33; 14]`. -/
theorem modify_modify_example :
    modify 2 22 (modify 3 33 (Str.pack (Str.interval 10 15))) = Str.pack [10, 11, 22, 33, 14] := by
  decide

/-- With `L = [10;..15]`, `2→L 3 | 3→L 2 | L = [10; 11; 13; 12; 14]`: swapping two items. -/
theorem modify_swap_example :
    let L : HList ℤ := Str.pack (Str.interval 10 15)
    modify 2 (L.at 3) (modify 3 (L.at 2) L) = Str.pack [10, 11, 13, 12, 14] := by
  decide

end Examples

end HList

end LaPToP.DataStructures

/-! ### Modification and indexing -/

namespace LaPToP.DataStructures.HList

variable {α : Type u}

/-- `#(n→i | L) = #L`: modification preserves length. -/
theorem length_contents_modify (L : HList α) (n : ℕ) (i : α) :
    (modify n i L).contents.length = L.contents.length := List.length_set ..

variable [Inhabited α]

/-- `(n→i | L) n = i` for `n` an index of `L`. -/
theorem at_modify_self (L : HList α) {n : ℕ} (i : α) (h : n < L.contents.length) :
    (modify n i L).at n = i := by
  simp [modify, «at», Str.update, Str.at, List.getD_eq_getElem?_getD, List.getElem?_set_self h]

/-- `(n→i | L) m = L m` for `m ≠ n`. -/
theorem at_modify_ne (L : HList α) {n m : ℕ} (i : α) (h : m ≠ n) :
    (modify n i L).at m = L.at m := by
  simp [modify, «at», Str.update, Str.at, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

end LaPToP.DataStructures.HList
