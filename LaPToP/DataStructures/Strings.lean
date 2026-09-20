import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.List.Flatten
import Mathlib.Data.ENat.Basic
import Mathlib.Data.List.Lex

/-!
# String Theory

This module formalizes Section 2.2 (String Theory) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), for finite strings.

## The model

Hehner's strings are uncontained sequences: `4; 2; 4; 6` is a four-item
string, `nil` is the empty string, and any item `i` is a one-item string. A
*string of `α`* is modelled as a Lean `List α`. The book's notation translates as

| aPToP     | here                         | meaning                              |
| --------- | ---------------------------- | ------------------------------------ |
| `nil`     | `Str.nil` (`= []`)           | the empty string                     |
| `i`       | `Str.item i` (`= [i]`)       | a one-item string                    |
| `S; T`    | `S ++ T`                     | join                                 |
| `↔S`      | `Str.len S`                  | length, in `ℕ∞` as in the book       |
| `S n`     | `Str.at S n`                 | item `n` of `S` (indexing from 0)    |
| `S T`     | `Str.sub S T`                | the items of `S` at the indexes `T`  |
| `n*S`     | `Str.copies n S`             | `n` copies of `S` joined together    |
| `*S`      | `Str.star S`                 | the bunch of all `n*S`               |
| `S⊲n⊳i`   | `Str.update S n i`           | `S` but with item `i` at index `n`   |
| `x;..y`   | `Str.interval x y`           | the string `x; x+1; ...; y-1`        |
| `S < T`   | `S < T` (lexicographic)      | order, given an order on items       |

Only finite strings are modelled, so the book's provisos `↔S < ∞` are
automatically satisfied and are dropped from the statements, and the copy
count `n` is a natural number rather than an extended natural.

The book leaves `S n` unspecified when `n` is not an index of `S`; here
indexing returns `default` in that case, and the laws that depend on indexes
being in range carry that hypothesis explicitly.
-/

namespace LaPToP.DataStructures

universe u v

/-- A *string* of items of type `α` (aPToP §2.2), modelled as a list. -/
abbrev Str (α : Type u) := List α

namespace Str

variable {α : Type u}

/-- `nil`, the empty string. -/
abbrev nil : Str α := []

/-- The one-item string consisting of the item `i`; the book writes it just `i`. -/
abbrev item (i : α) : Str α := [i]

/-- `↔S`, the length of a string, as an extended natural number (the book's
lengths live in `xnat`). -/
def len (S : Str α) : ℕ∞ := (S.length : ℕ∞)

/-- `S n`, item `n` of `S`; indexes count the items that precede an item, so
they start at `0`. Out of range the book leaves the value unspecified; we
return `default`. -/
def «at» [Inhabited α] (S : Str α) (n : ℕ) : α := S.getD n default

/-- `S T` for a string of indexes `T`: the string of the items of `S` at those
indexes, e.g. `(3; 5; 7; 9) (2; 1; 2) = 7; 5; 7`. -/
def sub [Inhabited α] (S : Str α) (T : Str ℕ) : Str α := T.map S.at

/-- `n*S`, `n` copies of `S` joined together, e.g. `3*(0; 1) = 0; 1; 0; 1; 0; 1`. -/
def copies (n : ℕ) (S : Str α) : Str α := (List.replicate n S).flatten

/-- `*S`, the bunch of all strings formed by joining any number of copies of
`S`: `*(0; 1) = nil, 0;1, 0;1;0;1, ...`. -/
def star (S : Str α) : Set (Str α) := Set.range (copies · S)

/-- `S⊲n⊳i`, "`S` but at `n` is `i`": the string like `S` except that the item
at index `n` is `i`. -/
def update (S : Str α) (n : ℕ) (i : α) : Str α := S.set n i

/-- `x;..y`, "`x` to `y`": the string `x; x+1; ...; y-1` (empty unless `x < y`). -/
def interval (x y : ℤ) : Str ℤ := (List.range (y - x).toNat).map (fun k : ℕ => x + k)

/-! ### Axioms of String Theory (aPToP §2.2)

In the book, `S`, `T`, `U` are strings, `i`, `j` are items, and `n` is an
extended natural number. -/

section Join

variable (S T U : Str α) (i : α)

/-- `S; nil = S` (identity, left equation). -/
theorem append_nil : S ++ nil = S := List.append_nil S

/-- `S = nil; S` (identity, right equation). -/
theorem nil_append : nil ++ S = S := List.nil_append S

/-- `S; (T; U) = (S; T); U` (associativity). -/
theorem append_assoc : S ++ (T ++ U) = (S ++ T) ++ U := (List.append_assoc S T U).symm

/-- `↔nil = 0` (base). -/
theorem len_nil : len (nil : Str α) = 0 := rfl

/-- `↔i = 1` (base). -/
theorem len_item : len (item i) = 1 := rfl

/-- `↔(S; T) = ↔S + ↔T`. -/
theorem len_append : len (S ++ T) = len S + len T := by
  simpa [len] using (ENat.natCast_add (List.length S) (List.length T))

/-- `i = j = (S; i; T = S; j; T)`: equal strings have equal items at each index.
(Listed with the order axioms in the book; it needs no order.) -/
theorem append_item_append_inj (j : α) : i = j ↔ S ++ item i ++ T = S ++ item j ++ T := by
  simp

end Join

section Indexing

variable [Inhabited α] (S T U : Str α) (i : α)

/-- `S nil = nil`. -/
theorem sub_nil : sub S nil = nil := rfl

/-- `(S; i; T) ↔S = i`: the item at index `↔S` of `S; i; T` is `i`. (The book's
proviso `↔S < ∞` holds automatically for finite strings.) -/
theorem at_append_item_append : «at» (S ++ item i ++ T) S.length = i := by
  simp [«at», List.getD_eq_getElem?_getD]

/-- `S (T; U) = S T; S U`: indexing distributes over join of index strings. -/
theorem sub_append (T U : Str ℕ) : sub S (T ++ U) = sub S T ++ sub S U :=
  List.map_append ..

/-- Indexing a mapped string at an in-range index. -/
theorem at_map_of_lt {β : Type v} [Inhabited β] (f : α → β) (T : Str α) {k : ℕ}
    (hk : k < T.length) : «at» (T.map f) k = f («at» T k) := by
  simp [«at», List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]

/-- `S (T U) = (S T) U`, for `U` a string of indexes of `T`. -/
theorem sub_sub (T : Str ℕ) (U : Str ℕ) (hU : ∀ k ∈ U, k < T.length) :
    sub S (sub T U) = sub (sub S T) U := by
  simp only [sub, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  simp only [Function.comp]
  rw [at_map_of_lt _ _ (hU k hk)]

end Indexing

section Copies

variable (S T : Str α) (i j : α) (n : ℕ)

/-- `0*S = nil`. -/
theorem copies_zero : copies 0 S = nil := rfl

/-- `(n+1)*S = n*S; S`. -/
theorem copies_succ : copies (n + 1) S = copies n S ++ S := by
  simp [copies, List.replicate_succ', List.flatten_append]

/-- `(a+b)*S = a*S; b*S`. -/
theorem copies_add (a b : ℕ) (S : Str α) : copies (a + b) S = copies a S ++ copies b S := by
  induction b with
  | zero => simp [copies_zero]
  | succ b ih => rw [Nat.add_succ, copies_succ, copies_succ, ih, List.append_assoc]

/-- `n*(k*S) = (n×k)*S`: copies of copies are copies, the elementwise content of `**S = *S`. -/
theorem copies_copies (n k : ℕ) (S : Str α) : copies n (copies k S) = copies (n * k) S := by
  induction n with
  | zero => simp [copies_zero]
  | succ n ih => rw [copies_succ, ih, Nat.succ_mul, copies_add]

/-- `**S = *S` elementwise: a string of copies of a string of copies of `S` is a string of copies of `S`. -/
theorem copies_mem_star {T : Str α} (hT : T ∈ star S) (n : ℕ) : copies n T ∈ star S := by
  obtain ⟨k, rfl⟩ := hT
  exact ⟨n * k, (copies_copies n k S).symm⟩

/-- `3*(0; 1) = 0; 1; 0; 1; 0; 1`, the book's example. -/
theorem copies_three_example : copies 3 [0, 1] = [0, 1, 0, 1, 0, 1] := rfl

/-- Membership in `*S`: the strings `n*S`. -/
theorem mem_star : T ∈ star S ↔ ∃ n : ℕ, copies n S = T := Iff.rfl

/-- `(S; i; T)⊲↔S⊳j = S; j; T`: updating at index `↔S` replaces `i` by `j`. -/
theorem update_append_item_append :
    update (S ++ item i ++ T) S.length j = S ++ item j ++ T := by
  simp [update, List.append_assoc, List.set_append_right _ _ le_rfl]

/-- `(S⊲n⊳i)m = if n=m then i else Sm` (Reference §11.3.5), for an index `n` of `S`. -/
theorem at_update [Inhabited α] (S : Str α) {n : ℕ} (hn : n < S.length) (i : α) (m : ℕ) :
    «at» (update S n i) m = if n = m then i else «at» S m := by
  by_cases hnm : n = m
  · subst hnm; simp [«at», update, List.getD_eq_getElem?_getD, hn]
  · simp [«at», update, List.getD_eq_getElem?_getD, List.getElem?_set_ne hnm, hnm]

/-- `3; 5; 9⊲2⊳8 = 3; 5; 8`, the book's example. -/
theorem update_example : update [3, 5, 9] 2 8 = [3, 5, 8] := rfl

end Copies

/-! ### Order (aPToP §2.2)

"If the items of the string can be compared for order `< ≤ > ≥`, then so can
the strings. The order of two strings is determined by the items at the first
index where they differ. ... If there is no index where they differ, the
shorter string comes before the longer one." This is Lean's lexicographic order
on lists. -/

section Order

variable [LT α] (S T U : Str α) (i j : α)

/-- `nil ≤ S`. -/
theorem nil_le : (nil : Str α) ≤ S := List.nil_le S

/-- `S < S; i; T`: a proper prefix comes first. -/
theorem lt_append_item_append : S < S ++ item i ++ T := by
  induction S with
  | nil => exact List.nil_lt_cons i T
  | cons a S ih => exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, ih⟩)

/-- `i < j ⇒ S; i; T < S; j; U`: strings are ordered by the first differing item. -/
theorem append_lt_append_of_lt (h : i < j) : S ++ item i ++ T < S ++ item j ++ U := by
  induction S with
  | nil => exact List.cons_lt_cons_iff.2 (Or.inl h)
  | cons a S ih => exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, ih⟩)

end Order

/-- The order on strings is a linear order when the items are linearly ordered (Mathlib's
lexicographic `LinearOrder (List α)`), and its `<` is the `List.lt` used above: so the Generic laws
of the Reference chapter (§11.3.0) for `< ≤ > ≥ ↑ ↓` apply to strings, as the book states. -/
theorem lt_iff_lex [LinearOrder α] (S T : Str α) : S < T ↔ List.Lex (· < ·) S T := Iff.rfl

/-- `S ≤ T = ¬ T < S` (Totality, an instance of the Generic laws for strings). -/
theorem le_iff_not_lt [LinearOrder α] (S T : Str α) : S ≤ T ↔ ¬ T < S := not_lt.symm

/-! ### The string interval `x;..y` (aPToP §2.2) -/

section Interval

/-- `↔(x;..y) = y – x` (with the difference truncated at `0`; for `x ≤ y` it is
exactly `y – x`). -/
theorem len_interval (x y : ℤ) : len (interval x y) = ((y - x).toNat : ℕ∞) := by
  simp [len, interval]

/-- `x;..x = nil`. -/
theorem interval_self (x : ℤ) : interval x x = nil := by
  simp [interval]

/-- `x;..x+1 = x`. -/
theorem interval_succ (x : ℤ) : interval x (x + 1) = item x := by
  have h : (x + 1 - x).toNat = 1 := by omega
  simp [interval, item, h]

/-- `(x;..y); (y;..z) = x;..z` for `x ≤ y ≤ z`. -/
theorem interval_append_interval {x y z : ℤ} (hxy : x ≤ y) (hyz : y ≤ z) :
    interval x y ++ interval y z = interval x z := by
  have h : (z - x).toNat = (y - x).toNat + (z - y).toNat := by omega
  simp only [interval, h, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp]
  omega

/-- The items of `x;..y` are exactly the integers `i` with `x ≤ i < y`. -/
theorem mem_interval (i x y : ℤ) : i ∈ interval x y ↔ x ≤ i ∧ i < y := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨(i - x).toNat, by omega, by omega⟩

end Interval

end Str

end LaPToP.DataStructures
