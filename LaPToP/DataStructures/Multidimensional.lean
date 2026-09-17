import LaPToP.DataStructures.Lists

/-!
# Multidimensional structures

This module formalizes Subsection 2.3.0 (Multidimensional Structures) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), p. 22, and with it the
`@` and string-indexed modification laws of the Reference chapter
(Section 11.3.6).

"A list is sometimes called an array, especially if it is multidimensional. For
example, let `A = [[6; 3; 7; 0]; [4; 9; 2; 5]; [1; 5; 8; 3]]`. Then `A` is a
2-dimensional array, or more particularly, a `3×4` array. ... Indexing `A` with
one index gives a list `A 1 = [4; 9; 2; 5]` which can then be indexed again to
give a number. `A 1 2 = 2`. ... Lists of lists can also be quite irregular in
shape, not just by containing lists of different lengths, but in
dimensionality. For example, let `B = [[2; 3]; 4; [5; [6; 7]]]`. Now `B 0 0 = 2`
and `B 1 = 4`, and `B 1 1` is undefined. The number of indexes needed to obtain a
number varies. We can regain some regularity in the following way. Let `L` be
a list, let `n` be an index, and let `S` and `T` be strings of indexes. Then
`L@nil = L`, `L@n = L n`, `L@(S; T) = L@S@T`. Now we can always “index” with a
single string, obtaining the same result as indexing by the sequence of items
in the string. In the example list, `B@(2; 1; 0) = B 2 1 0 = 6`. We generalize
the notation `S→i | L` to allow `S` to be a string of indexes. The axioms are
`nil→i | L = i`, `(S; T)→i | L = S→(T→i | L@S) | L`. Thus `S→i | L` is a list
like `L` except that `S` points to item `i`. For example,
`(0;1)→6 | [[0; 1; 2]; [3; 4; 5]] = [[0; 6; 2]; [3; 4; 5]]`."

## The model

Rectangular arrays are lists of lists, `HList (HList α)`, indexed twice. The
irregular structures — "lists of lists ... irregular in shape ... in
dimensionality" — need a type of finitely nested lists: `Nested α` is either an
item or a list of nested structures (the book's `B`). String indexing `L@S`
and string-indexed modification `S→i | L` are defined by recursion on the
string, one index at a time, and the book's axioms are proved from them; where
the book leaves a result undefined (`B 1 1`, indexing an item, or an index out
of range), the definitions return a default item, as `L n` does out of range
in Section 2.3. Both examples are computed.
-/

namespace LaPToP.DataStructures

universe u

variable {α : Type u}

/-! ### Rectangular arrays: lists of lists -/

/-- The `3×4` array `A = [[6; 3; 7; 0]; [4; 9; 2; 5]; [1; 5; 8; 3]]`. -/
def arrayA : HList (HList ℕ) := Str.pack [Str.pack [6, 3, 7, 0], Str.pack [4, 9, 2, 5], Str.pack [1, 5, 8, 3]]

/-- "Indexing `A` with one index gives a list `A 1 = [4; 9; 2; 5]`". -/
theorem arrayA_one : arrayA.at 1 = Str.pack [4, 9, 2, 5] := rfl

/-- "which can then be indexed again to give a number. `A 1 2 = 2`". -/
theorem arrayA_one_two : (arrayA.at 1).at 2 = 2 := rfl

/-- `A (1, 2) = A 1, A 2` — indexing by a bunch gives the bunch of the two rows. -/
theorem arrayA_bunch : (arrayA.at) '' ({1, 2} : Set ℕ) = {Str.pack [4, 9, 2, 5], Str.pack [1, 5, 8, 3]} := by
  rw [Set.image_insert_eq, Set.image_singleton]; rfl

/-- `A [1, 2] = [A 1, A 2]` — indexing by a list of indexes gives the list of rows. -/
theorem arrayA_list : arrayA.comp (Str.pack [1, 2]) = Str.pack [Str.pack [4, 9, 2, 5], Str.pack [1, 5, 8, 3]] := rfl

/-! ### Irregular structures: finitely nested lists -/

/-- A finitely nested list: an item, or a list of nested lists ("lists of lists ... irregular in
shape ... in dimensionality"). -/
inductive Nested (α : Type u) where
  /-- A single item. -/
  | item : α → Nested α
  /-- A list of nested lists. -/
  | list : List (Nested α) → Nested α

namespace Nested

/-- The default nested structure is the default item. -/
instance [Inhabited α] : Inhabited (Nested α) := ⟨item default⟩

/-- `L n`, one level of indexing; a default item where the book leaves the result undefined
(indexing an item, or out of range). -/
def child [Inhabited α] : Nested α → ℕ → Nested α
  | list M, n => M.getD n default
  | item _, _ => default

/-- `L@S`, indexing by a string of indexes, one index at a time. -/
def idx [Inhabited α] : Nested α → Str ℕ → Nested α
  | L, [] => L
  | L, n :: S => idx (child L n) S

/-- `n→i | L` at one level: replace the `n`-th component (a list unchanged where the book leaves the
result undefined). -/
def setChild : ℕ → Nested α → Nested α → Nested α
  | n, i, list M => list (M.set n i)
  | _, _, item a => item a

/-- `S→i | L`, modification at a string of indexes, one index at a time. -/
def modify [Inhabited α] : Str ℕ → Nested α → Nested α → Nested α
  | [], i, _ => i
  | n :: S, i, L => setChild n (modify S i (child L n)) L

variable [Inhabited α] (L i : Nested α) (n : ℕ) (S T : Str ℕ)

/-- `L@nil = L`. -/
theorem idx_nil : idx L Str.nil = L := rfl

/-- `L@n = L n`. -/
theorem idx_item : idx L (Str.item n) = child L n := rfl

/-- `L@(S; T) = L@S@T`. -/
theorem idx_append : idx L (S ++ T) = idx (idx L S) T := by
  induction S generalizing L with
  | nil => rfl
  | cons n S ih => exact ih (child L n)

/-- `nil→i | L = i`. -/
theorem modify_nil : modify Str.nil i L = i := rfl

/-- `(S; T)→i | L = S→(T→i | L@S) | L`. -/
theorem modify_append : modify (S ++ T) i L = modify S (modify T i (idx L S)) L := by
  induction S generalizing L with
  | nil => rfl
  | cons n S ih => simp only [List.cons_append, modify, idx, ih]

/-- The book's `B = [[2; 3]; 4; [5; [6; 7]]]`. -/
def exampleB : Nested ℕ :=
  list [list [item 2, item 3], item 4, list [item 5, list [item 6, item 7]]]

/-- `B 0 0 = 2`. -/
theorem exampleB_zero_zero : child (child exampleB 0) 0 = item 2 := rfl

/-- `B 1 = 4`. -/
theorem exampleB_one : child exampleB 1 = item 4 := rfl

/-- "`B 1 1` is undefined": indexing the item `4` again gives only the default. -/
theorem exampleB_one_one : child (child exampleB 1) 1 = default := rfl

/-- `B@(2; 1; 0) = B 2 1 0 = 6`. -/
theorem exampleB_idx : idx exampleB [2, 1, 0] = item 6 := rfl

/-- `(0;1)→6 | [[0; 1; 2]; [3; 4; 5]] = [[0; 6; 2]; [3; 4; 5]]`. -/
theorem modify_example :
    modify [0, 1] (item 6) (list [list [item 0, item 1, item 2], list [item 3, item 4, item 5]]) =
      list [list [item 0, item 6, item 2], list [item 3, item 4, item 5]] := rfl

/-- A list of items is a nested structure, and its indexing agrees with `L n`. -/
def ofHList (L : HList α) : Nested α := list (L.contents.map item)

theorem child_ofHList (L : HList α) (n : ℕ) : child (ofHList L) n = item (L.at n) := by
  simp only [child, ofHList, HList.at, Str.at]
  rcases h : L.contents[n]? with _ | a
  · simp [List.getD_eq_getElem?_getD, h]; rfl
  · simp [List.getD_eq_getElem?_getD, h]

end Nested

end LaPToP.DataStructures
