import LaPToP.TheoryDesign.Stack

/-!
# Data-tree theory and its implementation

This module formalizes Section 7.0.4 (Data-Tree Theory) and Section 7.0.5
(Data-Tree Implementation) of Eric Hehner's *A Practical Theory of
Programming* (aPToP).

"We introduce the syntax `tree`, `emptree`, `graft`, `left`, `right`, `root`
... For the purpose of studying trees, we want a strong theory": construction,
induction `emptree, graft B X B: B ⇒ tree: B`, the two "distinct trees" axioms,
and `left (graft t x u) = t`, `root (graft t x u) = x`, `right (graft t x u) = u`.
"For most programming purposes, the following simpler, weaker theory is
sufficient": `tree ⧧ null`, `graft t x u: tree`, and the three selector axioms.

The book implements trees of integers by nested lists — `emptree = [nil]`,
`graft t x u = [t; x; u]`, `left t = t 0`, `root t = t 1`, `right t = t 2` —
which mixes lists and integers as items and so is not expressible with the
homogeneous `HList ℤ` of this formalization; the implementation given here is
the inductive type `BinTree X` (the recursive data definition
`tree = emptree, graft tree X tree` taken as a datatype), with the selectors
returning the argument on `emptree`. Both `left`/`right`/`root` of `emptree`
are left unspecified by the theory, exactly as `pop empty` is for stacks.
-/

namespace LaPToP.TheoryDesign

universe u v

/-- A *data-tree theory* over items `X` (aPToP §7.0.4), "a strong theory". -/
structure DataTreeTheory (X : Type u) where
  /-- `tree`, "a bunch consisting of all finite binary trees of items of type `X`". -/
  Tree : Type v
  /-- `emptree: tree`, "a tree containing no items". -/
  emptree : Tree
  /-- `graft: tree→X→tree→tree`, "the tree with the item at the root and the two given
  trees as left and right subtree". -/
  graft : Tree → X → Tree → Tree
  /-- `left`, the left subtree. -/
  left : Tree → Tree
  /-- `right`, the right subtree. -/
  right : Tree → Tree
  /-- `root`, the root item. -/
  root : Tree → X
  /-- Tree induction: `emptree, graft B X B: B ⇒ tree: B`. -/
  induction : ∀ P : Tree → Prop, P emptree → (∀ t x u, P t → P u → P (graft t x u)) → ∀ t, P t
  /-- `graft t x u ⧧ emptree`. -/
  graft_ne_emptree : ∀ t x u, graft t x u ≠ emptree
  /-- `graft t x u = graft v y w = t=v ∧ x=y ∧ u=w`. -/
  graft_inj : ∀ t x u v y w, graft t x u = graft v y w ↔ t = v ∧ x = y ∧ u = w
  /-- `left (graft t x u) = t`. -/
  left_graft : ∀ t x u, left (graft t x u) = t
  /-- `root (graft t x u) = x`. -/
  root_graft : ∀ t x u, root (graft t x u) = x
  /-- `right (graft t x u) = u`. -/
  right_graft : ∀ t x u, right (graft t x u) = u

/-- The "simpler, weaker" data-tree theory: `tree ⧧ null`, `graft t x u: tree`,
and the three selector axioms — "we don't really need to be given an empty
tree ... and we probably don't need tree induction". -/
structure SimpleTreeTheory (X : Type u) where
  /-- `tree`. -/
  Tree : Type v
  /-- `tree ⧧ null`. -/
  nonempty : Nonempty Tree
  /-- `graft`. -/
  graft : Tree → X → Tree → Tree
  /-- `left`. -/
  left : Tree → Tree
  /-- `right`. -/
  right : Tree → Tree
  /-- `root`. -/
  root : Tree → X
  /-- `left (graft t x u) = t`. -/
  left_graft : ∀ t x u, left (graft t x u) = t
  /-- `root (graft t x u) = x`. -/
  root_graft : ∀ t x u, root (graft t x u) = x
  /-- `right (graft t x u) = u`. -/
  right_graft : ∀ t x u, right (graft t x u) = u

namespace DataTreeTheory

variable {X : Type u} (T : DataTreeTheory X)

/-- Every tree is `emptree` or a `graft`. -/
theorem eq_emptree_or_graft (t : T.Tree) : t = T.emptree ∨ ∃ l x r, t = T.graft l x r :=
  T.induction (fun t => t = T.emptree ∨ ∃ l x r, t = T.graft l x r) (Or.inl rfl)
    (fun l x r _ _ => Or.inr ⟨l, x, r, rfl⟩) t

/-- The selector axioms alone make `graft` injective, so the second "distinct
trees" axiom is derivable from them. -/
theorem graft_inj_of_selectors (t u v w : T.Tree) (x y : X) (h : T.graft t x u = T.graft v y w) :
    t = v ∧ x = y ∧ u = w :=
  ⟨by rw [← T.left_graft t x u, h, T.left_graft], by rw [← T.root_graft t x u, h, T.root_graft],
    by rw [← T.right_graft t x u, h, T.right_graft]⟩

/-- Every data-tree theory is a simple one. -/
def toSimple : SimpleTreeTheory X where
  Tree := T.Tree
  nonempty := ⟨T.emptree⟩
  graft := T.graft
  left := T.left
  right := T.right
  root := T.root
  left_graft := T.left_graft
  root_graft := T.root_graft
  right_graft := T.right_graft

end DataTreeTheory

/-! ### Implementation by an inductive type (aPToP §7.0.5) -/

/-- Finite binary trees of items of type `X`: the recursive data definition
`tree = emptree, graft tree X tree` as a datatype. -/
inductive BinTree (X : Type u)
  /-- `emptree`. -/
  | emptree : BinTree X
  /-- `graft t x u`. -/
  | graft (l : BinTree X) (x : X) (r : BinTree X) : BinTree X

namespace BinTree

variable {X : Type u}

/-- `left`; on `emptree` the theory says nothing, and we return `emptree`. -/
def left : BinTree X → BinTree X
  | emptree => emptree
  | graft l _ _ => l

/-- `right`; on `emptree` we return `emptree`. -/
def right : BinTree X → BinTree X
  | emptree => emptree
  | graft _ _ r => r

/-- `root`; on `emptree` we return the default item. -/
def root [Inhabited X] : BinTree X → X
  | emptree => default
  | graft _ x _ => x

/-- Binary trees implement data-tree theory. -/
def theory (X : Type u) [Inhabited X] : DataTreeTheory X where
  Tree := BinTree X
  emptree := emptree
  graft := graft
  left := left
  right := right
  root := root
  induction P h0 hs t := by
    induction t with
    | emptree => exact h0
    | graft l x r ihl ihr => exact hs l x r ihl ihr
  graft_ne_emptree _ _ _ := fun h => by cases h
  graft_inj _ _ _ _ _ _ := by simp
  left_graft _ _ _ := rfl
  root_graft _ _ _ := rfl
  right_graft _ _ _ := rfl

/-- The book's example tree `[[[nil]; 2; [[nil]; 5; [nil]]]; 3; [[nil]; 7; [nil]]]`. -/
def example₁ : BinTree ℤ :=
  graft (graft emptree 2 (graft emptree 5 emptree)) 3 (graft emptree 7 emptree)

/-- Its root is `3` and the root of its left subtree is `2`. -/
theorem example₁_roots : example₁.root = 3 ∧ example₁.left.root = 2 := ⟨rfl, rfl⟩

end BinTree

end LaPToP.TheoryDesign
