import LaPToP.DataStructures.Lists
import LaPToP.RecursiveDefinition.Nat
import Mathlib.Data.List.Induction

/-!
# Data-stack theory and its implementation

This module formalizes Section 7.0.0 (Data-Stack Theory) and Section 7.0.1
(Data-Stack Implementation) of Eric Hehner's *A Practical Theory of
Programming* (aPToP).

## The model

"We introduce the syntax `stack`, `empty`, `push`, `pop`, and `top`", with
axioms `empty: stack`, `push: stack→X→stack`, `pop: stack→stack`,
`top: stack→X`, a construction axiom, an induction axiom, two axioms saying
that the constructors construct different stacks, and two axioms for
"last in, first out". A *theory* is modelled as a Lean structure
`DataStackTheory X`: a carrier type `Stack` (the bunch `stack` — a type,
so that `push: stack→X→stack` is total on it) with the four operations and
the axioms as fields. The construction axiom `empty, push stack X: stack` is
automatic for a type and is recorded as such; the predicate forms of
construction and induction are the book's.

"To prove that a theory is implemented, we prove (the axioms of the theory)
⇐ (the definitions of the implementation)": the implementation by lists —
`stack = [*int]`, `empty = [nil]`, `push s x = s;;[x]`,
`pop s = if s=empty then empty else s [0;..#s–1]`,
`top s = if s=empty then 0 else s (#s–1)` — is a term of type
`DataStackTheory ℤ`, whose fields are exactly those proofs.

Incompleteness: `pop empty = empty` and `top empty = 0` hold in this
implementation but fail in the book's alternative one (`pop empty = push
empty 0`, `top empty = 1`), which also satisfies the axioms; so the theory
neither proves nor refutes them. "A theory is a contract between two parties,
an implementer and a user."
-/

namespace LaPToP.TheoryDesign

open LaPToP.BasicTheories LaPToP.DataStructures

universe u v

/-- A *data-stack theory* over items `X` (aPToP §7.0.0): the syntax `stack`,
`empty`, `push`, `pop`, `top` together with the data-stack axioms. -/
structure DataStackTheory (X : Type u) where
  /-- `stack`, "a bunch consisting of all stacks of items of type `X`". -/
  Stack : Type v
  /-- `empty: stack`, "a stack containing no items". -/
  empty : Stack
  /-- `push: stack→X→stack`, "the stack containing the same items plus the one new item". -/
  push : Stack → X → Stack
  /-- `pop: stack→stack`, "the stack minus the newest remaining item". -/
  pop : Stack → Stack
  /-- `top: stack→X`, "the newest remaining item". -/
  top : Stack → X
  /-- Induction: `P empty ∧ (∀s: stack· ∀x: X· P s ⇒ P (push s x)) ⇒ ∀s: stack· P s`
  — "to exclude anything else from being a stack". -/
  induction : ∀ P : Stack → Prop, P empty → (∀ s x, P s → P (push s x)) → ∀ s, P s
  /-- `push s x ⧧ empty`: "the constructors always construct different stacks". -/
  push_ne_empty : ∀ s x, push s x ≠ empty
  /-- `push s x = push t y = s=t ∧ x=y`. -/
  push_inj : ∀ s t x y, push s x = push t y ↔ s = t ∧ x = y
  /-- `pop (push s x) = s` ("last in, first out"). -/
  pop_push : ∀ s x, pop (push s x) = s
  /-- `top (push s x) = x` ("last in, first out"). -/
  top_push : ∀ s x, top (push s x) = x

namespace DataStackTheory

variable {X : Type u} (T : DataStackTheory X)

/-- The construction axiom `empty, push stack X: stack`: automatic, since the
carrier is a type. -/
theorem construction (s : T.Stack) (x : X) : T.push s x ∈ (Set.univ : Bunch T.Stack) := Set.mem_univ _

/-- The predicate form of construction:
`P empty ∧ (∀s: stack· ∀x: X· P s ⇒ P (push s x)) ⇐ ∀s: stack· P s`. -/
theorem construction_pred (P : T.Stack → Prop) (h : ∀ s, P s) :
    P T.empty ∧ ∀ s x, P s → P (T.push s x) :=
  ⟨h _, fun _s _x _ => h _⟩

/-- The bunch form of induction: `empty, push B X: B ⇒ stack: B`. -/
theorem induction_bunch (B : Bunch T.Stack) (h0 : T.empty ∈ B) (hs : ∀ s ∈ B, ∀ x, T.push s x ∈ B) :
    (Set.univ : Bunch T.Stack) ⊆ B :=
  fun s _ => T.induction (· ∈ B) h0 (fun s x hs' => hs s hs' x) s

/-- Every stack is `empty` or a `push`. -/
theorem eq_empty_or_push (s : T.Stack) : s = T.empty ∨ ∃ t x, s = T.push t x :=
  T.induction (fun s => s = T.empty ∨ ∃ t x, s = T.push t x) (Or.inl rfl)
    (fun s x _ => Or.inr ⟨s, x, rfl⟩) s

/-- `push` is injective in both arguments — a consequence of the LIFO axioms
alone (`pop` and `top` recover the arguments), so the second "different
stacks" axiom is derivable from them. -/
theorem push_inj_of_lifo (s t : T.Stack) (x y : X) (h : T.push s x = T.push t y) : s = t ∧ x = y :=
  ⟨by rw [← T.pop_push s x, h, T.pop_push], by rw [← T.top_push s x, h, T.top_push]⟩

end DataStackTheory

/-! ### "It is possible that all stacks are equal" (aPToP §7.0.0)

"According to the axioms we have so far" — the four typing axioms,
construction and induction, before the two "different stacks" axioms and the
two LIFO axioms — "it is possible that all stacks are equal": a one-element
carrier satisfies them. -/

/-- The first six axioms of data-stack theory: typing, construction (automatic)
and induction. -/
structure WeakStackTheory (X : Type u) where
  /-- The carrier. -/
  Stack : Type v
  /-- `empty`. -/
  empty : Stack
  /-- `push`. -/
  push : Stack → X → Stack
  /-- `pop`. -/
  pop : Stack → Stack
  /-- `top`. -/
  top : Stack → X
  /-- Induction. -/
  induction : ∀ P : Stack → Prop, P empty → (∀ s x, P s → P (push s x)) → ∀ s, P s

/-- Every data-stack theory is in particular a weak one. -/
def DataStackTheory.toWeak {X : Type u} (T : DataStackTheory X) : WeakStackTheory X :=
  ⟨T.Stack, T.empty, T.push, T.pop, T.top, T.induction⟩

/-- The one-element model of the weak axioms, in which all stacks are equal. -/
def unitStack (X : Type u) [Inhabited X] : WeakStackTheory X where
  Stack := Unit
  empty := ()
  push _ _ := ()
  pop _ := ()
  top _ := default
  induction _ h0 _ _ := h0

/-- In the one-element model `push s x = empty`: the "different stacks" axiom
`push s x ⧧ empty` is not a consequence of the weak axioms. -/
theorem unitStack_push_eq_empty (X : Type u) [Inhabited X] (s : (unitStack X).Stack) (x : X) :
    (unitStack X).push s x = (unitStack X).empty := rfl

/-! ### Data-stack implementation by lists (aPToP §7.0.1)

"Suppose that lists and functions are implemented. Then we can implement a
stack of integers by the following definitions: `stack = [*int]`,
`empty = [nil]`, `push = ⟨s: stack· ⟨x: int· s;;[x]⟩⟩`,
`pop = ⟨s: stack· if s=empty then empty else s [0;..#s–1]⟩`,
`top = ⟨s: stack· if s=empty then 0 else s (#s–1)⟩`." -/

namespace ListStack

/-- `empty = [nil]`. -/
def empty : HList ℤ := Str.pack []

/-- `push s x = s;;[x]`. -/
def push (s : HList ℤ) (x : ℤ) : HList ℤ := HList.join s (Str.pack [x])

/-- `pop s = if s=empty then empty else s [0;..#s–1]`. -/
def pop (s : HList ℤ) : HList ℤ := if s = empty then empty else ⟨s.contents.dropLast⟩

/-- `top s = if s=empty then 0 else s (#s–1)`. -/
def top (s : HList ℤ) : ℤ := if s = empty then 0 else s.at (s.contents.length - 1)

/-- `push s x = ⟨s.contents ++ [x]⟩`. -/
theorem push_contents (s : HList ℤ) (x : ℤ) : (push s x).contents = s.contents ++ [x] := rfl

/-- `push s x ⧧ empty`. -/
theorem push_ne_empty (s : HList ℤ) (x : ℤ) : push s x ≠ empty := fun h =>
  List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil x []) (congrArg HList.contents h)

/-- Induction for lists viewed as stacks: from the right. -/
theorem induction (P : HList ℤ → Prop) (h0 : P empty) (hs : ∀ s x, P s → P (push s x)) (s : HList ℤ) :
    P s := by
  obtain ⟨l⟩ := s
  induction l using List.reverseRecOn with
  | nil => exact h0
  | append_singleton l x ih => exact hs ⟨l⟩ x ih

/-- `pop (push s x) = s`: "index the list". -/
theorem pop_push (s : HList ℤ) (x : ℤ) : pop (push s x) = s := by
  rw [pop, if_neg (push_ne_empty s x)]
  exact HList.ext (List.dropLast_concat)

/-- `top (push s x) = x`, the book's worked calculation. -/
theorem top_push (s : HList ℤ) (x : ℤ) : top (push s x) = x := by
  rw [top, if_neg (push_ne_empty s x)]
  simp [push_contents, HList.at, Str.at, List.getD_eq_getElem?_getD]

/-- `push s x = push t y = s=t ∧ x=y`. -/
theorem push_inj (s t : HList ℤ) (x y : ℤ) : push s x = push t y ↔ s = t ∧ x = y := by
  constructor
  · intro h
    have h' := congrArg HList.contents h
    simp only [push_contents] at h'
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    exact ⟨HList.ext h1, List.singleton_inj.1 h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- "The definitions must satisfy the axioms": lists implement data-stack theory. -/
def theory : DataStackTheory ℤ where
  Stack := HList ℤ
  empty := empty
  push := push
  pop := pop
  top := top
  induction := induction
  push_ne_empty := push_ne_empty
  push_inj := push_inj
  pop_push := pop_push
  top_push := top_push

/-- `pop empty = empty` is a theorem of this implementation ... -/
theorem pop_empty : pop empty = empty := if_pos rfl

/-- ... and so is `top empty = 0`. -/
theorem top_empty : top empty = 0 := if_pos rfl

end ListStack

/-! ### Incompleteness (aPToP §7.0.1)

"To show that a binary expression is unclassified, we must implement stacks
twice, making the expression a theorem in one implementation, and an
antitheorem in the other." -/

namespace ListStack'

/-- The alternative `pop = ⟨s: stack· if s=empty then push empty 0 else s [0;..#s–1]⟩`. -/
def pop (s : HList ℤ) : HList ℤ := if s = ListStack.empty then ListStack.push ListStack.empty 0 else ⟨s.contents.dropLast⟩

/-- The alternative `top = ⟨s: stack· if s=empty then 1 else s (#s–1)⟩`. -/
def top (s : HList ℤ) : ℤ := if s = ListStack.empty then 1 else s.at (s.contents.length - 1)

/-- The alternative implementation also satisfies the axioms. -/
def theory : DataStackTheory ℤ where
  Stack := HList ℤ
  empty := ListStack.empty
  push := ListStack.push
  pop := pop
  top := top
  induction := ListStack.induction
  push_ne_empty := ListStack.push_ne_empty
  push_inj := ListStack.push_inj
  pop_push s x := by
    rw [pop, if_neg (ListStack.push_ne_empty s x)]
    exact HList.ext List.dropLast_concat
  top_push s x := by
    rw [top, if_neg (ListStack.push_ne_empty s x)]
    simp [ListStack.push_contents, HList.at, Str.at, List.getD_eq_getElem?_getD]

/-- In the alternative implementation `pop empty ⧧ empty` ... -/
theorem pop_empty_ne : pop ListStack.empty ≠ ListStack.empty := by
  rw [pop, if_pos rfl]; exact ListStack.push_ne_empty _ _

/-- ... and `top empty ⧧ 0`. -/
theorem top_empty_ne : top ListStack.empty ≠ 0 := by
  rw [top, if_pos rfl]; decide

end ListStack'

/-- "So stack theory is incomplete": `pop empty = empty` is neither a theorem
nor an antitheorem of data-stack theory — it holds in one model and fails in
another. -/
theorem pop_empty_unclassified :
    ¬ (∀ T : DataStackTheory.{0, 0} ℤ, T.pop T.empty = T.empty) ∧
      ¬ (∀ T : DataStackTheory.{0, 0} ℤ, T.pop T.empty ≠ T.empty) :=
  ⟨fun h => ListStack'.pop_empty_ne (h ListStack'.theory),
    fun h => h ListStack.theory ListStack.pop_empty⟩

/-- Likewise for `top empty = 0`. -/
theorem top_empty_unclassified :
    ¬ (∀ T : DataStackTheory.{0, 0} ℤ, T.top T.empty = 0) ∧
      ¬ (∀ T : DataStackTheory.{0, 0} ℤ, T.top T.empty ≠ 0) :=
  ⟨fun h => ListStack'.top_empty_ne (h ListStack'.theory), fun h => h ListStack.theory ListStack.top_empty⟩

end LaPToP.TheoryDesign
