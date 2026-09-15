import LaPToP.TheoryDesign.Stack

/-!
# Data-queue theory and its implementation

This module formalizes Section 7.0.3 (Data-Queue Theory) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), together with the list
implementation the book leaves as Exercise 426.

"The queue data structure, also known as a buffer ... is the structure with
the motto: the first one in is the first one out. We introduce the syntax
`queue`, `emptyq`, `join`, `leave`, and `front`." The axioms are the
construction axioms `emptyq: queue`, `join q x: queue`, the "distinct queues"
axioms, queue induction, and the four "first in, first out" axioms. The
typing axioms `q⧧emptyq ⇒ leave q: queue` and `q⧧emptyq ⇒ front q: X` "can now
be proved" from induction — and are automatic for a carrier type.
-/

namespace LaPToP.TheoryDesign

open LaPToP.DataStructures

universe u v

/-- A *data-queue theory* over items `X` (aPToP §7.0.3). -/
structure DataQueueTheory (X : Type u) where
  /-- `queue`, "a bunch consisting of all queues of items of type `X`". -/
  Queue : Type v
  /-- `emptyq: queue`, "a queue containing no items". -/
  emptyq : Queue
  /-- `join: queue→X→queue`, "the queue containing the same items plus the one new item". -/
  join : Queue → X → Queue
  /-- `leave`, "the queue minus the oldest remaining item". -/
  leave : Queue → Queue
  /-- `front`, "the oldest remaining item". -/
  front : Queue → X
  /-- Queue induction: `emptyq, join B X: B ⇒ queue: B`. -/
  induction : ∀ P : Queue → Prop, P emptyq → (∀ q x, P q → P (join q x)) → ∀ q, P q
  /-- `join q x ⧧ emptyq`. -/
  join_ne_emptyq : ∀ q x, join q x ≠ emptyq
  /-- `join q x = join r y = q=r ∧ x=y`. -/
  join_inj : ∀ q r x y, join q x = join r y ↔ q = r ∧ x = y
  /-- `leave (join emptyq x) = emptyq`. -/
  leave_join_emptyq : ∀ x, leave (join emptyq x) = emptyq
  /-- `q⧧emptyq ⇒ leave (join q x) = join (leave q) x`. -/
  leave_join : ∀ q x, q ≠ emptyq → leave (join q x) = join (leave q) x
  /-- `front (join emptyq x) = x`. -/
  front_join_emptyq : ∀ x, front (join emptyq x) = x
  /-- `q⧧emptyq ⇒ front (join q x) = front q`. -/
  front_join : ∀ q x, q ≠ emptyq → front (join q x) = front q

namespace DataQueueTheory

variable {X : Type u} (T : DataQueueTheory X)

/-- Every queue is `emptyq` or a `join`. -/
theorem eq_emptyq_or_join (q : T.Queue) : q = T.emptyq ∨ ∃ r x, q = T.join r x :=
  T.induction (fun q => q = T.emptyq ∨ ∃ r x, q = T.join r x) (Or.inl rfl)
    (fun q x _ => Or.inr ⟨q, x, rfl⟩) q

/-- Joining items to a nonempty queue does not change its front: the FIFO
character, iterated. -/
theorem front_foldl (l : List X) (q : T.Queue) (hq : q ≠ T.emptyq) :
    T.front (l.foldl T.join q) = T.front q := by
  induction l generalizing q with
  | nil => rfl
  | cons y l ih =>
    rw [List.foldl_cons, ih (T.join q y) (T.join_ne_emptyq q y), T.front_join q y hq]

/-- "The first one in is the first one out": the item joined to the empty queue
stays at the front whatever is joined afterwards. -/
theorem front_joins (x : X) (l : List X) : T.front (l.foldl T.join (T.join T.emptyq x)) = x := by
  rw [front_foldl T l _ (T.join_ne_emptyq _ _), T.front_join_emptyq]

end DataQueueTheory

/-! ### Data-queue implementation by lists (Exercise 426) -/

namespace ListQueue

/-- `emptyq = [nil]`. -/
def emptyq : HList ℤ := Str.pack []

/-- `join q x = q;;[x]`: the new item goes to the back. -/
def join (q : HList ℤ) (x : ℤ) : HList ℤ := HList.join q (Str.pack [x])

/-- `leave q = q [1;..#q]`: drop the front item (`leave emptyq = emptyq`). -/
def leave (q : HList ℤ) : HList ℤ := ⟨q.contents.tail⟩

/-- `front q = q 0` (`front emptyq = 0`). -/
def front (q : HList ℤ) : ℤ := q.contents.headD 0

/-- `join q x ⧧ emptyq`. -/
theorem join_ne_emptyq (q : HList ℤ) (x : ℤ) : join q x ≠ emptyq := ListStack.push_ne_empty q x

/-- Lists implement data-queue theory. -/
def theory : DataQueueTheory ℤ where
  Queue := HList ℤ
  emptyq := emptyq
  join := join
  leave := leave
  front := front
  induction := ListStack.induction
  join_ne_emptyq := join_ne_emptyq
  join_inj := ListStack.push_inj
  leave_join_emptyq _ := rfl
  leave_join q x hq := by
    have hne : q.contents ≠ [] := fun h => hq (HList.ext h)
    exact HList.ext (List.tail_append_of_ne_nil hne)
  front_join_emptyq _ := rfl
  front_join q x hq := by
    obtain ⟨l⟩ := q
    cases l with
    | nil => exact absurd rfl hq
    | cons a l => rfl

end ListQueue

end LaPToP.TheoryDesign
