import LaPToP.TheoryDesign.ProgramStack

/-!
# Program-queue and program-tree theories

This module formalizes Section 7.1.4 (Program-Queue Theory) and the axioms
of Section 7.1.5 (Program-Tree Theory) of Eric Hehner's *A Practical Theory
of Programming* (aPToP).

"Program-queue theory introduces five names: `mkemptyq` (a program to make the
queue empty), `isemptyq` (a binary variable to say whether the queue is
empty), `join` (a procedure with parameter of type `X`), `leave` (a program),
and `front` (of type `X`). The axioms are

    isemptyq′ ⇐ mkemptyq
    isemptyq ⇒ front′=x ∧ ¬isemptyq′ ⇐ join x
    ¬isemptyq ⇒ front′=front ∧ ¬isemptyq′ ⇐ join x
    isemptyq ⇒ (join x. leave = mkemptyq)
    ¬isemptyq ⇒ (join x. leave = leave. join x)"

## The model

As for program-stack theory (`LaPToP.TheoryDesign.ProgramStack`), the theory
is a structure over a state type `σ`. The first three axioms are refinements.
The last two, `b ⇒ (P = Q)`, assert the equality of two specifications
whenever the initial state satisfies `b`; they are stated pointwise, as
`∀ s s′, b s → (P s s′ ↔ Q s s′)`. The list implementation `mkemptyq = q:= [nil]`,
`isemptyq = (q = [nil])`, `join x = q:= q;;[x]`, `leave = q:= q[1;..#q]`,
`front = q 0` is proved to satisfy all five axioms (the book gives no
implementation in this section; the data-queue implementation of Section
7.0.3 suggests it), and the first-in-first-out behaviour is derived from the
axioms alone: `join x. join y. leave = join x. leave. join y`, and from an
empty queue `join x. join y. leave = mkemptyq. join y`, after which the front
is `y`.

Program-tree theory (Section 7.1.5) is given here only as the structure of
its first, axiomatic definition — `node`, `aim`, `go`, the assignments to
`node` and `aim`, and the auxiliary specification `work`, "which helps in
writing the axioms, but is not an addition to the theory, and does not need
to be implemented". No implementation is given; the second definition by
implementer's variables `T`, `p` (with `T@(p; 1)`) is not formalized.
-/

namespace LaPToP.TheoryDesign

open LaPToP.DataStructures LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

universe u v

/-- *Program-queue theory* (aPToP §7.1.4): `mkemptyq`, `isemptyq`, `join`, `leave`,
`front` with the five axioms. -/
structure ProgramQueueTheory (X : Type u) (σ : Type v) where
  /-- `mkemptyq`, "a program to make the queue empty". -/
  mkemptyq : Spec σ
  /-- `isemptyq`, "a binary variable to say whether the queue is empty". -/
  isemptyq : σ → Prop
  /-- `join x`, "a procedure with parameter of type `X`". -/
  join : X → Spec σ
  /-- `leave`, "a program". -/
  leave : Spec σ
  /-- `front`, a state variable "of type `X`". -/
  front : σ → X
  /-- `isemptyq′ ⇐ mkemptyq`. -/
  isemptyq_mkemptyq : Refines (fun _ s' => isemptyq s') mkemptyq
  /-- `isemptyq ⇒ front′=x ∧ ¬isemptyq′ ⇐ join x`. -/
  join_empty : ∀ x, Refines (fun s s' => isemptyq s → front s' = x ∧ ¬ isemptyq s') (join x)
  /-- `¬isemptyq ⇒ front′=front ∧ ¬isemptyq′ ⇐ join x`. -/
  join_nonempty : ∀ x, Refines (fun s s' => ¬ isemptyq s → front s' = front s ∧ ¬ isemptyq s') (join x)
  /-- `isemptyq ⇒ (join x. leave = mkemptyq)`, pointwise. -/
  join_leave_empty : ∀ x s s', isemptyq s → (seq (join x) leave s s' ↔ mkemptyq s s')
  /-- `¬isemptyq ⇒ (join x. leave = leave. join x)`, pointwise. -/
  join_leave_nonempty : ∀ x s s', ¬ isemptyq s → (seq (join x) leave s s' ↔ seq leave (join x) s s')

namespace ProgramQueueTheory

variable {X : Type u} {σ : Type v} (T : ProgramQueueTheory X σ)

/-- `¬isemptyq′ ⇐ join x`: joining never leaves the queue empty (from the second
and third axioms by cases). -/
theorem not_isemptyq_join (x : X) : Refines (fun _ s' => ¬ T.isemptyq s') (T.join x) := by
  intro s s' h
  by_cases hs : T.isemptyq s
  · exact (T.join_empty x s s' h hs).2
  · exact (T.join_nonempty x s s' h hs).2

/-- `front′=x ∧ ¬isemptyq′ ⇐ mkemptyq. join x` (Refinement by Steps). -/
theorem front_mkemptyq_join (x : X) :
    Refines (fun _ s' => T.front s' = x ∧ ¬ T.isemptyq s') (seq T.mkemptyq (T.join x)) :=
  fun _ _ ⟨u, hmk, hj⟩ => T.join_empty x u _ hj (T.isemptyq_mkemptyq _ u hmk)

/-- First in, first out: `join x. join y. leave = join x. leave. join y`, since the
queue is not empty after `join x`. -/
theorem join_join_leave (x y : X) (s s' : σ) :
    seq (T.join x) (seq (T.join y) T.leave) s s' ↔ seq (T.join x) (seq T.leave (T.join y)) s s' := by
  constructor
  · rintro ⟨u, hx, h⟩
    exact ⟨u, hx, (T.join_leave_nonempty y u s' (T.not_isemptyq_join x s u hx)).mp h⟩
  · rintro ⟨u, hx, h⟩
    exact ⟨u, hx, (T.join_leave_nonempty y u s' (T.not_isemptyq_join x s u hx)).mpr h⟩

/-- From an empty queue, `join x. join y. leave = mkemptyq. join y`. -/
theorem join_join_leave_empty (x y : X) (s s' : σ) (hs : T.isemptyq s) :
    seq (T.join x) (seq (T.join y) T.leave) s s' ↔ seq T.mkemptyq (T.join y) s s' := by
  rw [join_join_leave, seq_assoc]
  constructor
  · rintro ⟨u, hxl, hy⟩
    exact ⟨u, (T.join_leave_empty x s u hs).mp hxl, hy⟩
  · rintro ⟨u, hmk, hy⟩
    exact ⟨u, (T.join_leave_empty x s u hs).mpr hmk, hy⟩

/-- From an empty queue, after `join x. join y. leave` the front is `y`. -/
theorem front_join_join_leave_empty (x y : X) :
    Refines (fun s s' => T.isemptyq s → T.front s' = y ∧ ¬ T.isemptyq s')
      (seq (T.join x) (seq (T.join y) T.leave)) :=
  fun s s' h hs => T.front_mkemptyq_join y s s' ((T.join_join_leave_empty x y s s' hs).mp h)

end ProgramQueueTheory

/-! ### A list implementation

`q: [*X]`, `mkemptyq = q:= [nil]`, `isemptyq = (q = [nil])`, `join x = q:= q;;[x]`,
`leave = q:= q[1;..#q]`, `front = q 0`. -/

/-- The implementer's state: the variable `q: [*X]`. -/
structure PQ (X : Type u) where
  /-- The implementer's variable `q`. -/
  q : HList X

namespace ListProgramQueue

variable {X : Type u} [Inhabited X]

/-- `mkemptyq = q:= [nil]`. -/
def mkemptyq : Spec (PQ X) := fun _ st' => st' = ⟨Str.pack []⟩

/-- `isemptyq = (q = [nil])`. -/
def isemptyq (st : PQ X) : Prop := st.q = Str.pack []

/-- `join x = q:= q;;[x]`. -/
def join (x : X) : Spec (PQ X) := fun st st' => st' = ⟨HList.join st.q (Str.pack [x])⟩

/-- `leave = q:= q[1;..#q]`. -/
def leave : Spec (PQ X) := fun st st' => st' = ⟨⟨st.q.contents.tail⟩⟩

/-- `front = q 0`. -/
def front (st : PQ X) : X := st.q.at 0

omit [Inhabited X] in
theorem isemptyq_iff (st : PQ X) : isemptyq st ↔ st.q.contents = [] := by
  obtain ⟨⟨l⟩⟩ := st
  simp [isemptyq, Str.pack]

omit [Inhabited X] in
theorem isemptyq_mkemptyq : Refines (fun _ st' : PQ X => isemptyq st') mkemptyq := by
  rintro _ _ rfl
  rfl

theorem join_empty (x : X) :
    Refines (fun st st' : PQ X => isemptyq st → front st' = x ∧ ¬ isemptyq st') (join x) := by
  rintro st st' rfl h
  rw [isemptyq_iff] at h
  obtain ⟨⟨l⟩⟩ := st
  simp only at h
  subst h
  simp [front, isemptyq_iff, HList.join, HList.at, Str.at, Str.pack]

theorem join_nonempty (x : X) :
    Refines (fun st st' : PQ X => ¬ isemptyq st → front st' = front st ∧ ¬ isemptyq st') (join x) := by
  rintro st st' rfl h
  rw [isemptyq_iff] at h
  obtain ⟨⟨l⟩⟩ := st
  simp only at h
  refine ⟨?_, ?_⟩
  · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil h
    simp [front, HList.join, HList.at, Str.at, Str.pack]
  · simp [isemptyq_iff, HList.join, Str.pack]

omit [Inhabited X] in
theorem join_leave_empty (x : X) (st st' : PQ X) (h : isemptyq st) :
    seq (join x) leave st st' ↔ mkemptyq st st' := by
  rw [isemptyq_iff] at h
  obtain ⟨⟨l⟩⟩ := st
  simp only at h
  subst h
  simp [seq, join, leave, mkemptyq, HList.join, Str.pack]

omit [Inhabited X] in
theorem join_leave_nonempty (x : X) (st st' : PQ X) (h : ¬ isemptyq st) :
    seq (join x) leave st st' ↔ seq leave (join x) st st' := by
  rw [isemptyq_iff] at h
  obtain ⟨⟨l⟩⟩ := st
  simp only at h
  simp [seq, join, leave, HList.join, Str.pack, List.tail_append_of_ne_nil h]

/-- Lists implement program-queue theory. -/
def theory (X : Type u) [Inhabited X] : ProgramQueueTheory X (PQ X) where
  mkemptyq := mkemptyq
  isemptyq := isemptyq
  join := join
  leave := leave
  front := front
  isemptyq_mkemptyq := isemptyq_mkemptyq
  join_empty := join_empty
  join_nonempty := join_nonempty
  join_leave_empty := join_leave_empty
  join_leave_nonempty := join_leave_nonempty

end ListProgramQueue

/-! ### Program-tree theory (aPToP §7.1.5), the axioms -/

/-- The three directions: "up (toward the parent of this node), left (toward the
left child of this node), or right (toward the right child of this node)". -/
inductive Dir where
  /-- Toward the parent. -/
  | up
  /-- Toward the left child. -/
  | left
  /-- Toward the right child. -/
  | right
  deriving DecidableEq

/-- *Program-tree theory* (aPToP §7.1.5), first definition. "Variable `node` (of
type `X`) tells the value of the item where you are, and it can be assigned a
new value. Variable `aim` tells what direction you are facing, and it can be
assigned a new direction. Program `go` moves you to the next node in the
direction you are facing, and turns you facing back the way you came." The
axioms use the auxiliary specification `work`: "Do anything, wander around
changing the values of nodes if you like, but do not go from this node (your
location at the start of `work`) in this direction (the value of variable
`aim` at the start of `work`). End where you started, facing the way you were
facing at the start." -/
structure ProgramTreeTheory (X : Type u) (σ : Type v) where
  /-- `node`, the item where you are. -/
  node : σ → X
  /-- `aim`, the direction you are facing. -/
  aim : σ → Dir
  /-- `node:= x`. -/
  assignNode : X → Spec σ
  /-- `aim:= d`. -/
  assignAim : Dir → Spec σ
  /-- `go`. -/
  go : Spec σ
  /-- `work`, the auxiliary specification. -/
  work : Spec σ
  /-- `(aim′=up) = (aim⧧up) ⇐ go`. -/
  aim_go : Refines (fun s s' => (aim s' = Dir.up) ↔ aim s ≠ Dir.up) go
  /-- `node′=node ∧ aim′=aim ⇐ go. work. go`. -/
  go_work_go : Refines (fun s s' => node s' = node s ∧ aim s' = aim s) (seq go (seq work go))
  /-- `work ⇐ ok`. -/
  work_ok : Refines work ok
  /-- `work ⇐ node:= x`. -/
  work_assignNode : ∀ x, Refines work (assignNode x)
  /-- `work ⇐ a=aim⧧b ∧ (aim:= b. go. work. go. aim:= a)`. -/
  work_turn : ∀ a b, Refines work
    (fun s s' => a = aim s ∧ aim s ≠ b ∧ seq (assignAim b) (seq go (seq work (seq go (assignAim a)))) s s')
  /-- `work ⇐ work. work`. -/
  work_work : Refines work (seq work work)

namespace ProgramTreeTheory

variable {X : Type u} {σ : Type v} (T : ProgramTreeTheory X σ)

/-- Going, changing the node there, and coming back leaves `node` and `aim`
unchanged: `node′=node ∧ aim′=aim ⇐ go. node:= x. go`. -/
theorem go_assignNode_go (x : X) :
    Refines (fun s s' => T.node s' = T.node s ∧ T.aim s' = T.aim s) (seq T.go (seq (T.assignNode x) T.go)) :=
  fun s s' ⟨u, hgo, v, hx, hgo'⟩ => T.go_work_go s s' ⟨u, hgo, v, T.work_assignNode x u v hx, hgo'⟩

/-- Two `go`s with `work` in between (any number of times) return: `work ⇐ work. work`
composes with `go_work_go`. -/
theorem go_work_work_go :
    Refines (fun s s' => T.node s' = T.node s ∧ T.aim s' = T.aim s) (seq T.go (seq (seq T.work T.work) T.go)) :=
  fun s s' ⟨u, hgo, v, hw, hgo'⟩ => T.go_work_go s s' ⟨u, hgo, v, T.work_work u v hw, hgo'⟩

end ProgramTreeTheory

end LaPToP.TheoryDesign
