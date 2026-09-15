import LaPToP.TheoryDesign.Stack

/-!
# Simple data-stack theory

This module formalizes Section 7.0.2 (Simple Data-Stack Theory) of Eric
Hehner's *A Practical Theory of Programming* (aPToP).

"For most purposes, it is sufficient to be able to push items onto a stack,
pop items off, and look at the top item. The theory we need is considerably
simpler than the one presented previously. Our simpler data-stack theory
introduces the names `stack`, `push`, `pop`, and `top` with the following
four axioms: `stack ⧧ null`, `push s x: stack`, `pop (push s x) = s`,
`top (push s x) = x`."

The design remarks are made concrete: every data-stack theory is a simple
one (forgetting `empty` and the extra axioms), the list implementation is a
model, and there is a model with *no* empty stack at all — infinite stacks
(streams) `ℕ → X`, in which every stack is a `push` — "we never need an empty
stack, nor to test if a stack is empty".
-/

namespace LaPToP.TheoryDesign

universe u v

/-- The *simple data-stack theory* (aPToP §7.0.2): `stack ⧧ null`,
`push s x: stack`, `pop (push s x) = s`, `top (push s x) = x`. -/
structure SimpleStackTheory (X : Type u) where
  /-- `stack`. -/
  Stack : Type v
  /-- `stack ⧧ null`, "so that we can still declare variables of type stack". -/
  nonempty : Nonempty Stack
  /-- `push s x: stack`. -/
  push : Stack → X → Stack
  /-- `pop`; the book drops `pop: stack→stack` so that `pop empty` need not be provided. -/
  pop : Stack → Stack
  /-- `top`; likewise `top: stack→X` is dropped. -/
  top : Stack → X
  /-- `pop (push s x) = s`. -/
  pop_push : ∀ s x, pop (push s x) = s
  /-- `top (push s x) = x`. -/
  top_push : ∀ s x, top (push s x) = x

namespace SimpleStackTheory

variable {X : Type u}

/-- Every data-stack theory is a simple data-stack theory: the simple theory is weaker. -/
def ofDataStack (T : DataStackTheory X) : SimpleStackTheory X where
  Stack := T.Stack
  nonempty := ⟨T.empty⟩
  push := T.push
  pop := T.pop
  top := T.top
  pop_push := T.pop_push
  top_push := T.top_push

/-- The list implementation is a model of the simple theory. -/
def listModel : SimpleStackTheory ℤ := ofDataStack ListStack.theory

/-- The stream model: stacks are infinite sequences `ℕ → X`; `push` prepends,
`pop` drops the head, `top` is the head. -/
def streamModel (X : Type u) [Inhabited X] : SimpleStackTheory X where
  Stack := ℕ → X
  nonempty := ⟨fun _ => default⟩
  push s x := fun n => match n with
    | 0 => x
    | n + 1 => s n
  pop s := fun n => s (n + 1)
  top s := s 0
  pop_push _ _ := rfl
  top_push _ _ := rfl

/-- In the stream model every stack is a `push`: there is no empty stack, so
the strong axiom `push s x ⧧ empty` could not hold for any choice of `empty`.
"As long as we are given some tree [stack], we can build" what we need. -/
theorem streamModel_every_push (X : Type u) [Inhabited X] (e : (streamModel X).Stack) :
    ∃ s x, (streamModel X).push s x = e :=
  ⟨fun n => e (n + 1), e 0, funext fun n => by cases n <;> rfl⟩

end SimpleStackTheory

end LaPToP.TheoryDesign
