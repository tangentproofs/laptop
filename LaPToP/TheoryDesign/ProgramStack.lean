import LaPToP.ProgramTheory.Scope
import LaPToP.TheoryDesign.Stack

/-!
# Program-stack theory

This module formalizes Sections 7.1.0–7.1.3 (Program-Stack Theory, its
implementation, and the fancy and weak variants) of Eric Hehner's
*A Practical Theory of Programming* (aPToP).

## The model

A *program theory* speaks about programs and state variables rather than
about a data type: "the simplest version of program-stack theory introduces
three names: `push` (a procedure with parameter of type `X`), `pop` (a
program), and `top` (of type `X`)", with the two axioms `top′=x ⇐ push x` and
`ok ⇐ push x. pop`. Accordingly `ProgramStackTheory X σ` is a structure over a
state type `σ` with `push : X → Spec σ`, `pop : Spec σ`, `top : σ → X` and
the two axioms as refinements. "Users and implementers ... cannot freely see
or change each other's variables": the implementation's state `PS X` consists
of the implementer's variable `s: [*X]` only; user variables would be added
as a product, unchanged by the stack operations.

The derived laws are the book's: "any natural number of pushes are undone by
the same number of pops", and `top′=x ⇐ push x. push y. push z. pop. pop`.
The list implementation `push x = s:= s;;[x]`, `pop = s:= s[0;..#s–1]`,
`top = s(#s–1)` satisfies both axioms — the book proves the first and leaves
the second as Exercise 429. The *fancy* theory adds `mkempty` and `isempty`;
the *weak* theory keeps `top′=x ⇐ push x` but replaces `ok ⇐ push x. pop` by
axioms about an auxiliary specification `balance`. The book's remark that the
weak theory "allows an implementation in which popping does not restore the
implementer's variable `s` ... but instead marks the last item as garbage" is
not formalized here (only the strong list model is given, which is also a
model of the weak theory).
-/

namespace LaPToP.TheoryDesign

open LaPToP.DataStructures LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

universe u v

/-- A specification refines an equal one. -/
theorem refinesOfEq {σ : Type v} {P Q : Spec σ} (h : P = Q) : Refines P Q := fun _ _ hq => h ▸ hq

/-- *Program-stack theory* (aPToP §7.1.0): `push` (a procedure with a parameter),
`pop` (a program), `top` (a variable), with `top′=x ⇐ push x` and `ok ⇐ push x. pop`. -/
structure ProgramStackTheory (X : Type u) (σ : Type v) where
  /-- `push x`, "a procedure with parameter of type `X`". -/
  push : X → Spec σ
  /-- `pop`, "a program". -/
  pop : Spec σ
  /-- `top`, a state variable "of type `X`". -/
  top : σ → X
  /-- `top′=x ⇐ push x`. -/
  top_push : ∀ x, Refines (fun _ s' => top s' = x) (push x)
  /-- `ok ⇐ push x. pop`: "a pop undoes a push". -/
  push_pop : ∀ x, Refines ok (seq (push x) pop)

namespace ProgramStackTheory

variable {X : Type u} {σ : Type v} (T : ProgramStackTheory X σ)

/-- `P ⇐ push x. pop. P`: a push-pop pair before any specification is harmless. -/
theorem push_pop_seq (x : X) (P : Spec σ) : Refines P (seq (T.push x) (seq T.pop P)) := by
  rw [seq_assoc]
  exact refines_trans _ _ _ (refinesOfEq (ok_seq P).symm) (refines_seq_mono (T.push_pop x) (refines_refl P))

/-- `push x₁. (push x₂. (… (push xₙ. ok. pop) …). pop). pop`: `n` pushes followed by `n` pops. -/
def balanced : List X → Spec σ
  | [] => ok
  | x :: xs => seq (T.push x) (seq (balanced xs) T.pop)

/-- "Any natural number of pushes are undone by the same number of pops": `ok ⇐ balanced xs`. -/
theorem ok_refines_balanced (xs : List X) : Refines ok (T.balanced xs) := by
  induction xs with
  | nil => exact refines_refl ok
  | cons x xs ih =>
    refine refines_trans _ _ _ (T.push_pop x) (refines_seq_mono (refines_refl _) ?_)
    exact refines_trans _ _ _ (refinesOfEq (ok_seq T.pop).symm) (refines_seq_mono ih (refines_refl _))

/-- The book's calculation: `ok ⇐ push x. pop = push x. ok. pop ⇐ push x. push y. pop. pop`. -/
theorem ok_refines_push_push_pop_pop (x y : X) :
    Refines ok (seq (T.push x) (seq (T.push y) (seq T.pop T.pop))) := by
  have h := T.ok_refines_balanced [x, y]
  simp only [balanced] at h
  rwa [ok_seq, ← seq_assoc] at h

/-- A balanced block before a specification is harmless: `P ⇐ balanced xs. P`. -/
theorem refines_balanced_seq (xs : List X) (P : Spec σ) : Refines P (seq (T.balanced xs) P) :=
  refines_trans _ _ _ (refinesOfEq (ok_seq P).symm)
    (refines_seq_mono (T.ok_refines_balanced xs) (refines_refl P))

/-- "When we push something onto the stack, we find it there later at the
appropriate time": `top′=x ⇐ push x. push y. push z. pop. pop`. -/
theorem top_push_push_push_pop_pop (x y z : X) :
    Refines (fun _ s' => T.top s' = x)
      (seq (T.push x) (seq (T.push y) (seq (T.push z) (seq T.pop T.pop)))) := by
  refine refines_trans _ _ _ (T.top_push x) ?_
  exact refines_trans _ _ _ (refinesOfEq (seq_ok (T.push x)).symm)
    (refines_seq_mono (refines_refl _) (T.ok_refines_push_push_pop_pop y z))

/-- Any push is eventually visible: `top′=x ⇐ push x. balanced xs`. -/
theorem top_push_balanced (x : X) (xs : List X) :
    Refines (fun _ s' => T.top s' = x) (seq (T.push x) (T.balanced xs)) := by
  refine refines_trans _ _ _ (T.top_push x) ?_
  exact refines_trans _ _ _ (refinesOfEq (seq_ok (T.push x)).symm)
    (refines_seq_mono (refines_refl _) (T.ok_refines_balanced xs))

end ProgramStackTheory

/-! ### Implementation (aPToP §7.1.1)

"To implement program-stack theory, we introduce an implementer's variable
`s: [*X]` and define `push = ⟨x: X· s:= s;;[x]⟩`, `pop = s:= s[0;..#s–1]`,
`top = s(#s–1)`." -/

/-- The implementer's state: the variable `s: [*X]`. -/
structure PS (X : Type u) where
  /-- The implementer's variable `s`. -/
  s : HList X

namespace ListProgramStack

variable {X : Type u} [Inhabited X]

/-- `push x = s:= s;;[x]`. -/
def push (x : X) : Spec (PS X) := fun st st' => st' = ⟨HList.join st.s (Str.pack [x])⟩

/-- `pop = s:= s[0;..#s–1]`. -/
def pop : Spec (PS X) := fun st st' => st' = ⟨⟨st.s.contents.dropLast⟩⟩

/-- `top = s(#s–1)`. -/
def top (st : PS X) : X := st.s.at (st.s.contents.length - 1)

/-- The first axiom, the book's calculation: `(top′=x ⇐ push x) = (s′(#s′–1) = x ⇐ s:= s;;[x]) = ⊤`. -/
theorem top_push (x : X) : Refines (fun _ st' : PS X => top st' = x) (push x) := by
  rintro st st' rfl
  simp [top, HList.join, HList.at, Str.at, Str.pack, List.getD_eq_getElem?_getD]

omit [Inhabited X] in
/-- The second axiom, Exercise 429: `ok ⇐ push x. pop`. -/
theorem push_pop (x : X) : Refines ok (seq (push x) pop) := by
  rintro st st' ⟨_, rfl, rfl⟩
  obtain ⟨⟨l⟩⟩ := st
  show (⟨⟨(l ++ [x]).dropLast⟩⟩ : PS X) = ⟨⟨l⟩⟩
  rw [List.dropLast_concat]

/-- Lists implement program-stack theory. -/
def theory (X : Type u) [Inhabited X] : ProgramStackTheory X (PS X) where
  push := push
  pop := pop
  top := top
  top_push := top_push
  push_pop := push_pop

end ListProgramStack

/-! ### Fancy program-stack theory (aPToP §7.1.2) -/

/-- The fancy theory adds `mkempty` ("a program to make the stack empty") and
`isempty` ("a binary variable to say whether the stack is empty"), with
`top′=x ∧ ¬isempty′ ⇐ push x`, `ok ⇐ push x. pop`, `isempty′ ⇐ mkempty`. -/
structure FancyProgramStackTheory (X : Type u) (σ : Type v) extends ProgramStackTheory X σ where
  /-- `mkempty`, a program. -/
  mkempty : Spec σ
  /-- `isempty`, a binary variable. -/
  isempty : σ → Prop
  /-- `¬isempty′ ⇐ push x` (with `top′=x ⇐ push x` inherited). -/
  not_isempty_push : ∀ x, Refines (fun _ s' => ¬ isempty s') (push x)
  /-- `isempty′ ⇐ mkempty`. -/
  isempty_mkempty : Refines (fun _ s' => isempty s') mkempty

/-- The book's first fancy axiom in one piece: `top′=x ∧ ¬isempty′ ⇐ push x`. -/
theorem FancyProgramStackTheory.top_push_not_isempty {X : Type u} {σ : Type v}
    (T : FancyProgramStackTheory X σ) (x : X) :
    Refines (fun _ s' => T.top s' = x ∧ ¬ T.isempty s') (T.push x) :=
  fun s s' h => ⟨T.top_push x s s' h, T.not_isempty_push x s s' h⟩

namespace ListProgramStack

variable {X : Type u} [Inhabited X]

/-- `mkempty = s:= [nil]`. -/
def mkempty : Spec (PS X) := fun _ st' => st' = ⟨Str.pack []⟩

/-- `isempty = (s = [nil])`. -/
def isempty (st : PS X) : Prop := st.s = Str.pack []

/-- Lists implement the fancy theory too. -/
def fancyTheory (X : Type u) [Inhabited X] : FancyProgramStackTheory X (PS X) where
  toProgramStackTheory := theory X
  mkempty := mkempty
  isempty := isempty
  not_isempty_push x := by
    rintro st st' rfl h
    have h' : st.s.contents ++ [x] = [] := congrArg HList.contents h
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil x []) h'
  isempty_mkempty := by rintro st st' rfl; rfl

end ListProgramStack

/-! ### Weak program-stack theory (aPToP §7.1.3) -/

/-- The weak theory keeps `top′=x ⇐ push x` "but we do not need the composition
`push x. pop` to leave all variables unchanged. We do require that any natural
number of pushes followed by the same number of pops gives back the original
top": `top′=top ⇐ balance`, `balance ⇐ ok`, `balance ⇐ push x. balance. pop`,
"where `balance` is a specification that helps in writing the axioms, but is
not an addition to the theory, and does not need to be implemented". -/
structure WeakProgramStackTheory (X : Type u) (σ : Type v) where
  /-- `push x`. -/
  push : X → Spec σ
  /-- `pop`. -/
  pop : Spec σ
  /-- `top`. -/
  top : σ → X
  /-- `balance`, an auxiliary specification. -/
  balance : Spec σ
  /-- `top′=x ⇐ push x`. -/
  top_push : ∀ x, Refines (fun _ s' => top s' = x) (push x)
  /-- `top′=top ⇐ balance`. -/
  top_balance : Refines (fun s s' => top s' = top s) balance
  /-- `balance ⇐ ok`. -/
  balance_ok : Refines balance ok
  /-- `balance ⇐ push x. balance. pop`. -/
  balance_push_pop : ∀ x, Refines balance (seq (push x) (seq balance pop))

namespace WeakProgramStackTheory

variable {X : Type u} {σ : Type v} (T : WeakProgramStackTheory X σ)

/-- `n` pushes followed by `n` pops, as for the strong theory. -/
def balanced : List X → Spec σ
  | [] => ok
  | x :: xs => seq (T.push x) (seq (balanced xs) T.pop)

/-- `balance ⇐ balanced xs`. -/
theorem balance_refines_balanced (xs : List X) : Refines T.balance (T.balanced xs) := by
  induction xs with
  | nil => exact T.balance_ok
  | cons x xs ih =>
    exact refines_trans _ _ _ (T.balance_push_pop x)
      (refines_seq_mono (refines_refl _) (refines_seq_mono ih (refines_refl _)))

/-- "Any natural number of pushes followed by the same number of pops gives
back the original top": `top′=top ⇐ balanced xs`. -/
theorem top_balanced (xs : List X) : Refines (fun s s' => T.top s' = T.top s) (T.balanced xs) :=
  refines_trans _ _ _ T.top_balance (T.balance_refines_balanced xs)

end WeakProgramStackTheory

/-- The strong theory implies the weak one, with `balance := ok`. -/
def ProgramStackTheory.toWeak {X : Type u} {σ : Type v} (T : ProgramStackTheory X σ) :
    WeakProgramStackTheory X σ where
  push := T.push
  pop := T.pop
  top := T.top
  balance := ok
  top_push := T.top_push
  top_balance := fun _ _ h => h ▸ rfl
  balance_ok := refines_refl ok
  balance_push_pop x := by rw [ok_seq]; exact T.push_pop x

end LaPToP.TheoryDesign
