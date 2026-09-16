import LaPToP.TheoryDesign.DataTransformation

/-!
# Security switch

This module formalizes Section 7.2.0 (Security Switch) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), Exercise 460.

"It has three binary user's variables `a`, `b`, and `c`. The users assign
values to `a` and `b` as input to the switch. The switch's output is assigned
to `c`. The output changes when both inputs have changed. More precisely, the
output changes when both inputs differ from what they were the previous time
the output changed. ... We can implement the switch with two binary
implementer's variables: `A` records the state of input `a` at the last
previous output change, `B` records the state of input `b` at the last
previous output change. There are two operations:

    a:= ¬a. if a⧧A ∧ b⧧B then c:= ¬c. A:= a. B:= b else ok
    b:= ¬b. if a⧧A ∧ b⧧B then c:= ¬c. A:= a. B:= b else ok

... This implementation is a direct formalization of the problem, but it can
be simplified by data transformation. We replace implementer's variables `A`
and `B` by nothing according to the transformer `A=B=c`. ... The
transformation does not affect the assignments to `a` and `b`, so we have only
one transformation to make. ... `= if a⧧c ∧ b⧧c then c:= ¬c else ok =
c:= (a⧧c ∧ b⧧c) ⧧ c`. Output `c` becomes the majority value of `a`, `b`, and
`c`."

## The model

User's variables `U := Bool × Bool × Bool` (`a`, `b`, `c`); old implementer's
variables `O := Bool × Bool` (`A`, `B`); new implementer's variables `N := Unit`
("by nothing"). The transformer `A=B=c` mentions the user's variable `c`, so it
is a `Spec.transformU` transformer `D : U → O → N → Prop`, and `D′` primes `c`
as well as `A`, `B` — exactly as in the book's calculation, where
`∃A′, B′· A′=B′=c′` is eliminated by one-point. The book's chain of equalities
is proved as the single equation `transformU D switchStep = c:= (a⧧c ∧ b⧧c) ⧧ c`,
and the majority remark by `decide`.
-/

namespace LaPToP.TheoryDesign

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

namespace SecuritySwitch

open Spec

/-- The user's variables `a`, `b`, `c`. -/
abbrev U := Bool × Bool × Bool

/-- The old implementer's variables `A`, `B`. -/
abbrev O := Bool × Bool

/-- The transformer `A=B=c`: "we replace implementer's variables `A` and `B` by
nothing". -/
def D (u : U) (o : O) (_ : Unit) : Prop := o.1 = u.2.2 ∧ o.2 = u.2.2

/-- "To check that this is a transformer, we check `∃A, B· A=B=c ⇐ ⊤`,
generalization, using `c` for both `A` and `B`." -/
theorem isTransformer : IsTransformerU D := fun u _ => ⟨(u.2.2, u.2.2), rfl, rfl⟩

/-- `if a⧧A ∧ b⧧B then c:= ¬c. A:= a. B:= b else ok`, the common second half of
both operations, as a relation on `(a, b, c), (A, B)`. -/
def switchStep : Spec (U × O) :=
  cond (fun s => s.1.1 ≠ s.2.1 ∧ s.1.2.1 ≠ s.2.2)
    (fun s s' => s' = ((s.1.1, s.1.2.1, !s.1.2.2), (s.1.1, s.1.2.1))) ok

/-- `a:= ¬a` on the full state. -/
def flipA : Spec (U × O) := fun s s' => s' = ((!s.1.1, s.1.2.1, s.1.2.2), s.2)

/-- `b:= ¬b` on the full state. -/
def flipB : Spec (U × O) := fun s s' => s' = ((s.1.1, !s.1.2.1, s.1.2.2), s.2)

/-- The first operation `a:= ¬a. if a⧧A ∧ b⧧B then c:= ¬c. A:= a. B:= b else ok`. -/
def opA : Spec (U × O) := seq flipA switchStep

/-- The second operation `b:= ¬b. if a⧧A ∧ b⧧B then c:= ¬c. A:= a. B:= b else ok`. -/
def opB : Spec (U × O) := seq flipB switchStep

/-- The transformed operation `c:= (a⧧c ∧ b⧧c) ⧧ c`, on the user's variables and
no implementer's variables. -/
def switchStepT : Spec (U × Unit) := fun s s' =>
  s' = ((s.1.1, s.1.2.1, xor (decide (s.1.1 ≠ s.1.2.2 ∧ s.1.2.1 ≠ s.1.2.2)) s.1.2.2), ())

/-- The book's calculation: `∀A, B· A=B=c ⇒ ∃A′, B′· A′=B′=c′ ∧ if a⧧A ∧ b⧧B then
c:= ¬c. A:= a. B:= b else ok = if a⧧c ∧ b⧧c then c:= ¬c else ok = c:= (a⧧c ∧ b⧧c) ⧧ c`. -/
theorem transformU_switchStep : transformU D switchStep = switchStepT := by
  refine Spec.ext fun ⟨⟨a, b, c⟩, ⟨⟩⟩ ⟨⟨a', b', c'⟩, ⟨⟩⟩ => ?_
  simp only [transformU, D, switchStep, switchStepT, Spec.cond, Spec.ok]
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> decide

/-- "The transformation does not affect the assignments to `a` and `b`": the
transformed first operation is `a:= ¬a. c:= (a⧧c ∧ b⧧c) ⧧ c`. -/
theorem transformU_opA :
    transformU D opA = seq (fun s s' : U × Unit => s' = ((!s.1.1, s.1.2.1, s.1.2.2), ())) switchStepT := by
  rw [← transformU_switchStep]
  refine Spec.ext fun ⟨⟨a, b, c⟩, ⟨⟩⟩ ⟨⟨a', b', c'⟩, ⟨⟩⟩ => ?_
  simp only [transformU, D, opA, seq, flipA, Prod.exists, exists_eq_left]

/-- Likewise for the second operation: `b:= ¬b. c:= (a⧧c ∧ b⧧c) ⧧ c`. -/
theorem transformU_opB :
    transformU D opB = seq (fun s s' : U × Unit => s' = ((s.1.1, !s.1.2.1, s.1.2.2), ())) switchStepT := by
  rw [← transformU_switchStep]
  refine Spec.ext fun ⟨⟨a, b, c⟩, ⟨⟩⟩ ⟨⟨a', b', c'⟩, ⟨⟩⟩ => ?_
  simp only [transformU, D, opB, seq, flipB, Prod.exists, exists_eq_left]

/-- The majority value of three binary values. -/
def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- "Output `c` becomes the majority value of `a`, `b`, and `c`." -/
theorem xor_eq_majority (a b c : Bool) : xor (decide (a ≠ c ∧ b ≠ c)) c = majority a b c := by
  cases a <;> cases b <;> cases c <;> decide

/-- "As a circuit, that's three “exclusive or” gates and one “and” gate":
`(a⧧c ∧ b⧧c) ⧧ c = ((a xor c) ∧ (b xor c)) xor c`. -/
theorem xor_circuit (a b c : Bool) : xor (decide (a ≠ c ∧ b ≠ c)) c = xor ((xor a c) && (xor b c)) c := by
  cases a <;> cases b <;> cases c <;> decide

end SecuritySwitch

end LaPToP.TheoryDesign
