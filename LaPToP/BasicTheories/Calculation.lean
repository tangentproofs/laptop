import LaPToP.BasicTheories.Binary

/-!
# Proof by calculation

This module formalizes the proof format of Section 1.0.1 of Eric Hehner's
*A Practical Theory of Programming* (aPToP): "one form of proof is a
continuing equation with hints", and its worked example, the first Law of
Portation.

"A proof is a binary expression that is clearly a theorem. ... One form of
proof is a continuing equation with hints:
`expression0 = expression1 = expression2 = expression3`, with `hint 0`,
`hint 1`, `hint 2` on the right side of the page. ... This continuing equation
is a short way of writing the longer binary expression
`expression0 = expression1 ∧ expression1 = expression2 ∧ expression2 = expression3`.
... The best kind of hint is the name of a law. ... By the transitivity of
`=`, this proof proves the theorem `expression0 = expression3`. A formal proof
is a proof in which every step fits the form of the law given as hint."

Lean's `calc` block is exactly this form: each step is an equation justified
by the law named as its hint, and the block proves the equation between the
first and last expressions by transitivity. The steps below use the laws of
`LaPToP.BasicTheories.Binary` under the book's names.
-/

namespace LaPToP.BasicTheories.Calculation

open Binary

variable (a b c : Binary)

/-- "This continuing equation is a short way of writing the longer binary
expression `expression0 = expression1 ∧ expression1 = expression2`", and "by
the transitivity of `=`, this proof proves the theorem `expression0 = expression2`". -/
theorem continuing_equation {α : Sort _} {x y z : α} (h : x = y ∧ y = z) : x = z := h.1.trans h.2

/-- The book's worked example, "the first Law of Portation
`a ∧ b ⇒ c = a ⇒ (b ⇒ c)`, using only previous laws":

```
  a∧b ⇒ c            Material Implication
= ¬(a∧b) ∨ c         Duality
= ¬a ∨ ¬b ∨ c        Material Implication
= a ⇒ ¬b ∨ c         Material Implication
= a ⇒ (b ⇒ c)
```
"By not using brackets on that line, we silently use the Associative Law of
disjunction" — made explicit as a step here. -/
theorem portation_calc : imp (a && b) c = imp a (imp b c) :=
  calc imp (a && b) c
      = (!(a && b) || c) := imp_eq_not_or (a && b) c        -- Material Implication
    _ = ((!a || !b) || c) := by rw [Binary.not_and]          -- Duality
    _ = (!a || (!b || c)) := (or_assoc (!a) (!b) c).symm     -- Associative (silent in the book)
    _ = imp a (!b || c) := (imp_eq_not_or a (!b || c)).symm  -- Material Implication
    _ = imp a (imp b c) := by rw [imp_eq_not_or b c]         -- Material Implication

/-- "Here is the proof again, in a different form":

```
  (a∧b ⇒ c = a ⇒ (b ⇒ c))              Material Implication, 3 times
= (¬(a∧b) ∨ c = ¬a ∨ (¬b ∨ c))         Duality
= (¬a ∨ ¬b ∨ c = ¬a ∨ ¬b ∨ c)          Reflexivity
= ⊤
```
Here the whole equation is a binary expression, calculated down to `⊤`. -/
theorem portation_calc' : (imp (a && b) c == imp a (imp b c)) = true :=
  calc (imp (a && b) c == imp a (imp b c))
      = ((!(a && b) || c) == (!a || (!b || c))) := rfl            -- Material Implication, 3 times
    _ = (((!a || !b) || c) == (!a || (!b || c))) := by rw [Binary.not_and] -- Duality
    _ = (((!a || !b) || c) == ((!a || !b) || c)) := by rw [Binary.or_assoc] -- Associative
    _ = true := beq_self _                                          -- Reflexivity

/-- The two forms prove the same law: the calculation to `⊤` yields the equation. -/
theorem portation_of_calc' : imp (a && b) c = imp a (imp b c) :=
  beq_iff_eq.1 (portation_calc' a b c)

/-- Every step of a formal proof "fits the form of the law given as hint": the
laws used above are exactly `Binary.imp_eq_not_or`, `Binary.not_and`,
`Binary.or_assoc`, `Binary.beq_self` — and the result is the book's Law of
Portation `Binary.and_imp_eq_imp_imp`. -/
theorem portation_calc_eq_law : portation_calc = and_imp_eq_imp_imp := rfl

end LaPToP.BasicTheories.Calculation
