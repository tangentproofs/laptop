import LaPToP.Exercises.Basic
import Mathlib.Tactic

/-!
# Exercises — Introduction (aPToP §10.0)

Exercises 0–3 are puzzles about statements; each is formalized with binary
(`Bool`) variables for the statements, and its answer proved by checking every
case.
-/

namespace LaPToP.Exercises.Ch0

/-! ### Exercise 0 (the four cards)

Four cards show `D`, `E`, `2`, `3`; each has a letter on one side and a digit on
the other. To determine whether every card with a `D` on one side has a `3` on
the other, a card must be turned over exactly when what is on its hidden side
can decide the rule for it. -/

/-- A letter: `D`, `E`, or another. -/
inductive Letter | D | E | other
  deriving DecidableEq

/-- A digit: `2`, `3`, or another. -/
inductive Digit | two | three | other
  deriving DecidableEq

/-- Every letter. -/
def letters : List Letter := [.D, .E, .other]

/-- Every digit. -/
def digits : List Digit := [.two, .three, .other]

/-- The rule, for one card. -/
def rule (l : Letter) (d : Digit) : Bool := l != .D || d == .three

/-- A card showing a letter must be turned if the rule depends on its digit. -/
def turnLetter (l : Letter) : Bool := digits.any fun d₁ => digits.any fun d₂ => rule l d₁ != rule l d₂

/-- A card showing a digit must be turned if the rule depends on its letter. -/
def turnDigit (d : Digit) : Bool := letters.any fun l₁ => letters.any fun l₂ => rule l₁ d != rule l₂ d

/-- **Exercise 0**: turn over `D` and `2`, and not `E` or `3`. -/
theorem exercise_0 :
    turnLetter .D = true ∧ turnLetter .E = false ∧ turnDigit .two = true ∧
      turnDigit .three = false := by decide

/-! ### Exercise 1 (who is looking at whom)

Jack looks at Anne, Anne looks at George; Jack is married, George is single;
whether Anne is married is not given. -/

/-- **Exercise 1**: yes — whichever Anne is, a married person is looking at a
single one (Jack at Anne, or Anne at George). -/
theorem exercise_1 (anne : Bool) :
    let jack := true; let george := false
    ((jack && !anne) || (anne && !george)) = true := by
  cases anne <;> rfl

/-! ### Exercise 2 (three statements) -/

/-- How many of three statements are false. -/
def falses (a b c : Bool) : ℕ := [a, b, c].count false

/-- **Exercise 2**: the only consistent reading is that statement (ii) is true
and statements (i) and (iii) are false. -/
theorem exercise_2 (s₁ s₂ s₃ : Bool) :
    (s₁ = decide (falses s₁ s₂ s₃ = 1) ∧ s₂ = decide (falses s₁ s₂ s₃ = 2) ∧
        s₃ = decide (falses s₁ s₂ s₃ = 3)) ↔
      (s₁ = false ∧ s₂ = true ∧ s₃ = false) := by
  revert s₁ s₂ s₃; decide

/-! ### Exercise 3 (five statements about themselves)

A statement about itself is formalized by an equation `s = e s`: its value must
be the value of what it says. -/

/-- **Exercise 3**: (i) `s = s` may be true or false; (ii) `s = ¬s` has no
consistent value; (iii) `s = (s ∨ ¬s)` must be true; (iv) `s = ¬(s ∨ ¬s)` and
(v) `s = (s ∧ ¬s)` must be false. -/
theorem exercise_3 :
    (∀ s : Bool, s = s) ∧
    (∀ s : Bool, s ≠ !s) ∧
    (∀ s : Bool, s = (s || !s) ↔ s = true) ∧
    (∀ s : Bool, s = !(s || !s) ↔ s = false) ∧
    (∀ s : Bool, s = (s && !s) ↔ s = false) := by decide

end LaPToP.Exercises.Ch0
