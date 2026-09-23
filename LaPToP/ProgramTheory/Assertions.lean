import LaPToP.ProgramTheory.Time
import LaPToP.ProgramTheory.Scope

/-!
# Assertions and backtracking

This module formalizes Section 5.4 (Assertions) and Section 5.4.0
(Backtracking) of Eric Hehner's *A Practical Theory of Programming* (aPToP).

## The model

"Assertions are defined as follows: `assert b = if b then ok else screen!
“error”. wait until ∞`. If `b` is true, `assert b` is the same as `ok`. If `b`
is false, an error message is printed, and execution cannot proceed in finite
time to any following actions."

Output (`screen!`) is a Chapter 9 notation with no counterpart in this
formalization yet, and `wait until ∞` is `t:= t↑∞ = t:= ∞`. We therefore
formalize the else-branch honestly as *what is observable in the theory of
Chapter 4*: the final time is `∞` (execution never proceeds in finite time),
with nothing said about the memory variables; the printed message is not
modelled. This needs a state with a time variable: `AT = {t; x; y}`.

"`ensure b` ... means “make `b` true without changing anything”:
`ensure b = if b then ok else b ∧ ok = b ∧ ok`." Disjunction `or` as a
programming connective is `Spec.or`. The book's backtracking example
`x:= 0 or x:= 1. ensure x=1 = x:= 1` is proved.
-/

namespace LaPToP.ProgramTheory

universe u

namespace Spec

variable {σ : Type u}

/-! ### `ensure` and `or` (aPToP §5.4.0) -/

/-- `ensure b = b ∧ ok`: "make `b` true without changing anything". -/
def ensure (b : σ → Prop) : Spec σ := and (fun s _ => b s) ok

variable (b : σ → Prop) (P Q : Spec σ)

/-- `ensure b = if b then ok else b ∧ ok`, the book's first form. -/
theorem ensure_eq_cond : ensure b = cond b ok (and (fun s _ => b s) ok) :=
  Spec.ext fun s _ => by
    simp only [ensure, and, cond]
    by_cases hb : b s <;> simp [hb]

/-- "Like `assert b`, `ensure b` is equal to `ok` if `b` is true." -/
theorem ensure_of_holds {s : σ} (hb : b s) (s' : σ) : ensure b s s' ↔ ok s s' :=
  ⟨And.right, fun h => ⟨hb, h⟩⟩

/-- `ensure ⊤ = ok`. -/
theorem ensure_true : ensure (fun _ : σ => True) = ok :=
  Spec.ext fun _ _ => ⟨And.right, fun h => ⟨trivial, h⟩⟩

/-- "When `b` is false, ... this is unimplementable (unless `b` is identically
`⊤`)": `ensure b` is implementable iff `b` holds in every state. -/
theorem implementable_ensure_iff : Implementable (ensure b) ↔ ∀ s, b s :=
  ⟨fun h s => let ⟨_, hb, _⟩ := h s; hb, fun h s => ⟨s, h s, rfl⟩⟩

/-- `P. ensure b` keeps the results of `P` that satisfy `b`: `ensure` filters
the poststate. -/
theorem seq_ensure : seq P (ensure b) = fun s s' => P s s' ∧ b s' :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨_, hP, hb, h⟩ => h ▸ ⟨hP, hb⟩, fun ⟨hP, hb⟩ => ⟨_, hP, hb, rfl⟩⟩

/-- `(P or Q). ensure b = (P. ensure b) or (Q. ensure b)`: the choice is made
so as to satisfy the later `ensure` (backtracking). -/
theorem or_seq_ensure : seq (or P Q) (ensure b) = or (seq P (ensure b)) (seq Q (ensure b)) := by
  rw [seq_ensure, seq_ensure, seq_ensure]
  exact Spec.ext fun _ _ => by simp only [or]; tauto

/-- `P ∨ Q ⇐ P`: "normally this choice is made as a refinement". -/
theorem or_refines_left : Refines (or P Q) P := fun _ _ h => Or.inl h

/-- `P ∨ Q ⇐ Q`. -/
theorem or_refines_right : Refines (or P Q) Q := fun _ _ h => Or.inr h

end Spec

/-! ### Assertions (aPToP §5.4) -/

namespace Assertions

open Spec

/-- A state with a time variable `t` and two integer variables `x`, `y`. -/
structure AT where
  /-- The time variable. -/
  t : ℕ∞
  /-- The variable `x`. -/
  x : ℤ
  /-- The variable `y`. -/
  y : ℤ

/-- `x:= e`. -/
def assignX (e : AT → ℤ) : Spec AT := fun s s' => s' = { s with x := e s }

/-- `y:= e`. -/
def assignY (e : AT → ℤ) : Spec AT := fun s s' => s' = { s with y := e s }

/-- Substitution Law for `x:= e`. -/
theorem assignX_seq (e : AT → ℤ) (P : Spec AT) : seq (assignX e) P = fun s s' => P { s with x := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- `assert b = if b then ok else screen! “error”. wait until ∞`: if `b` holds,
`ok`; otherwise "execution cannot proceed in finite time to any following
actions", i.e. `t′ = ∞` (the printed message is not modelled). -/
def assert (b : AT → Prop) : Spec AT := cond b ok fun _ s' => s'.t = ⊤

variable (b : AT → Prop) (P : Spec AT)

/-- "If `b` is true, `assert b` is the same as `ok`." -/
theorem assert_of_holds {s : AT} (hb : b s) (s' : AT) : assert b s s' ↔ ok s s' := by
  rw [assert, cond_pos _ _ b hb]

/-- If `b` is false, `assert b` ends at time `∞`. -/
theorem assert_of_not {s : AT} (hb : ¬ b s) (s' : AT) : assert b s s' ↔ s'.t = ⊤ := by
  rw [assert, cond_neg _ _ b hb]

/-- What a machine with no clock can see of an assertion: starting from a state
at finite time, the behaviours of `assert b` that end in finite time are exactly
`ensure b`. The difference between the two — a false `assert` is implementable
by waiting forever, a false `ensure` is not implementable at all — lives
entirely in the time variable, so on a state without one they cannot be told
apart. -/
theorem assert_finite (b : AT → Prop) {s : AT} (hs : s.t ≠ ⊤) (s' : AT) :
    (assert b s s' ∧ s'.t ≠ ⊤) ↔ ensure b s s' := by
  constructor
  · rintro ⟨h, ht⟩
    by_cases hb : b s
    · exact ⟨hb, (assert_of_holds b hb s').1 h⟩
    · exact absurd ((assert_of_not b hb s').1 h) ht
  · rintro ⟨hb, hok⟩
    rw [show s' = s from hok]
    exact ⟨(assert_of_holds b hb s).2 rfl, hs⟩

/-- `assert ⊤ = ok`: "in a correct program, the asserted expressions will
always be true, and so all assertions are redundant". -/
theorem assert_true : assert (fun _ => True) = ok :=
  Spec.ext fun s _ => by rw [assert_of_holds _ trivial]

/-- `ensure b` refines `assert b`: both are `ok` when `b` holds. -/
theorem assert_refines_ensure : Refines (assert b) (ensure b) := fun _ _ ⟨hb, h⟩ =>
  (assert_of_holds b hb _).2 h

/-- An assertion is implementable with time not decreasing: a false assertion
is satisfied by waiting forever. -/
theorem implementable_assert : ∀ s, ∃ s', assert b s s' ∧ s.t ≤ s'.t := fun s => by
  by_cases hb : b s
  · exact ⟨s, (assert_of_holds b hb s).2 rfl, le_rfl⟩
  · exact ⟨{ s with t := ⊤ }, (assert_of_not b hb _).2 rfl, le_top⟩

/-- Hence `assert b` is implementable. -/
theorem implementable_assert' : Implementable (assert b) := fun s =>
  let ⟨s', h, _⟩ := implementable_assert b s; ⟨s', h⟩

/-- A false assertion followed by anything: "execution cannot proceed in finite
time to any following actions" — the following specification starts at time `∞`. -/
theorem assert_seq_of_not {s : AT} (hb : ¬ b s) (s' : AT) :
    seq (assert b) P s s' ↔ ∃ s'', s''.t = ⊤ ∧ P s'' s' := by
  simp only [seq, assert_of_not b hb]

/-- A true assertion followed by `P` is `P`. -/
theorem assert_seq_of_holds {s : AT} (hb : b s) (s' : AT) : seq (assert b) P s s' ↔ P s s' := by
  simp only [seq, assert_of_holds b hb, Spec.ok]
  exact ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨s, rfl, hP⟩⟩

/-! ### Backtracking (aPToP §5.4.0) -/

/-- `x:= 0 or x:= 1`: "a program whose execution assigns either 0 or 1 to `x`". -/
def choice : Spec AT := or (assignX fun _ => 0) (assignX fun _ => 1)

/-- `x:= 0 or x:= 1. ensure x=1 = x:= 1`: "although an implementation is given a
choice between `x:= 0` and `x:= 1`, it must choose the right one to satisfy a
later binary expression". -/
theorem choice_ensure : seq choice (ensure fun s => s.x = 1) = assignX fun _ => 1 := by
  rw [seq_ensure]
  refine Spec.ext fun s s' => ⟨?_, ?_⟩
  · rintro ⟨h | h, hx⟩
    · simp only [assignX] at h
      subst h
      simp at hx
    · exact h
  · intro h
    simp only [assignX] at h
    exact ⟨Or.inr h, by subst h; rfl⟩

/-- `x:= 0 or x:= 1` is implementable, and so is the whole example. -/
theorem implementable_choice : Implementable choice := fun _s => ⟨_, Or.inl rfl⟩

end Assertions

end LaPToP.ProgramTheory
