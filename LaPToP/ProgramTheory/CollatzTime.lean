import LaPToP.ProgramTheory.Time

/-!
# The Collatz program and its execution time

This module formalizes the remark on Exercise 255 (Collatz) that closes
Subsection 4.2.7 of Eric Hehner's *A Practical Theory of Programming*
(aPToP).

"Finding the execution time of any program can always be done by
transforming the program into a function that expresses the execution time.
To illustrate how, we do Exercise 255 (Collatz), which is a famous program
whose execution time is considered to be unknown. Let `n` be a natural
variable. Then, including recursive time,

    n′=1 ⇐ if n=1 then ok else if even n then n:= n/2 else n:= 3×n + 1. t:= t+1. n′=1

We can express the execution time as `f n`, where function `f` must satisfy

    t′ = t + f n ⇐ if n=1 then ok else if even n then n:= n/2 else n:= 3×n + 1. t:= t+1. t′ = t + f n

which can be simplified to `f 1 = 0`, `even n ∧ n>1 ⇒ f n = 1 + f (n/2)`,
`odd n ∧ n>1 ⇒ f n = 1 + f (3×n + 1)`. ... It is not even known whether `f` is
finite for all `n>0`. If it were as well studied and familiar as square, we
would accept it as a time bound."

## The model

The refinement `n′=1 ⇐ …` with the recursive call as the specification is
proved (it says nothing about termination: the specification `n′=1` is what
the recursive call is assumed to establish). The book's time function is
characterized by its three equations, `IsCollatzTime f`, with values in
`xnat` so that `∞` is allowed; for any such `f` the timing refinement is
proved. Nothing is claimed about finiteness — that is the Collatz conjecture,
which the Blueprint's demo chapter keeps as its intentionally open node.
-/

namespace LaPToP.ProgramTheory

namespace CollatzTime

open Spec

/-- The state: the natural variable `n` and the time. -/
structure CS where
  /-- `n`. -/
  n : ℕ
  /-- The time. -/
  t : ℕ∞

/-- `n:= e`. -/
def assignN (e : CS → ℕ) : Spec CS := fun s s' => s' = { s with n := e s }
/-- `t:= t+1`. -/
def tick : Spec CS := fun s s' => s' = { s with t := s.t + 1 }

theorem assignN_seq (e : CS → ℕ) (P : Spec CS) : seq (assignN e) P = fun s s' => P { s with n := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem tick_seq (P : Spec CS) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- The Collatz step as a program: `if even n then n:= n/2 else n:= 3×n + 1`. -/
def step : Spec CS := cond (fun s => Even s.n) (assignN fun s => s.n / 2) (assignN fun s => 3 * s.n + 1)

/-- `if n=1 then ok else (step). t:= t+1. G`, the body with the recursive call `G`. -/
def body (G : Spec CS) : Spec CS := cond (fun s => s.n = 1) ok (seq step (seq tick G))

/-- `n′=1`. -/
def Goal : Spec CS := fun _ s' => s'.n = 1

/-- `n′=1 ⇐ if n=1 then ok else if even n then n:= n/2 else n:= 3×n + 1. t:= t+1. n′=1`
(the recursive call as the specification). -/
theorem goal_refines : Refines Goal (body Goal) := by
  rintro s s' (⟨hn, rfl⟩ | ⟨-, u, -, v, -, hG⟩)
  · exact hn
  · exact hG

/-- The book's execution-time function: `f 1 = 0`, `even n ∧ n>1 ⇒ f n = 1 + f (n/2)`,
`odd n ∧ n>1 ⇒ f n = 1 + f (3×n + 1)`, with values in `xnat`. -/
def IsCollatzTime (f : ℕ → ℕ∞) : Prop :=
  f 1 = 0 ∧ (∀ n, n ≠ 1 → Even n → f n = 1 + f (n / 2)) ∧ (∀ n, n ≠ 1 → ¬ Even n → f n = 1 + f (3 * n + 1))

/-- `t′ = t + f n`. -/
def TimeSpec (f : ℕ → ℕ∞) : Spec CS := fun s s' => s'.t = s.t + f s.n

/-- `t′ = t + f n ⇐ if n=1 then ok else if even n then n:= n/2 else n:= 3×n + 1. t:= t+1. t′ = t + f n`,
for any `f` satisfying the three equations. -/
theorem time_refines {f : ℕ → ℕ∞} (hf : IsCollatzTime f) : Refines (TimeSpec f) (body (TimeSpec f)) := by
  obtain ⟨h1, heven, hodd⟩ := hf
  rintro s s' (⟨hn, rfl⟩ | ⟨hn, h⟩)
  · simp only [TimeSpec, hn, h1, add_zero]
  · obtain ⟨u, hu, v, hv, hT⟩ := h
    rw [tick] at hv
    subst hv
    simp only [TimeSpec] at hT ⊢
    rcases hu with ⟨he, rfl⟩ | ⟨he, rfl⟩
    · rw [hT, heven s.n hn he, add_assoc]
    · rw [hT, hodd s.n hn he, add_assoc]

end CollatzTime

end LaPToP.ProgramTheory
