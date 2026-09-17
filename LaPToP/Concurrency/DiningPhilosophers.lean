import LaPToP.Concurrency.Transformation
import Mathlib.Data.Finset.Basic

/-!
# Dining philosophers

This module formalizes Subsection 8.1.2 (Dining Philosophers) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), Exercise 491.

"Five philosophers are sitting around a round table, thinking. ... Between
each pair of neighboring philosophers is a chopstick. Whenever a philosopher
gets hungry, the hungry philosopher reaches for the chopstick on the left
and the chopstick on the right, because it takes two chopsticks to eat. ...
A standard solution is to write one process for the life of each
philosopher, placing them in parallel. ... `life = P 0 || P 1 || P 2 || P 3 || P 4`,
`P i = think i. (up i || up(i⊕1)). eat i. (down i || down(i⊕1)). P i`,
`up i = chopstick i:= ⊤`, `down i = chopstick i:= ⊥`, `eat i = (uses chopstick i
and chopstick(i⊕1))`, `think i = (does not use any chopstick)`. This solution
is incorrect; it has too much concurrency. `P 0` cannot be placed in parallel
with `P 1` because they both assign and use `chopstick 1`. ... This solution
can deadlock. ... We'll start with a one-at-a-time version in which there is
no concurrency and no deadlock. `life = (P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4). life`,
`P i = think i. up i. up(i⊕1). eat i. down i. down(i⊕1)`. ... Then we
transform to get concurrency. `(think i. think j)` becomes `(think i || think j)`.
... If `i⧧j`, `(up i. up j)` becomes `(up i || up j)`. ... If `i⧧j ∧ i⊕1⧧j`,
`(eat i. up j)` and `(up j. eat i)` become `(eat i || up j)`. ... If `i⧧j ∧ i⊕1⧧j ∧
i⧧j⊕1`, `(eat i. eat j)` becomes `(eat i || eat j)`. ... All these
transformations are immediately seen from the definitions of `think`, `up`,
`down`, and `eat`. ... Before any transformation, there is no possibility of
deadlock. No transformation introduces the possibility. The result is the
maximum concurrency that does not lead to deadlock."

## The model

The state has the five chopsticks (`Fin 5 → Bool`; `i⊕1` is `i + 1` in
`Fin 5`) and a private variable `mind i` for each philosopher. `think i` is an
arbitrary deterministic computation on `mind i` alone ("does not use any
chopstick"), `eat i` an arbitrary deterministic computation on `mind i` that
reads `chopstick i` and `chopstick (i⊕1)` ("uses" them); both are
parameters. The variables each action mentions are made explicit
(`thinkVars`, `upVars`, `eatVars`), and the book's conditions are proved to
be exactly the disjointness of these variable sets — the criterion of
Section 8.1 for placing two programs in parallel. Each transformation is
then an equality of specifications: the two actions commute, so by
Section 8.1 either order is the concurrent composition. The one-at-a-time
`life` is defined, and "no possibility of deadlock" is the totality of each
`P i` (every action is always possible; nothing ever waits). The "too much
concurrency" of the standard solution is illustrated: `up 1` and `down 1` do
not commute.
-/

namespace LaPToP.Concurrency

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

namespace Dining

/-- The state: the five chopsticks and each philosopher's private variable. -/
structure DS where
  /-- `chopstick i`: whether chopstick `i` is picked up. -/
  chopstick : Fin 5 → Bool
  /-- The private state of philosopher `i` (what they think about, how hungry they are…). -/
  mind : Fin 5 → ℕ

/-- The state variables, for the criterion of Section 8.1. -/
inductive Var where
  /-- `chopstick i`. -/
  | ch (i : Fin 5)
  /-- `mind i`. -/
  | mind (i : Fin 5)
  deriving DecidableEq

/-- A deterministic step `σ:= f σ`. -/
def stepF (f : DS → DS) : Spec DS := fun s s' => s' = f s

theorem stepF_seq (f : DS → DS) (Q : Spec DS) : seq (stepF f) Q = fun s s' => Q (f s) s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hQ⟩ => h ▸ hQ, fun hQ => ⟨_, rfl, hQ⟩⟩

/-- `up i = chopstick i:= ⊤`. -/
def up (i : Fin 5) : Spec DS := stepF fun s => { s with chopstick := Function.update s.chopstick i true }

/-- `down i = chopstick i:= ⊥`. -/
def down (i : Fin 5) : Spec DS := stepF fun s => { s with chopstick := Function.update s.chopstick i false }

/-- `think i`: some computation `T` on `mind i` that "does not use any chopstick". -/
def think (T : Fin 5 → ℕ → ℕ) (i : Fin 5) : Spec DS := stepF fun s => { s with mind := Function.update s.mind i (T i (s.mind i)) }

/-- `eat i`: some computation `Eφ` on `mind i` that "uses chopstick `i` and chopstick `i⊕1`". -/
def eat (Eφ : Fin 5 → ℕ → Bool → Bool → ℕ) (i : Fin 5) : Spec DS :=
  stepF fun s => { s with mind := Function.update s.mind i (Eφ i (s.mind i) (s.chopstick i) (s.chopstick (i + 1))) }

/-- The variables of `think i`. -/
def thinkVars (i : Fin 5) : Finset Var := {Var.mind i}
/-- The variables of `up i` and `down i`. -/
def upVars (i : Fin 5) : Finset Var := {Var.ch i}
/-- The variables of `eat i`. -/
def eatVars (i : Fin 5) : Finset Var := {Var.mind i, Var.ch i, Var.ch (i + 1)}

/-! ### The book's conditions are disjointness of variables -/

theorem disjoint_think_think (i j : Fin 5) : Disjoint (thinkVars i) (thinkVars j) ↔ i ≠ j := by
  revert i j; decide

theorem disjoint_think_up (i j : Fin 5) : Disjoint (thinkVars i) (upVars j) := by
  revert i j; decide

theorem disjoint_think_eat (i j : Fin 5) : Disjoint (thinkVars i) (eatVars j) ↔ i ≠ j := by
  revert i j; decide

theorem disjoint_up_up (i j : Fin 5) : Disjoint (upVars i) (upVars j) ↔ i ≠ j := by
  revert i j; decide

/-- "If `i⧧j ∧ i⊕1⧧j`, `(eat i. up j)` … become `(eat i || up j)`." -/
theorem disjoint_eat_up (i j : Fin 5) : Disjoint (eatVars i) (upVars j) ↔ i ≠ j ∧ i + 1 ≠ j := by
  revert i j; decide

/-- "If `i⧧j ∧ i⊕1⧧j ∧ i⧧j⊕1`, `(eat i. eat j)` becomes `(eat i || eat j)`": two
philosophers can eat at the same time as long as they are not neighbours. -/
theorem disjoint_eat_eat (i j : Fin 5) : Disjoint (eatVars i) (eatVars j) ↔ i ≠ j ∧ i + 1 ≠ j ∧ i ≠ j + 1 := by
  revert i j; decide

/-! ### The transformations: the actions commute -/

theorem think_think_comm (T : Fin 5 → ℕ → ℕ) {i j : Fin 5} (h : i ≠ j) : seq (think T i) (think T j) = seq (think T j) (think T i) := by
  refine Spec.ext fun s s' => ?_
  simp only [think, stepF_seq, stepF, Function.update_of_ne h, Function.update_of_ne h.symm]
  rw [Function.update_comm h]

theorem think_up_comm (T : Fin 5 → ℕ → ℕ) (i j : Fin 5) : seq (think T i) (up j) = seq (up j) (think T i) := by
  refine Spec.ext fun s s' => ?_
  simp only [think, up, stepF_seq, stepF]

theorem think_down_comm (T : Fin 5 → ℕ → ℕ) (i j : Fin 5) : seq (think T i) (down j) = seq (down j) (think T i) := by
  refine Spec.ext fun s s' => ?_
  simp only [think, down, stepF_seq, stepF]

theorem think_eat_comm (T : Fin 5 → ℕ → ℕ) (Eφ : Fin 5 → ℕ → Bool → Bool → ℕ) {i j : Fin 5} (h : i ≠ j) : seq (think T i) (eat Eφ j) = seq (eat Eφ j) (think T i) := by
  refine Spec.ext fun s s' => ?_
  simp only [think, eat, stepF_seq, stepF, Function.update_of_ne h, Function.update_of_ne h.symm]
  rw [Function.update_comm h]

theorem up_up_comm {i j : Fin 5} (h : i ≠ j) : seq (up i) (up j) = seq (up j) (up i) := by
  refine Spec.ext fun s s' => ?_
  simp only [up, stepF_seq, stepF]
  rw [Function.update_comm h]

theorem up_down_comm {i j : Fin 5} (h : i ≠ j) : seq (up i) (down j) = seq (down j) (up i) := by
  refine Spec.ext fun s s' => ?_
  simp only [up, down, stepF_seq, stepF]
  rw [Function.update_comm h]

theorem down_down_comm {i j : Fin 5} (h : i ≠ j) : seq (down i) (down j) = seq (down j) (down i) := by
  refine Spec.ext fun s s' => ?_
  simp only [down, stepF_seq, stepF]
  rw [Function.update_comm h]

theorem eat_up_comm (Eφ : Fin 5 → ℕ → Bool → Bool → ℕ) {i j : Fin 5} (h1 : i ≠ j) (h2 : i + 1 ≠ j) : seq (eat Eφ i) (up j) = seq (up j) (eat Eφ i) := by
  refine Spec.ext fun s s' => ?_
  simp only [eat, up, stepF_seq, stepF, Function.update_of_ne h1, Function.update_of_ne h2]

theorem eat_down_comm (Eφ : Fin 5 → ℕ → Bool → Bool → ℕ) {i j : Fin 5} (h1 : i ≠ j) (h2 : i + 1 ≠ j) : seq (eat Eφ i) (down j) = seq (down j) (eat Eφ i) := by
  refine Spec.ext fun s s' => ?_
  simp only [eat, down, stepF_seq, stepF, Function.update_of_ne h1, Function.update_of_ne h2]

theorem eat_eat_comm (Eφ : Fin 5 → ℕ → Bool → Bool → ℕ) {i j : Fin 5} (h : i ≠ j) : seq (eat Eφ i) (eat Eφ j) = seq (eat Eφ j) (eat Eφ i) := by
  refine Spec.ext fun s s' => ?_
  simp only [eat, stepF_seq, stepF, Function.update_of_ne h, Function.update_of_ne h.symm]
  rw [Function.update_comm h]

/-- "Too much concurrency": `up 1` and `down 1` both assign `chopstick 1` and do not commute. -/
theorem up_down_not_comm : seq (up 1) (down 1) ≠ seq (down 1) (up 1) := by
  intro h
  have := congrFun (congrFun h ⟨fun _ => false, fun _ => 0⟩)
    ⟨Function.update (fun _ => false) 1 false, fun _ => 0⟩
  simp only [up, down, stepF_seq, stepF, Function.update_idem, eq_iff_iff] at this
  have h1 := this.mp trivial
  have h2 := congrArg (fun s : DS => s.chopstick 1) h1
  simp at h2

/-! ### The one-at-a-time life -/

/-- `P i = think i. up i. up(i⊕1). eat i. down i. down(i⊕1)`. -/
def Pi (T : Fin 5 → ℕ → ℕ) (Eφ : Fin 5 → ℕ → Bool → Bool → ℕ) (i : Fin 5) : Spec DS :=
  seq (think T i) (seq (up i) (seq (up (i + 1)) (seq (eat Eφ i) (seq (down i) (down (i + 1))))))

/-- `life = (P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4). life`, as a function of the unknown `life`. -/
def lifeBody (T : Fin 5 → ℕ → ℕ) (Eφ : Fin 5 → ℕ → Bool → Bool → ℕ) (L : Spec DS) : Spec DS :=
  seq (or (or (or (or (Pi T Eφ 0) (Pi T Eφ 1)) (Pi T Eφ 2)) (Pi T Eφ 3)) (Pi T Eφ 4)) L

/-- "No possibility of deadlock": every `P i` is total — each action is always
possible, nothing ever waits. -/
theorem implementable_Pi (T : Fin 5 → ℕ → ℕ) (Eφ : Fin 5 → ℕ → Bool → Bool → ℕ) (i : Fin 5) : Implementable (Pi T Eφ i) := by
  intro s
  simp only [Pi, think, up, eat, down, stepF_seq, stepF]
  exact ⟨_, rfl⟩

/-- One round of `life` is total, choosing (say) philosopher `0`. -/
theorem implementable_lifeBody_ok (T : Fin 5 → ℕ → ℕ) (Eφ : Fin 5 → ℕ → Bool → Bool → ℕ) : Implementable (lifeBody T Eφ ok) := by
  intro s
  obtain ⟨u, hu⟩ := implementable_Pi T Eφ 0 s
  exact ⟨u, u, Or.inl (Or.inl (Or.inl (Or.inl hu))), rfl⟩

end Dining

end LaPToP.Concurrency
