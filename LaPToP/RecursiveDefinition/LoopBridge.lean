import LaPToP.ProgramTheory.Interpreter
import LaPToP.RecursiveDefinition.Programs

/-!
# The terminating runs of a loop, and the loop defined by least fixed point

Two accounts of the while-loop have been formalized, and this module ties them
together.

* Section 5.2 gives the loop as a *refinement notation*: `Spec.WhileRefines W b P`
  says that `W ⇐ while b do P od` is provable in the book's sense. The
  interpreter needs a specification rather than a notation, so
  `Spec.whileRel b R` was defined as the relation of the *terminating*
  executions, and shown to be the strongest solution of the refinement
  (`Spec.refines_whileRel`): whatever a Section 5.2 development proves of `W`
  holds of every run that terminates.
* Section 6.1.1 defines the loop by *axioms* — `whileC` is the constructor with
  recursive timing, `WhileAxioms` the three axioms, and the loop they define is
  the weakest specification satisfying the first two.

## What is proved here

Write `whileRun b P = whileRel b (P. t:= t+1)` for the terminating runs of the
loop *with the recursive timing* of Section 6.1.1 — the body of the loop the
axioms describe is `P. t:= t+1`, so this is the honest comparison. Then, for any
body that does not decrease time (`Refines timeNondecreasing P`, which holds of
`tick` and of assignments to `x` and `y`):

* `whileC_whileRun` — `whileRun b P` is a fixed point of the book's constructor:
  `while b do P od = t′≥t ∧ if b then P. t:= t+1. while b do P od else ok` holds
  with `whileRun b P` for the loop.
* `whileRun_refines_of_prefixed` — it is the *strongest* such solution: every
  `Z` with `t′≥t ∧ if b then P. t:= t+1. Z else ok ⇐ Z` is refined by it.
* `refines_whileRun` — hence, by the induction axiom, every `Wh` satisfying
  `WhileAxioms` is refined by `whileRun b P`. **This is the bridge**: every
  terminating execution of the loop — in particular every successful run of
  `Interpreter.run` on a loop, and every `Interpreter.Eval` derivation — is a
  behaviour allowed by the loop that Section 6.1.1 defines.

## The residual gap, stated honestly

The converse fails, and must: `whileRun` is the strongest fixed point and the
book's loop is the weakest, and they differ exactly on the nonterminating
computations, which the book's loop admits at time `∞`.
`not_refines_whileRun` proves this for `while ⊤ do t:= t+1 od`, which has no
terminating runs at all while any `Wh` satisfying the axioms relates
`t, x, y = 0` to `t′ = ∞`. So the bridge is a partial-correctness bridge, as it
should be.

A second gap is one of state spaces, not of mathematics. Section 6.1.1 is
formalized over the concrete state `ZS` (a time variable and two integers)
because the axioms mention `t:= t+1`, while `Interpreter.Prog` runs over
`Spec.State Var Val = Var → Val`, which has no time variable. The bridge is
therefore proved at the level of the loop specification `Spec.whileRel`, which
is exactly what `Interpreter.denote` assigns to `whileDo`; carrying a time
variable inside the interpreter's state is left to a later round.
-/

namespace LaPToP.RecursiveDefinition

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

namespace LoopDefinition

open Zap

variable {b : ZS → Prop} {P : Spec ZS}

/-! ### Bodies that do not decrease time -/

/-- `t:= t+1` does not decrease time. -/
theorem timeNondecreasing_tick : Refines timeNondecreasing tick := by
  intro s s' h
  subst h
  exact le_add_of_nonneg_right zero_le_one

/-- `x:= e` does not decrease time: it leaves `t` alone. -/
theorem timeNondecreasing_assignX (e : ZS → ℤ) : Refines timeNondecreasing (assignX e) := by
  intro s s' h
  subst h
  exact le_rfl

/-- `y:= e` does not decrease time. -/
theorem timeNondecreasing_assignY (e : ZS → ℤ) : Refines timeNondecreasing (assignY e) := by
  intro s s' h
  subst h
  exact le_rfl

/-- A sequence of steps that do not decrease time does not decrease time. -/
theorem timeNondecreasing_seq {Q : Spec ZS} (hP : Refines timeNondecreasing P)
    (hQ : Refines timeNondecreasing Q) : Refines timeNondecreasing (seq P Q) := by
  rintro s s' ⟨u, hu, hu'⟩
  exact le_trans (hP _ _ hu) (hQ _ _ hu')

/-! ### The terminating runs of the loop with recursive timing -/

/-- The terminating executions of `while b do P od` with the recursive timing of
Section 6.1.1: the body of one iteration is `P. t:= t+1`. -/
def whileRun (b : ZS → Prop) (P : Spec ZS) : Spec ZS := whileRel b (seq P tick)

/-- `while b do P od = if b then P. t:= t+1. while b do P od else ok` for the
terminating runs. -/
theorem whileRun_unfold (b : ZS → Prop) (P : Spec ZS) :
    whileRun b P = cond b (seq P (seq tick (whileRun b P))) ok := by
  rw [seq_assoc]
  exact whileRel_unfold b (seq P tick)

/-- A loop whose body does not decrease time does not decrease time on its
terminating runs — the first of the book's three axioms, for `whileRun`. -/
theorem timeNondecreasing_whileRun (hP : Refines timeNondecreasing P) :
    Refines timeNondecreasing (whileRun b P) := by
  intro s s' h
  replace h : whileRel b (seq P tick) s s' := h
  induction h with
  | exit => exact le_rfl
  | @step s t s' _ hR _ ih =>
    obtain ⟨u, hPu, htick⟩ := hR
    exact le_trans (le_trans (hP _ _ hPu) (timeNondecreasing_tick _ _ htick)) ih

/-- The terminating runs are a fixed point of the Section 6.1.1 constructor:
`t′≥t ∧ if b then P. t:= t+1. whileRun else ok = whileRun`. -/
theorem whileC_whileRun (hP : Refines timeNondecreasing P) :
    whileC b P (whileRun b P) = whileRun b P := by
  have hT := timeNondecreasing_whileRun (b := b) hP
  refine Spec.ext fun s s' => ⟨fun h => ?_, fun h => ?_⟩
  · rw [whileRun_unfold]
    exact h.2
  · refine ⟨hT s s' h, ?_⟩
    rw [whileRun_unfold] at h
    exact h

/-- The terminating runs are the *strongest* pre-fixed point of the constructor:
any `Z` with `t′≥t ∧ if b then P. t:= t+1. Z else ok ⇐ Z` is refined by them. -/
theorem whileRun_refines_of_prefixed {Z : Spec ZS} (hP : Refines timeNondecreasing P)
    (h : Refines Z (whileC b P Z)) : Refines Z (whileRun b P) := by
  intro s s' hw
  replace hw : whileRel b (seq P tick) s s' := hw
  induction hw with
  | @exit s hb => exact h s s ⟨le_rfl, Or.inr ⟨hb, rfl⟩⟩
  | @step s t s' hb hR hW ih =>
    obtain ⟨u, hPu, htick⟩ := hR
    refine h s s' ⟨?_, Or.inl ⟨hb, u, hPu, t, htick, ih⟩⟩
    exact le_trans (le_trans (hP _ _ hPu) (timeNondecreasing_tick _ _ htick))
      (timeNondecreasing_whileRun hP t s' hW)

/-- **The bridge.** Every terminating execution of the loop is a behaviour of the
loop that the Section 6.1.1 axioms define: `while b do P od ⇐ whileRun b P` for
any `Wh` satisfying `WhileAxioms`. So a run of `Interpreter.run` on a loop, or a
fuel-free `Interpreter.Eval` derivation for it, is allowed by the
least-fixed-point loop as well as by the Section 5.2 one. -/
theorem refines_whileRun {Wh : Spec ZS} (h : WhileAxioms Wh b P)
    (hP : Refines timeNondecreasing P) : Refines Wh (whileRun b P) :=
  h.induction _ (refines_of_eq (whileC_whileRun hP))

/-- Since the two solutions are fixed points at opposite ends, a specification
satisfying the axioms is refined by the terminating runs whenever it is refined
by *some* pre-fixed point of the constructor. -/
theorem refines_whileRun_of_prefixed {Wh Z : Spec ZS} (h : WhileAxioms Wh b P)
    (hP : Refines timeNondecreasing P) (hZ : Refines Z (whileC b P Z)) :
    Refines Wh (whileRun b P) ∧ Refines Z (whileRun b P) :=
  ⟨refines_whileRun h hP, whileRun_refines_of_prefixed hP hZ⟩

/-! ### The gap: nontermination -/

/-- For `while ⊤ do t:= t+1 od`, every specification satisfying the axioms
admits every final state at time `∞` — the same argument as
`WhileAxioms.refines_top_time`, for a body that does not decrease time. -/
theorem WhileAxioms.refines_top_time_tick {Wh : Spec ZS}
    (h : WhileAxioms Wh (fun _ => True) tick) : Refines Wh fun _ s' => s'.t = ⊤ := by
  refine h.induction _ fun s s' hW => ?_
  exact ⟨show s.t ≤ s'.t from hW ▸ le_top, Or.inl ⟨trivial, _, rfl, _, rfl, hW⟩⟩

/-- `while ⊤ do t:= t+1 od` has no terminating runs. -/
theorem whileRun_top_tick : whileRun (fun _ => True) tick = bot :=
  whileRel_of_always _ _ fun _ => trivial

/-- **The residual gap.** The bridge cannot be strengthened to an equality: for
`while ⊤ do t:= t+1 od` the terminating runs are `⊥` while the loop defined by
the axioms relates `t, x, y = 0` to `t′ = ∞`. The least-fixed-point loop
describes the nonterminating computations, which no account of *runs* can. -/
theorem not_refines_whileRun {Wh : Spec ZS} (h : WhileAxioms Wh (fun _ => True) tick) :
    ¬ Refines (whileRun (fun _ => True) tick) Wh := fun hr => by
  have hWh : Wh ⟨0, 0, 0⟩ ⟨⊤, 0, 0⟩ := WhileAxioms.refines_top_time_tick h _ _ rfl
  have hrun := hr _ _ hWh
  rw [whileRun_top_tick] at hrun
  exact hrun

end LoopDefinition

end LaPToP.RecursiveDefinition
