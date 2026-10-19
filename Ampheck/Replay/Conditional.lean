import Ampheck.Replay.Sessions

/-!
# Replays: conditional laws, the dialog, and the named forms

Conditional readings at the number and the boolean level, supplying a law variable
by hand, `if … fi`, and the quantifiers. Each is checked by evaluation in Lean's
kernel, as `Ampheck.Replay` explains; the commands are there, and the sessions in
`Ampheck.Replay.Sessions`. These are kept out of `Ampheck.Replay` because a replay
against the shipped laws is expensive to evaluate in the kernel, and `lake build
ampheck` should not have to; `lake build AmpheckReplay` builds them.
-/

namespace Ampheck
namespace Replay

open Expr (var mvar num bin neg)

set_option maxRecDepth 100000

/-! ### Conditional laws at the number level -/

/-- So does a law of the list, when the premise is an instance of one side it
equates with `⊤`: `0 ≤ 0` is settled by `x ≤ x`. -/
theorem a_law_settles_a_ground_premise :
    Law.settles Laws.number (bin .le (num 0) (num 0)) = true := by decide +kernel

/-- And `0 ≤ m` is settled by neither: nothing in the list says it, so a step
that needs it is a step with a gap. -/
theorem nothing_settles_zero_le_m :
    Law.settles Laws.number (bin .le (num 0) (var "m")) = false := by decide +kernel

/-- It proves `0 ≤ m ⇒ n ≤ n + m`, with no gap and fully zoomed out: the premise
was discharged, so nothing is left over. -/
theorem bound_proves : provedIn conditionalSession bound = some boundGoal := by decide +kernel

theorem bound_complete :
    ((conditionalSession.steps bound).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

/-- At that number level the law is offered twice, `+` being symmetric, and the
two differ in exactly the way the document says they should: writing `n` needs
`0 ≤ m`, which the context settles, so it carries no premise; writing `m` needs
`0 ≤ n`, which nothing settles, so it says so before it is taken. -/
theorem bound_offers_discharged_and_gapped :
    ((conditionalSession.steps (bound.take 3)).toOption.map fun d =>
      (d.suggestions.filter (·.law == "upper bound")).map fun s => (s.op, s.result, s.premise))
      = some [(.ge, var "n", none), (.ge, var "m", some (bin .le (num 0) (var "n")))] := by decide +kernel

/-- The conditional reading puts a *number* direction in the margin, so the
boolean line cannot take it as a step of its own — but the line's main operands
are number parts, and a law applies to a part. So on `n ≤ n + m` the same law is
read three applicable ways: unconditionally on the whole line, which is the step
its own `⇐` licenses; conditionally on the operand `n + m`, rewriting the line in
place to `n ≤ n` with the premise `0 ≤ m` discharged by the context — which is
the very step the two zoom-ins of `bound` take the long way round; and
conditionally on that operand the other way round, writing `n ≤ m`, which needs
`0 ≤ n` and says so. -/
theorem bound_reads_the_boolean_line_three_ways :
    ((conditionalSession.steps (bound.take 2)).toOption.map fun d =>
      (d.suggestions.filter fun s => s.law == "upper bound" && s.holes.isEmpty).map
        fun s => (s.part, s.result, s.premise))
      = some
        [(Part.whole, bin .le (num 0) (var "m"), none),
         (Part.operand 1, bin .le (var "n") (var "n"), none),
         (Part.operand 1, bin .le (var "n") (var "m"), some (bin .le (num 0) (var "n")))] := by
  decide

/-- Taking it writes the line and leaves the warning sign on the line the step was
taken from, with the premise recorded there as what would close it. -/
theorem gapped_leaves_the_premise_as_a_gap :
    ((conditionalSession.steps gapped).toOption.map fun d =>
      (d.gaps, d.note 0, d.lines[0]?.bind Line.premise))
      = some ([0], "!", some (bin .le (num 0) (var "m"))) := by decide +kernel

/-- And the proof claims nothing, exactly as a gap left by direct entry makes it
claim nothing: the premise is a hole in the calculation, not a footnote to it. -/
theorem gapped_proves_nothing : provedIn conditionalSession gapped = none := by decide +kernel

/-- The line it wrote is the one the law licenses, and it carries the law's name:
the step is not refused, it is recorded as conditional. -/
theorem gapped_writes_the_law_s_line :
    ((conditionalSession.steps gapped).toOption.bind fun d =>
      d.lines[1]?.map fun l => (l.conn, l.expr, l.why))
      = some (some .ge, var "n", "upper bound") := by decide +kernel

/-! ### The conditional reading at the boolean level -/

/-- The conditional readings come last in every law the kernel ships with, which
is what makes the dedup keep the reading that needs nothing. -/
theorem conditional_variants_come_last :
    (Laws.boolean ++ Laws.number).all (fun l =>
      l.variants == l.variants.filter (·.premise.isNone)
        ++ l.variants.filter (·.premise.isSome)) = true := by decide +kernel

/-- Every conditional reading the *shipped boolean* laws offer is greyed until a
variable is supplied. A monotonicity or transitivity law relates the line to a
third formula that the line does not determine — `(a ⇒ b) ⇒ (a ∧ c ⇒ b ∧ c)` read
from `a ∧ c` must be told what `b` is — so matching leaves a variable free and the
kernel will not apply it unasked. That is the whole of the duplication guard's
promise: the list a user reads down is the list they read before, and a row that
needs telling says so. Saying it is the dialog box below (`Replay.dialog`). -/
theorem shipped_boolean_conditional_readings_are_all_greyed :
    ((session.steps
        [.start .boolean .down (bin .and (var "x") (bin .and (var "y") (var "z")))]).toOption.map
      conditionalRows) = some (true, true) := by decide +kernel

/-- It proves the goal, with no gap and fully zoomed out: the premise was
discharged, so nothing is left over. -/
theorem ponens_proves : provedIn ponensSession ponens = some ponensGoal := by decide +kernel

theorem ponens_complete :
    ((ponensSession.steps ponens).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

/-- The three readings of the context that can be taken there: the fact itself,
written on the whole line, and the conditional reading at each operand of
`b ⇒ c`. None of them carries a premise, because `a` is in force. -/
theorem ponens_offers_discharged_boolean_steps :
    ((ponensSession.steps (ponens.take 3)).toOption.map fun d =>
      (d.suggestions.filter fun s => s.law == "context" && s.holes.isEmpty).map
        fun s => (s.part, s.op, s.result, s.premise))
      = some
        [(Part.whole, .rimp, var "a", none),
         (Part.operand 0, .rimp, bin .imp (var "c") (var "c"), none),
         (Part.operand 1, .rimp, bin .imp (var "b") (var "b"), none)] := by decide +kernel

/-- Both readings are still offered, and both now say what they would leave to
prove. -/
theorem ponensGappy_offers_them_with_the_premise :
    ((ponensSession.steps (ponensGappy.take 2)).toOption.map fun d =>
      (d.suggestions.filter fun s =>
        s.law == "context" && s.holes.isEmpty && s.premise.isSome).map
        fun s => (s.part, s.result, s.premise))
      = some
        [(Part.operand 0, bin .imp (var "c") (var "c"), some (var "a")),
         (Part.operand 1, bin .imp (var "b") (var "b"), some (var "a"))] := by decide +kernel

/-- Taking one writes the line and leaves the document's warning sign on the line
the step was taken from, with the premise recorded there as what would close
it. -/
theorem ponensGappy_leaves_the_premise_as_a_gap :
    ((ponensSession.steps ponensGappy).toOption.map fun d =>
      (d.gaps, d.note 1, d.lines[1]?.bind Line.premise))
      = some ([1], "!", some (var "a")) := by decide +kernel

/-- And the proof claims nothing — which is right, because without `a` the goal is
not a theorem. The gap is not a formality: it is the difference between this and
`ponens`. -/
theorem ponensGappy_proves_nothing : provedIn ponensSession ponensGappy = none := by decide +kernel

/-! ### Supplying a law variable by hand -/

/-- Before the binding, the two readings at that operand are both greyed, and each
says which variable it is waiting for and what it would then need. -/
theorem dialog_rows_are_greyed_until_bound :
    ((dialogSession.steps (dialog.take 2)).toOption.map fun d =>
      (d.suggestions.filter fun s => s.law == "monotonic" && s.part == .operand 0).map
        fun s => (s.holes, s.result, s.premise))
      = some
        [(["b"], bin .imp (bin .and (mvar "b") (var "z")) (bin .and (var "y") (var "z")),
          some (bin .imp (var "x") (mvar "b"))),
         (["b"], bin .imp (bin .and (mvar "b") (var "x")) (bin .and (var "y") (var "z")),
          some (bin .imp (var "z") (mvar "b")))] := by decide +kernel

/-- With the binding the proof goes through: the greyed row became a step, and the
premise it needed was settled by the context, so there is no gap. -/
theorem dialog_proves : provedIn dialogSession dialog = some monoGoal := by decide +kernel

theorem dialog_complete :
    ((dialogSession.steps dialog).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

/-- Without the binding the very same command finds nothing: a suggestion that
leaves a variable free is not one `apply` will take, which is what it was before
and what keeps the dialog box honest — the kernel never guesses. -/
theorem dialog_needs_the_binding :
    ((dialogSession.steps (dialog.take 2 ++
      [.applyNamed "monotonic"
        (some (.rimp, bin .imp (bin .and (var "y") (var "z")) (bin .and (var "y") (var "z"))))
        []])).toOption).isSome = false := by decide +kernel

/-- A binding for a variable the suggestion has not got is refused too, rather
than quietly ignored: it is a typo, not a step. -/
theorem dialog_refuses_a_stray_binding :
    ((dialogSession.steps (dialog.take 2)).toOption.bind fun d =>
      (d.suggestions.filter fun s => s.law == "monotonic" && !s.holes.isEmpty).head?.map
        fun s => (d.applySuggestion s [("q", var "y")]).toOption.isSome)
      = some false := by decide +kernel

theorem dialogGappy_leaves_the_premise_as_a_gap :
    ((dialogSession.steps dialogGappy).toOption.map fun d =>
      (d.gaps, d.note 0, d.lines[0]?.bind Line.premise))
      = some ([0], "!", some (bin .imp (var "x") (var "y"))) := by decide +kernel

theorem dialogGappy_proves_nothing : provedIn dialogSession dialogGappy = none := by decide +kernel

/-! ### `if … then … else … fi` -/

theorem condBase_proves :
    provedIn condSession condBase
      = some (bin .eq (Expr.cond .top (var "x") (var "y")) (var "x")) := by decide +kernel

/-- Zooming in to the then-branch gains the condition, and leaves the direction
alone: the branch is in positive position. -/
theorem condBranch_gains_the_condition :
    ((condSession.steps (condBranch.take 2)).toOption.map fun d =>
      (d.contextLaws.map Law.stmt, d.frame?.map Frame.dir))
      = some ([var "b"], some .up) := by decide +kernel

theorem condBranch_proves :
    provedIn condSession condBranch = some (Expr.cond (var "b") (var "b") .top) := by decide +kernel

theorem condBranch_complete :
    ((condSession.steps condBranch).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

/-! ### `∀ids: d· b` and `∃ids: d· b` -/

/-- The law file line `generalized duality` is this expression, `x` and all: the
binder name a law writes is part of the law, and the next two theorems are about
what happens when a line spells it differently. -/
theorem duality_is_the_law_file_line :
    (Laws.quantifier.find? fun l => l.name == "generalized duality").map Law.stmt
      = some (bin .eq (neg (Expr.quant .all ["x"] (mvar "d") (mvar "b")))
                      (Expr.quant .ex ["x"] (mvar "d") (neg (mvar "b")))) := by decide +kernel

theorem quantDuality_proves :
    provedIn quantSession quantDuality
      = some (bin .eq (neg bounded)
          (Expr.quant .ex ["i"] (var "nat") (neg (bin .ge (var "i") (num 0))))) := by decide +kernel

/-- Zooming in to the body gains `i: nat` and leaves the direction alone: the body
is in positive position. -/
theorem quantBody_gains_the_membership :
    ((quantSession.steps (quantBody.take 2)).toOption.map fun d =>
      (d.contextLaws.map Law.stmt, d.frame?.map Frame.dir))
      = some ([bin .mem (var "i") (var "nat")], some .same) := by decide +kernel

theorem quantBody_proves :
    provedIn quantSession quantBody
      = some (bin .eq
          (Expr.quant .all ["i"] (var "nat") (neg (neg (bin .ge (var "i") (num 0)))))
          bounded) := by decide +kernel

theorem quantBody_complete :
    ((quantSession.steps quantBody).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

theorem quantDistribution_proves :
    provedIn quantSession quantDistribution
      = some (bin .eq distributionLine
          (bin .and (Expr.quant .all ["i"] (var "nat") (bin .ge (var "i") (num 0)))
                    (Expr.quant .all ["i"] (var "nat") (bin .le (var "i") (num 9))))) := by decide +kernel

/-- The hole this form leaves, pinned down rather than left to be discovered.

A domain is a *bunch*; the kernel's types are `boolean` and `number`; so a domain
whose own spelling settles nothing is read as boolean, and the boolean laws are
offered on it. `∀i: ¬¬nat· i ≥ 0 ∧ i ≤ 9` is a suggestion this tool makes and a
type checker would refuse. The document's answer is its type checker and its
warning sign — "if the type checker is unable to determine that the unifying
expressions have the correct types, a warning sign is placed on the line to which
the law is being applied" — and that is not built here. It is written as a theorem
so that building it breaks this line instead of leaving it to rot. -/
theorem quant_domain_is_offered_boolean_laws :
    ((quantSession.steps [.start .boolean .same distributionLine]).toOption.map fun d =>
      d.suggestions.any fun s =>
        s.result == Expr.quant .all ["i"] (neg (neg (var "nat")))
          (bin .and (bin .ge (var "i") (num 0)) (bin .le (var "i") (num 9))))
      = some true := by decide +kernel

end Replay
end Ampheck
