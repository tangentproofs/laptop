import Ampheck.Replay.Sessions

/-!
# Replays: the focus lands anywhere

Replays that reach an outer line by a click instead of by zooming out, and that go
back *into* a closed subproof. Each is checked by evaluation in Lean's kernel, as
`Ampheck.Replay` explains; the commands are there, and the sessions in
`Ampheck.Replay.Sessions`. These are kept out of `Ampheck.Replay` because a replay
against the shipped laws is expensive to evaluate in the kernel, and `lake build
ampheck` should not have to; `lake build AmpheckReplay` builds them.
-/

namespace Ampheck
namespace Replay

open Expr (var mvar num bin neg)

set_option maxRecDepth 100000

/-! ### The focus lands anywhere: recomputing the zoom stack -/

/-- Clicking line 0 while two levels deep in the proof leaves the focus there,
the stack back at the outermost level, and no context: the zoom in's facts went
out with its frame. The subproof's own lines stay in the document, and the line
the zoom out wrote is line 4. -/
theorem anywhere_closes_the_stack :
    ((session.steps (anywhere.take 5)).toOption.map fun d =>
      (d.focus, d.stack.length, d.contextLaws.length, d.lines.size))
      = some (0, 1, 0, 5) := by decide +kernel

/-- Every line is focusable: the two of the outermost level because they are
open, and the three of the closed subproof because the zoom out that closed it
is the last line of this level and can be taken back. -/
theorem anywhere_leaves_every_line_open_to_a_click :
    ((session.steps (anywhere.take 5)).toOption.map fun d =>
      (List.range d.lines.size).filter (d.canFocus ·)) = some [0, 1, 2, 3, 4] := by decide +kernel

/-- Three of them re-open the subproof; the two of the open level do not. -/
theorem anywhere_says_which_clicks_reopen :
    ((session.steps (anywhere.take 5)).toOption.map fun d =>
      (List.range d.lines.size).filter (d.reopensOn ·)) = some [1, 2, 3] := by decide +kernel

/-- Carrying on from there proves what `discharge` proves … -/
theorem anywhere_proves : proved anywhere = some dischargeGoal := by decide +kernel

set_option maxHeartbeats 1000000 in
/-- … and in fact writes the very same document: clicking an outer line did
what `Cmd.zoomOut` does. -/
theorem anywhere_is_discharge :
    ((session.steps anywhere).toOption.map fun d => d.lines.toList)
      = ((session.steps discharge).toOption.map fun d => d.lines.toList) := by decide +kernel

theorem nested_closes_both_levels :
    ((session.steps nested).toOption.map fun d =>
      (d.focus, d.stack.length, d.contextLaws.length, d.lines.size))
      = some (0, 1, 0, 6) := by decide +kernel

/-- The bottom line is the goal with `a ∧ b` turned around, which is what the
two zoom-outs put back. -/
theorem nested_puts_the_subproofs_back :
    ((session.steps nested).toOption.bind fun d => d.lines[5]?.map Line.expr)
      = some (bin .imp (bin .imp (var "a") (var "b"))
                (bin .imp (var "a") (bin .and (var "b") (var "a")))) := by decide +kernel

/-! ### Going back into a closed subproof -/

/-- Clicking a line of the closed subproof puts the focus there, one level deep,
with the line the zoom out wrote taken back — four lines where there were five —
and the context the zoom in supplied in force again. -/
theorem click_reopens_the_subproof :
    ((session.steps (anywhere.take 5 ++ [.setFocus 2])).toOption.map fun d =>
      (d.focus, d.depth, d.lines.size, d.contextLaws.length))
      = some (2, 1, 4, 1) := by decide +kernel

/-- And it writes back the very state the zoom out was taken from: lines, stack,
focus and all. Re-opening is the inverse of zooming out, not an approximation
of it. -/
theorem reopen_undoes_the_zoom_out :
    (session.steps (discharge.take 4 ++ [.zoomOut, .setFocus 3])).toOption
      = (session.steps (discharge.take 4)).toOption := by decide +kernel

/-- A subproof closed *before* later work stays closed: `discharge` takes a step
at the outer level after zooming out, and the three lines of the subproof are
refused where the three of the open level are not. -/
theorem work_after_keeps_the_subproof_closed :
    ((session.steps discharge).toOption.map fun d =>
      (List.range d.lines.size).filter (d.canFocus ·)) = some [0, 4, 5] := by decide +kernel

theorem reopen_reaches_the_first_subproof :
    ((session.steps reopen).toOption.map fun d =>
      (d.depth, (List.range d.lines.size).filter (d.canFocus ·)))
      = some (1, [0, 1, 2, 3, 4]) := by decide +kernel

/-- Clicking into it closes the new level first — a level of one line, so closing
it is the undo the document says it is — and then takes the zoom out back: three
lines left, the first subproof innermost again, the focus where the click
landed. -/
theorem reopen_closes_the_new_level_first :
    ((session.steps (reopen ++ [.setFocus 1])).toOption.map fun d =>
      (d.focus, d.depth, d.lines.size)) = some (1, 1, 3) := by decide +kernel

/-- Two levels deep, two clicks go all the way back in: `nested` closes both
levels with one click on line 0, and clicking the innermost line re-opens both,
one `Doc.reopenStep` each. -/
theorem nested_reopens_both_levels :
    ((session.steps (nested ++ [.setFocus 3])).toOption.map fun d =>
      (d.focus, d.depth, d.lines.size, d.contextLaws.length))
      = some (3, 2, 4, 2) := by decide +kernel

end Replay
end Ampheck
