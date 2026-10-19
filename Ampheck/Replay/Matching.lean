import Ampheck.Replay.Sessions

/-!
# Replays: gaps, matching, parts, segments and the collapses

A gap closed, matching modulo associativity, symmetry and the identity, the order
of the suggestions, laws applied to a part and to a segment of a line, the display
collapses, a gap carried out of a subproof, and a segment zoomed in to. Each is
checked by evaluation in Lean's kernel, as `Ampheck.Replay` explains; the commands
are there, and the sessions in `Ampheck.Replay.Sessions`. These are kept out of
`Ampheck.Replay` because a replay against the shipped laws is expensive to
evaluate in the kernel, and `lake build ampheck` should not have to; `lake build
AmpheckReplay` builds them.
-/

namespace Ampheck
namespace Replay

open Expr (var mvar num bin neg)

set_option maxRecDepth 100000

/-! ### A gap, and closing it -/

/-- Direct entry really does leave a gap … -/
theorem gap_is_open :
    ((session.steps (gap.take 2)).toOption.map Doc.gaps) = some [0] := by decide +kernel

/-- … and taking the suggestion closes it, leaving a proof of `¬¬a = a`. -/
theorem gap_is_closed :
    ((session.steps gap).toOption.map Doc.gaps) = some [] := by decide +kernel

theorem gap_proves :
    proved gap = some (bin .eq (neg (neg (var "a"))) (var "a")) := by decide +kernel

/-! ### Matching modulo associativity, symmetry and the identity -/

/-- Specialization offers every sub-conjunction of `x ∧ y ∧ z`: the three single
conjuncts and the three pairs. Only `x ∧ y` was offered before matching went
modulo associativity, and only `x` and `x ∧ y` before it went modulo symmetry.

All six are whole-line steps that can be taken as they stand, so what orders them
is `Doc.rank`'s shorter-line key — the single conjuncts before the pairs — and
then the order matching found them, which is `x`, `x ∧ y`, `y ∧ z`, `x ∧ z`, `z`,
`y`, the readings needing no rearrangement first. -/
theorem specialization_reads_every_way :
    suggestedBy "specialization" .down conjunction
      = [(.imp, var "x"), (.imp, var "z"), (.imp, var "y"),
         (.imp, bin .and (var "x") (var "y")),
         (.imp, bin .and (var "y") (var "z")),
         (.imp, bin .and (var "x") (var "z"))] := by decide +kernel

/-- Symmetry rearranges the three operands every way but the one it started
with, which the identity-rewrite gate drops. Every one writes a line of the same
size, so the shorter-line key cannot separate them and `Doc.rank` falls to the
place: the five whole-line swaps first, then the two that come from the *segment*
sites — `x ∧ y` and `y ∧ z`, each turned around where it stands and the third
operand left alone, which is why a swap inside a longer association needs no
zoom. -/
theorem symmetry_reads_every_way :
    suggestedBy "symmetry" .down conjunction
      = [(.eq, bin .and (bin .and (var "y") (var "z")) (var "x")),
         (.eq, bin .and (var "z") (bin .and (var "x") (var "y"))),
         (.eq, bin .and (var "x") (bin .and (var "y") (var "z"))),
         (.eq, bin .and (var "y") (bin .and (var "x") (var "z"))),
         (.eq, bin .and (bin .and (var "x") (var "z")) (var "y")),
         (.eq, bin .and (bin .and (var "y") (var "x")) (var "z")),
         (.eq, bin .and (var "x") (bin .and (var "z") (var "y")))] := by decide +kernel

/-! ### The order the suggestions come in -/

/-- For `x ∧ y ∧ z` under the whole shipped law list, the suggestions' keys never
go backwards, and ranking the ranked list is the ranked list. -/
theorem suggestions_are_ranked :
    ((session.steps [.start .boolean .down conjunction]).toOption.map fun d =>
      (ranked (d.suggestions.map key), Doc.rank d.suggestions == d.suggestions))
      = some (true, true) := by decide +kernel

theorem assoc_proves : proved assoc = some (bin .imp conjunction (var "x")) := by decide +kernel

theorem assoc_complete :
    ((session.steps assoc).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

theorem swap_proves :
    proved swap = some (bin .imp (bin .and (var "x") (var "y")) (var "y")) := by decide +kernel

theorem swap_complete :
    ((session.steps swap).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

/-! ### A law applied to a part of a line -/

theorem minimize_proves :
    proved minimize = some (bin .eq part (bin .and (var "x") (var "y"))) := by decide +kernel

theorem minimize_complete :
    ((session.steps minimize).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

/-! ### A law applied to a contiguous segment of an association -/

theorem segmentFold_proves :
    provedIn segmentSession segmentFold
      = some (bin .eq segmentLine (bin .and (bin .and (var "x") (var "y")) (var "z"))) := by
  decide

theorem segmentFold_complete :
    ((segmentSession.steps segmentFold).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

/-- And it is the only way idempotence reaches `x ∧ y ∧ z` from that line: one
suggestion, from the one segment that matches. -/
theorem segmentFold_is_the_only_fold :
    ((segmentSession.steps [.start .boolean .same segmentLine]).toOption.map fun d =>
      (d.suggestions.filter fun s =>
        s.law == "idempotent" && s.result == bin .and (bin .and (var "x") (var "y")) (var "z")).length)
      = some 1 := by decide +kernel

/-- And the suggestion is *credited to the run it rewrites*: `Suggestion.part`
carries the site, which is what ranks a step by how specific its place is and
what lets a window draw which part of the line a step would rewrite. The fold is
credited to `y ∧ y`, the run of two operands from the first; a law that reads the
whole line is credited to the whole line. -/
theorem segmentFold_is_credited_to_the_run :
    ((segmentSession.steps [.start .boolean .same segmentLine]).toOption.map fun d =>
      ((d.suggestions.filter fun s =>
          s.law == "idempotent"
            && s.result == bin .and (bin .and (var "x") (var "y")) (var "z")).map
        Suggestion.part,
       (d.suggestions.filter fun s =>
          s.law == "double negation" && s.result == neg (neg segmentLine)).map
        Suggestion.part))
      = some ([.segment 1 2], [.whole]) := by decide +kernel

/-! ### The display collapses -/

theorem fold_proves :
    proved fold = some (bin .eq part (bin .and (var "x") (var "y"))) := by decide +kernel

/-- The document keeps all four lines … -/
theorem fold_keeps_its_four_lines :
    ((session.steps fold).toOption.map fun d => d.lines.size) = some 4 := by decide +kernel

/-- … and the display draws two: the subproof was a single law application, so
it folds into the line it was zoomed in from and `idempotent` moves up onto
that line. Lines 1 and 2 are not drawn; line 3 still answers to `focus 3`. -/
theorem fold_collapses :
    ((session.steps fold).toOption.map Doc.shownLines)
      = some [{ index := 0, depth := 0, note := "idempotent" },
              { index := 3, depth := 0, note := "" }] := by decide +kernel

/-- And what is drawn is, line for line, what `minimize` draws: the long way
round and the short way round look the same, which is the point of the fold. -/
theorem fold_shows_what_minimize_shows : shown fold = shown minimize := by decide +kernel

theorem merge_proves :
    proved merge
      = some (bin .eq nest
                (bin .and (var "x") (bin .or (var "y") (var "z")))) := by decide +kernel

/-- Seven lines in the document … -/
theorem merge_keeps_its_seven_lines :
    ((session.steps merge).toOption.map fun d => d.lines.size) = some 7 := by decide +kernel

/-- … five drawn, at one level of nesting rather than two. The middle level —
line 1, which the first zoom in wrote, and line 5, which the first zoom out
wrote — held nothing of its own, so the subproof it held is drawn a level
further out and those two lines are not drawn at all. The inner subproof is two
steps long, so it is not folded away as well. -/
theorem merge_collapses :
    ((session.steps merge).toOption.map Doc.shownLines)
      = some [{ index := 0, depth := 0, note := "" },
              { index := 2, depth := 1, note := "idempotent" },
              { index := 3, depth := 1, note := "double negation" },
              { index := 4, depth := 1, note := "" },
              { index := 6, depth := 0, note := "" }] := by decide +kernel

theorem mergeThenFold_collapses :
    ((session.steps mergeThenFold).toOption.map Doc.shownLines)
      = some [{ index := 0, depth := 0, note := "idempotent" },
              { index := 5, depth := 0, note := "" }] := by decide +kernel

/-- Nothing is collapsed while the level is still open: after the inner zoom
out of `merge`, the middle level is where the user is working, and all six
lines written so far are drawn. A collapse waits for the matching zoom out. -/
theorem merge_waits_for_the_zoom_out :
    ((session.steps (merge.take 6)).toOption.map fun d =>
      (d.lines.size, d.shownLines.length)) = some (6, 6) := by decide +kernel

/-- All four lines are drawn, and *two* warning signs are drawn: the one inside
the subproof, on the line the direct entry was made after, and the one the zoom
out carried out to the line it zoomed in from. Nothing folds — the subproof's
step is not a law's. -/
theorem gapInside_is_not_collapsed :
    ((session.steps gapInside).toOption.map fun d =>
      (d.shownLines.length, d.shownLines.map Shown.note))
      = some (4, ["!", "!", "", ""]) := by decide +kernel

/-! ### A gap carried out of the subproof that holds it -/

/-- The line zoomed in from (line 0) carries a gap of its own, beside the one
line 1 carries inside the subproof. Before this, line 0 carried none and the
outer step showed neither a law name nor a warning sign. -/
theorem gapInside_gaps_the_line_before_the_splice :
    ((session.steps gapInside).toOption.map fun d => (d.gaps, d.note 0))
      = some ([0, 1], "!") := by decide +kernel

/-- And the proof does not claim anything: the outer level has a gap in it, so
`Doc.outcome` refuses even though the subproof has been closed. -/
theorem gapInside_proves_nothing : proved gapInside = none := by decide +kernel

/-- Re-opening takes the carried gap back with the line that carried it out: a
click on the subproof's bottom line leaves the gap the direct entry made inside
the level, and nothing on the line above it. -/
theorem reopen_takes_the_carried_gap_back :
    ((session.steps (gapInside ++ [.setFocus 2])).toOption.map fun d =>
      (d.depth, d.lines.size, d.gaps)) = some (1, 3, [1]) := by decide +kernel

/-- And zooming out again carries it out again, writing the very document the
first zoom out wrote: the splice and the warning sign on the line before it come
back as they were. Going back in and out of a subproof that holds a gap changes
nothing. -/
theorem reopen_then_zoom_out_is_the_same_document :
    (session.steps (gapInside ++ [.setFocus 2, .zoomOut])).toOption
      = (session.steps gapInside).toOption := by decide +kernel

/-- A justified subproof splices as it always did. `fold`'s subproof is a single
law application: no gap is carried out, line 0 keeps the law's name — lifted by
the fold — and the proof stands. -/
theorem fold_splices_without_a_gap :
    ((session.steps fold).toOption.map fun d => (d.gaps, d.note 0))
      = some ([], "") := by decide +kernel

/-- Neither does a *longer* justified subproof: `merge`'s inner level is two law
steps, and the outer line before the splice is left unannotated, its
justification being the lines inside. -/
theorem merge_splices_without_a_gap :
    ((session.steps merge).toOption.map fun d => (d.gaps, d.note 0))
      = some ([], "") := by decide +kernel

theorem gapCarries_carries_it_all_the_way_out :
    ((session.steps gapCarries).toOption.map fun d => (d.gaps, d.note 0))
      = some ([0, 1, 2], "!") := by decide +kernel

/-- The merge would have drawn those six lines as four, and it does not: a
collapse never hides a line a warning sign hangs on, and now there is one at
each level. -/
theorem gapCarries_is_not_collapsed :
    ((session.steps gapCarries).toOption.map fun d =>
      (d.shownLines.length, d.shownLines.map Shown.note))
      = some (6, ["!", "!", "!", "", "", ""]) := by decide +kernel

/-- A click that abandons a gappy subproof carries the gap out too, because
`Doc.closeToDepth` closes the levels by running `Doc.zoomOut`: `focus 0` in
place of the two zoom-outs writes the very same document. -/
theorem gapCarries_is_the_same_by_clicking :
    (session.steps (gapCarries.take 4 ++ [.setFocus 0])).toOption.map (fun d => d.lines.toList)
      = (session.steps gapCarries).toOption.map (fun d => d.lines.toList) := by decide +kernel

/-! ### A segment as a level: zooming in to a run of operands -/

/-- The level the zoom opens has the segment for its first line, built
left-associated as `Expr.segmentExpr` builds it. -/
theorem segmentZoom_opens_the_segment :
    ((session.steps (segmentZoom.take 2)).toOption.map fun d =>
      d.lines.toList.map fun l => (l.depth, l.expr))
      = some [(0, segmentLine), (1, bin .and (var "y") (var "y"))] := by decide +kernel

/-- And the frame remembers which run it was, with the type, direction and
position the segment *site* carries — which is what lets the zoom out splice the
subproof back where it came from. -/
theorem segmentZoom_remembers_the_run :
    ((session.steps (segmentZoom.take 2)).toOption.bind fun d =>
      d.frame?.map fun f => (f.ty, f.dir, f.pos, f.part))
      = some (.boolean, .same, .positive, .segment 1 2) := by decide +kernel

/-- Zooming in to a segment of a conjunction gains the operands *outside* the
run as context, exactly as zooming in to one operand gains the other three:
here `x` and `z`. -/
theorem segmentZoom_gains_the_others :
    ((session.steps (segmentZoom.take 2)).toOption.map fun d =>
      d.contextLaws.map Law.stmt) = some [var "x", var "z"] := by decide +kernel

/-- A segment of `×` is neutral — the document's position table leaves `×` out,
since a factor is monotonic only for a nonnegative other — so zooming in to one
flattens the direction to `=`, whatever the level's was. That is the rule
`times_segments_are_neutral` reads off the site, now read off the level. -/
theorem times_segment_zoom_is_neutral :
    ((session.steps
        [ .start .number .down (bin .mul (bin .mul (var "n") (var "m")) (var "k")),
          .zoomIn (.segment 0 2) ]).toOption.bind fun d =>
      d.frame?.map fun f => (f.ty, f.dir, f.pos)) = some (.number, .same, .neutral) := by decide +kernel

/-- The whole line is not a level of its own, so `Part.whole` is refused: it is
the level one is already on. -/
theorem the_whole_line_is_not_a_zoom_target :
    (session.steps [.start .boolean .same segmentLine, .zoomIn .whole]).isOk = false := by decide +kernel

/-- It proves what the one-step segment rewrite proves. -/
theorem segmentZoom_proves :
    provedIn segmentSession segmentZoom
      = some (bin .eq segmentLine (bin .and (bin .and (var "x") (var "y")) (var "z"))) := by
  decide

theorem segmentZoom_complete :
    ((segmentSession.steps segmentZoom).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

/-- And the line the zoom out splices is, connective and formula, the line
`segmentFold` writes in one step: the long way round and the short way round
write the same thing, because both put the part back through `Part.replace`. -/
theorem segmentZoom_splices_what_the_site_writes :
    ((segmentSession.steps segmentZoom).toOption.bind fun d =>
        d.lines.toList.getLast?.map fun l => (l.conn, l.expr))
      = ((segmentSession.steps segmentFold).toOption.bind fun d =>
        d.lines.toList.getLast?.map fun l => (l.conn, l.expr)) := by decide +kernel

/-- The document keeps all four lines, and the display draws two: the subproof is
a single law application, so it folds into the line it was zoomed in from with
`idempotent` moved up — line for line what `segmentFold` draws. The collapses
needed nothing added for segment zooms. -/
theorem segmentZoom_collapses :
    ((segmentSession.steps segmentZoom).toOption.map fun d => (d.lines.size, d.shownLines))
      = some (4, [{ index := 0, depth := 0, note := "idempotent" },
                  { index := 3, depth := 0, note := "" }]) := by decide +kernel

theorem segmentZoom_shows_what_segmentFold_shows :
    shownIn segmentSession segmentZoom = shownIn segmentSession segmentFold := by decide +kernel

end Replay
end Ampheck
