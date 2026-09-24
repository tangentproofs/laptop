import Netty.Script
import Netty.Laws

/-!
# The document's example, replayed and checked in Lean

The Netty document opens with a short proof:

```
⇐  a ⇒ (b⇒a)  portation
=  a∧b ⇒ a    specialization
=  T
```

This module drives the kernel through it and proves, by evaluation in Lean's
kernel, that the session ends with no gaps, fully zoomed out, and proving
exactly `a ⇒ (b ⇒ a)`. Nothing here is a test in the usual sense: `Doc.step`,
`Doc.suggestions` and `Doc.outcome` are total functions on first-order data and
`Netty.Laws.boolean` is a literal, so `decide` settles the whole replay.

More replays are checked the same way: one that zooms in to a subexpression and
uses the context that zooming in supplies, one that reaches an outer line by a
click instead of by zooming out, one that goes back *into* a subproof it had
zoomed out of — and one that is refused because work was written after that
subproof closed — one that leaves a gap by direct entry and then closes it, one that applies a law to a *part* of a line instead of to the whole
of it, one that applies a law to a contiguous *segment* of an association that
neither the whole line nor a single operand can reach, one that zooms *into* such
a segment and splices it back, and two that exercise the
display collapses — a one-step subproof folded
into its parent line, and two zoom-ins matched by two zoom-outs drawn as one
zoom step.

`Netty.Demo` holds several of these proofs as *scripts*, which is what
`lake exe netty --demo=…` runs; `netty --selftest` checks that parsing each
script yields exactly the command list checked here, so the two cannot drift
apart.
-/

namespace Netty
namespace Replay

open Expr (var mvar num bin neg)

/-! ### The document's directions for zooming in

"positive position and any old direction makes the same new direction; negative
position and old direction ≤ makes new direction ≥ …" -/

example : Dir.zoom .down .positive = .down := by decide
example : Dir.zoom .up .positive = .up := by decide
example : Dir.zoom .down .negative = .up := by decide
example : Dir.zoom .up .negative = .down := by decide
example (p : Pos) : Dir.zoom .same p = .same := by cases p <;> decide
example (d : Dir) : Dir.zoom d .neutral = .same := by cases d <;> decide

/-! ### `a ⇒ (b ⇒ a)`, by portation and specialization -/

/-- `a ⇒ (b ⇒ a)`, the formula the document's example proves. -/
def goal : Expr := bin .imp (var "a") (bin .imp (var "b") (var "a"))

/-- The commands of the document's example. -/
def portation : List Cmd :=
  [ .start .boolean .up goal,
    .applyNamed "portation" none,
    .applyNamed "specialization" (some (.eq, .top)) ]

/-- A session with the shipped boolean laws and nothing else. -/
def session : Doc := { laws := Laws.boolean }

/-- Running a list of commands in a session and asking what it proves. -/
def provedIn (d : Doc) (cs : List Cmd) : Option Expr :=
  ((d.steps cs).toOption.bind fun d => d.outcome.toOption).map Outcome.proved

/-- Running a list of commands and asking what the proof proves. -/
def proved (cs : List Cmd) : Option Expr := provedIn session cs

/-- The lines of a finished replay, for the record. -/
def lines (cs : List Cmd) : Option (List (Option BinOp × Expr)) :=
  (session.steps cs).toOption.map fun d => d.lines.toList.map fun l => (l.conn, l.expr)

set_option maxRecDepth 100000

/-- The document's example proves `a ⇒ (b ⇒ a)`. -/
theorem portation_proves : proved portation = some goal := by decide

/-- Its proof pane is the document's three lines: the goal, `a ∧ b ⇒ a`, `⊤`,
joined by `=`. -/
theorem portation_lines :
    lines portation =
      some [(none, goal),
            (some .eq, bin .imp (bin .and (var "a") (var "b")) (var "a")),
            (some .eq, .top)] := by decide

/-- It leaves no gap, and ends at the outermost level. -/
theorem portation_complete :
    ((session.steps portation).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide

/-! ### Zooming in, and the context a zoom in supplies -/

/-- `(a ⇒ b) ⇒ (a ⇒ a ∧ b)`. -/
def dischargeGoal : Expr :=
  bin .imp (bin .imp (var "a") (var "b"))
    (bin .imp (var "a") (bin .and (var "a") (var "b")))

/-- Zoom in to the consequent — where `a ⇒ b` is context — discharge it, use
the context, zoom out, and finish with a base law. -/
def discharge : List Cmd :=
  [ .start .boolean .up dischargeGoal,
    .zoomIn (.operand 1),
    .applyNamed "discharge" (some (.eq, bin .imp (var "a") (var "b"))),
    -- The context law `a ⇒ b` can also be applied to a *part* of the line
    -- `a ⇒ b`, so the line it should write has to be named.
    .applyNamed "context" (some (.eq, .top)),
    .zoomOut,
    .applyNamed "base" (some (.eq, .top)) ]

/-- It proves `(a ⇒ b) ⇒ (a ⇒ a ∧ b)`, with no gap and fully zoomed out. -/
theorem discharge_proves : proved discharge = some dischargeGoal := by decide

theorem discharge_complete :
    ((session.steps discharge).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide

/-! ### The focus lands anywhere: recomputing the zoom stack

The document lets a click land on any line of the proof. Focusing a line of an
*outer* level closes the levels that sit below it, exactly as a run of zoom-outs
would, so nothing is lost: each abandoned subproof still puts its bottom line
back into the line it was zoomed in from. -/

/-- The `discharge` proof again, but where `discharge` zooms out, this one
clicks on line 0 — the outermost line — and then carries on at that level. -/
def anywhere : List Cmd :=
  [ .start .boolean .up dischargeGoal,
    .zoomIn (.operand 1),
    .applyNamed "discharge" (some (.eq, bin .imp (var "a") (var "b"))),
    .applyNamed "context" (some (.eq, .top)),
    .setFocus 0,
    .setFocus 4,
    .applyNamed "base" (some (.eq, .top)) ]

/-- Clicking line 0 while two levels deep in the proof leaves the focus there,
the stack back at the outermost level, and no context: the zoom in's facts went
out with its frame. The subproof's own lines stay in the document, and the line
the zoom out wrote is line 4. -/
theorem anywhere_closes_the_stack :
    ((session.steps (anywhere.take 5)).toOption.map fun d =>
      (d.focus, d.stack.length, d.contextLaws.length, d.lines.size))
      = some (0, 1, 0, 5) := by decide

/-- Every line is focusable: the two of the outermost level because they are
open, and the three of the closed subproof because the zoom out that closed it
is the last line of this level and can be taken back. -/
theorem anywhere_leaves_every_line_open_to_a_click :
    ((session.steps (anywhere.take 5)).toOption.map fun d =>
      (List.range d.lines.size).filter (d.canFocus ·)) = some [0, 1, 2, 3, 4] := by decide

/-- Three of them re-open the subproof; the two of the open level do not. -/
theorem anywhere_says_which_clicks_reopen :
    ((session.steps (anywhere.take 5)).toOption.map fun d =>
      (List.range d.lines.size).filter (d.reopensOn ·)) = some [1, 2, 3] := by decide

/-- Carrying on from there proves what `discharge` proves … -/
theorem anywhere_proves : proved anywhere = some dischargeGoal := by decide

/-- … and in fact writes the very same document: clicking an outer line did
what `Cmd.zoomOut` does. -/
theorem anywhere_is_discharge :
    ((session.steps anywhere).toOption.map fun d => d.lines.toList)
      = ((session.steps discharge).toOption.map fun d => d.lines.toList) := by decide

/-- Two levels deep, one click closes both. Here the inner subproof rewrites
`a ∧ b` to `b ∧ a`, and focusing line 0 writes the two lines the two zoom-outs
would have written. -/
def nested : List Cmd :=
  [ .start .boolean .up dischargeGoal,
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .applyNamed "symmetry" (some (.eq, bin .and (var "b") (var "a"))),
    .setFocus 0 ]

theorem nested_closes_both_levels :
    ((session.steps nested).toOption.map fun d =>
      (d.focus, d.stack.length, d.contextLaws.length, d.lines.size))
      = some (0, 1, 0, 6) := by decide

/-- The bottom line is the goal with `a ∧ b` turned around, which is what the
two zoom-outs put back. -/
theorem nested_puts_the_subproofs_back :
    ((session.steps nested).toOption.bind fun d => d.lines[5]?.map Line.expr)
      = some (bin .imp (bin .imp (var "a") (var "b"))
                (bin .imp (var "a") (bin .and (var "b") (var "a")))) := by decide

/-! ### Going back into a closed subproof

A click may land on a line of a subproof that has already been zoomed out of.
The kernel takes that zoom out back — `Doc.reopenStep`, its exact inverse — so
the level is innermost again with its context in force, and the focus is on the
line that was clicked. What it refuses is a subproof closed *before* later work
was written: undoing the zoom out would undo the work. -/

/-- Clicking a line of the closed subproof puts the focus there, one level deep,
with the line the zoom out wrote taken back — four lines where there were five —
and the context the zoom in supplied in force again. -/
theorem click_reopens_the_subproof :
    ((session.steps (anywhere.take 5 ++ [.setFocus 2])).toOption.map fun d =>
      (d.focus, d.depth, d.lines.size, d.contextLaws.length))
      = some (2, 1, 4, 1) := by decide

/-- And it writes back the very state the zoom out was taken from: lines, stack,
focus and all. Re-opening is the inverse of zooming out, not an approximation
of it. -/
theorem reopen_undoes_the_zoom_out :
    (session.steps (discharge.take 4 ++ [.zoomOut, .setFocus 3])).toOption
      = (session.steps (discharge.take 4)).toOption := by decide

/-- A subproof closed *before* later work stays closed: `discharge` takes a step
at the outer level after zooming out, and the three lines of the subproof are
refused where the three of the open level are not. -/
theorem work_after_keeps_the_subproof_closed :
    ((session.steps discharge).toOption.map fun d =>
      (List.range d.lines.size).filter (d.canFocus ·)) = some [0, 4, 5] := by decide

/-- A new level open at the same depth is no obstacle: zoom in, step, zoom out,
zoom in again, and every line is still reachable. -/
def reopen : List Cmd :=
  [ .start .boolean .up dischargeGoal,
    .zoomIn (.operand 1),
    .applyNamed "discharge" (some (.eq, bin .imp (var "a") (var "b"))),
    .zoomOut,
    .zoomIn (.operand 1) ]

theorem reopen_reaches_the_first_subproof :
    ((session.steps reopen).toOption.map fun d =>
      (d.depth, (List.range d.lines.size).filter (d.canFocus ·)))
      = some (1, [0, 1, 2, 3, 4]) := by decide

/-- Clicking into it closes the new level first — a level of one line, so closing
it is the undo the document says it is — and then takes the zoom out back: three
lines left, the first subproof innermost again, the focus where the click
landed. -/
theorem reopen_closes_the_new_level_first :
    ((session.steps (reopen ++ [.setFocus 1])).toOption.map fun d =>
      (d.focus, d.depth, d.lines.size)) = some (1, 1, 3) := by decide

/-- Two levels deep, two clicks go all the way back in: `nested` closes both
levels with one click on line 0, and clicking the innermost line re-opens both,
one `Doc.reopenStep` each. -/
theorem nested_reopens_both_levels :
    ((session.steps (nested ++ [.setFocus 3])).toOption.map fun d =>
      (d.focus, d.depth, d.lines.size, d.contextLaws.length))
      = some (3, 2, 4, 2) := by decide

/-! ### Conditional laws at the number level

A law such as `x ≤ x + y ⇐ 0 ≤ y` has `⇐` for its main operator, so its
unconditional readings are steps a *boolean* line can take. What makes it a step a
number line can take is its *conditional* reading (`Law.conditional`): the
consequent `x ≤ x + y` is a relation that stands in a number margin, with `0 ≤ y`
left over as a premise. A premise the laws in force settle is no premise at all;
one they do not settle leaves the document's warning sign, the same gap direct
entry leaves, with the premise recorded on the line as what would close it. -/

/-- The boolean laws together with the small number list. -/
def conditionalSession : Doc := { laws := Laws.boolean ++ Laws.number }

/-- The context discharges a premise: a `context` law is exactly the premise. -/
theorem context_settles_the_premise :
    Law.settles [Law.context (bin .le (num 0) (var "m"))] (bin .le (num 0) (var "m"))
      = true := by decide

/-- So does a law of the list, when the premise is an instance of one side it
equates with `⊤`: `0 ≤ 0` is settled by `x ≤ x`. -/
theorem a_law_settles_a_ground_premise :
    Law.settles Laws.number (bin .le (num 0) (num 0)) = true := by decide

/-- And `0 ≤ m` is settled by neither: nothing in the list says it, so a step
that needs it is a step with a gap. -/
theorem nothing_settles_zero_le_m :
    Law.settles Laws.number (bin .le (num 0) (var "m")) = false := by decide

/-- `0 ≤ m ⇒ n ≤ n + m`. -/
def boundGoal : Expr :=
  bin .imp (bin .le (num 0) (var "m")) (bin .le (var "n") (bin .add (var "n") (var "m")))

/-- Zoom in to the consequent, where `0 ≤ m` becomes context; zoom in again to
`n + m`, which is a *number* level; and there the conditional law fires, its
premise discharged by that context. Then out, and the two boolean steps that
finish it. -/
def bound : List Cmd :=
  [ .start .boolean .up boundGoal,
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .applyNamed "upper bound" (some (.ge, var "n")),
    .zoomOut,
    .applyNamed "reflexive" (some (.eq, .top)),
    .zoomOut,
    .applyNamed "base" (some (.eq, .top)) ]

/-- It proves `0 ≤ m ⇒ n ≤ n + m`, with no gap and fully zoomed out: the premise
was discharged, so nothing is left over. -/
theorem bound_proves : provedIn conditionalSession bound = some boundGoal := by decide

theorem bound_complete :
    ((conditionalSession.steps bound).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide

/-- At that number level the law is offered twice, `+` being symmetric, and the
two differ in exactly the way the document says they should: writing `n` needs
`0 ≤ m`, which the context settles, so it carries no premise; writing `m` needs
`0 ≤ n`, which nothing settles, so it says so before it is taken. -/
theorem bound_offers_discharged_and_gapped :
    ((conditionalSession.steps (bound.take 3)).toOption.map fun d =>
      (d.suggestions.filter (·.law == "upper bound")).map fun s => (s.op, s.result, s.premise))
      = some [(.ge, var "n", none), (.ge, var "m", some (bin .le (num 0) (var "n")))] := by decide

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

/-- The same law on the same line with nothing in force to settle its premise:
a number proof started at `n + m`. -/
def gapped : List Cmd :=
  [ .start .number .up (bin .add (var "n") (var "m")),
    .applyNamed "upper bound" (some (.ge, var "n")) ]

/-- Taking it writes the line and leaves the warning sign on the line the step was
taken from, with the premise recorded there as what would close it. -/
theorem gapped_leaves_the_premise_as_a_gap :
    ((conditionalSession.steps gapped).toOption.map fun d =>
      (d.gaps, d.note 0, d.lines[0]?.bind Line.premise))
      = some ([0], "!", some (bin .le (num 0) (var "m"))) := by decide

/-- And the proof claims nothing, exactly as a gap left by direct entry makes it
claim nothing: the premise is a hole in the calculation, not a footnote to it. -/
theorem gapped_proves_nothing : provedIn conditionalSession gapped = none := by decide

/-- The line it wrote is the one the law licenses, and it carries the law's name:
the step is not refused, it is recorded as conditional. -/
theorem gapped_writes_the_law_s_line :
    ((conditionalSession.steps gapped).toOption.bind fun d =>
      d.lines[1]?.map fun l => (l.conn, l.expr, l.why))
      = some (some .ge, var "n", "upper bound") := by decide

/-! ### A gap, and closing it -/

/-- Type `a` in directly under `¬¬a`, which leaves a warning sign; then move
the focus back and take the suggestion that writes the line already there,
which replaces the sign with the law's name. -/
def gap : List Cmd :=
  [ .start .boolean .up (neg (neg (var "a"))),
    .direct .eq (var "a"),
    .setFocus 0,
    .applyNamed "double negation" (some (.eq, var "a")) ]

/-- Direct entry really does leave a gap … -/
theorem gap_is_open :
    ((session.steps (gap.take 2)).toOption.map Doc.gaps) = some [0] := by decide

/-- … and taking the suggestion closes it, leaving a proof of `¬¬a = a`. -/
theorem gap_is_closed :
    ((session.steps gap).toOption.map Doc.gaps) = some [] := by decide

theorem gap_proves :
    proved gap = some (bin .eq (neg (neg (var "a"))) (var "a")) := by decide

/-! ### Matching modulo associativity, symmetry and the identity

The document says that clicking on any operand of `a + b + c` zooms in to it,
with no need of associative laws, and it has `symmetry` and `identity` laws that
a user should likewise not have to spend a step on. Applying a law reads a line
modulo all three: `specialization`, `a ∧ b ⇒ a`, matches `x ∧ y ∧ z` — which is
`(x ∧ y) ∧ z` — with `a := x` and `b := y ∧ z` as readily as with `a := x ∧ y`
and `b := z`, and, since `∧` is symmetric, with `a := y` and `b := x ∧ z` too. -/

/-- `x ∧ y ∧ z`, read as `(x ∧ y) ∧ z`. -/
def conjunction : Expr := bin .and (bin .and (var "x") (var "y")) (var "z")

/-- What the laws named `name` suggest for a proof of one line. -/
def suggestedBy (name : String) (dir : Dir) (e : Expr) : List (BinOp × Expr) :=
  match (session.steps [.start .boolean dir e]).toOption with
  | some d => (d.suggestions.filter (·.law == name)).map fun s => (s.op, s.result)
  | none => []

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
         (.imp, bin .and (var "x") (var "z"))] := by decide

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
         (.eq, bin .and (var "x") (bin .and (var "z") (var "y")))] := by decide

/-! ### The order the suggestions come in

Every widening of matching lengthened the list, and `Doc.rank` is the order it is
offered in: applicable before unconstrained, then fewer unconstrained variables,
then the shorter line the step writes, then the more specific place, then the law
file's own order. Rather than write a hundred-line list out, what is checked here
is that the keys never go backwards — which is what it means for the list to be in
that order — and that ranking an already ranked list changes nothing, which is
what it means for the order to be total and the sort stable. -/

/-- The numbers `Doc.rank` sorts by, most important first. -/
def key (s : Suggestion) : List Nat :=
  [if s.holes.isEmpty then 0 else 1, s.holes.length, s.result.size, s.part.rank]

/-- Lexicographic `≤` on those keys. -/
def leKey : List Nat → List Nat → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => if a == b then leKey as bs else a < b

/-- Whether a list of keys never goes backwards. -/
def ranked : List (List Nat) → Bool
  | k :: j :: rest => leKey k j && ranked (j :: rest)
  | _ => true

/-- For `x ∧ y ∧ z` under the whole shipped law list, the suggestions' keys never
go backwards, and ranking the ranked list is the ranked list. -/
theorem suggestions_are_ranked :
    ((session.steps [.start .boolean .down conjunction]).toOption.map fun d =>
      (ranked (d.suggestions.map key), Doc.rank d.suggestions == d.suggestions))
      = some (true, true) := by decide

/-- A proof that the reading associativity adds really can be taken: one step
from `x ∧ y ∧ z` to `x`, where before it took an associative law first. -/
def assoc : List Cmd :=
  [ .start .boolean .down conjunction,
    .applyNamed "specialization" (some (.imp, var "x")) ]

theorem assoc_proves : proved assoc = some (bin .imp conjunction (var "x")) := by decide

theorem assoc_complete :
    ((session.steps assoc).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide

/-- And one that symmetry adds: `x ∧ y ⇒ y`, in one step. No cut of `x ∧ y`
into contiguous segments gives `a := y`, so before this the proof needed the
symmetry law first. -/
def swap : List Cmd :=
  [ .start .boolean .down (bin .and (var "x") (var "y")),
    .applyNamed "specialization" (some (.imp, var "y")) ]

theorem swap_proves :
    proved swap = some (bin .imp (bin .and (var "x") (var "y")) (var "y")) := by decide

theorem swap_complete :
    ((session.steps swap).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide

/-- A pattern operand that is not a law variable takes one operand and no
more: `a ∧ (b ∨ c)` cannot read `x ∧ y ∧ z`, because no part of it is a
disjunction — not even now that the parts need not be contiguous. -/
theorem no_match_without_a_law_variable :
    Expr.matchAll (bin .and (mvar "a") (bin .or (mvar "b") (mvar "c"))) conjunction [] = [] := by
  decide

/-! ### Symmetry and the identity, at the matcher

The three readings, each in one line. Symmetry lets a pattern operand take
operands that are not next to each other; the identity lets a pattern operand
that *is* the unit take none at all, and lets a unit the line writes be struck
out. What it does not do is let a law *variable* take none — otherwise every
binary law would match every line. -/

/-- `a ∧ b` matches `y ∧ x`, which associativity alone cannot do: the two ways
round are the two matches, the one that needs no rearrangement first. -/
theorem symmetry_matches_a_swap :
    Expr.matchAll (bin .and (mvar "a") (mvar "b")) (bin .and (var "y") (var "x")) []
      = [[("b", var "x"), ("a", var "y")], [("b", var "y"), ("a", var "x")]] := by decide

/-- A law written with a unit reads a line that left it out: `a ∧ ⊤` matches
the bare line `y`. -/
theorem identity_is_elided :
    Expr.matchAll (bin .and (mvar "a") .top) (var "y") [] = [[("a", var "y")]] := by decide

/-- A unit the line writes is struck out of it: `a ∧ a` matches `x ∧ ⊤ ∧ x`,
which it cannot do while the `⊤` is still there to be shared out. -/
theorem identity_is_struck_out :
    Expr.matchAll (bin .and (mvar "a") (mvar "a"))
      (bin .and (bin .and (var "x") .top) (var "x")) [] = [[("a", var "x")]] := by decide

/-- But a law variable never takes the unit the line does not mention, so
`a ∧ b` still does not match a line that is not a conjunction at all. That is
what keeps the identity from making every binary law apply everywhere. -/
theorem a_variable_does_not_take_the_unit :
    Expr.matchAll (bin .and (mvar "a") (mvar "b")) (var "y") [] = [] := by decide

/-- `=` is symmetric without being an association, so it is matched by trying
its two operands both ways round. -/
theorem equality_is_symmetric :
    Expr.matchAll (bin .eq (mvar "a") (var "y")) (bin .eq (var "y") (var "x")) []
      = [[("a", var "x")]] := by decide

/-! ### A law applied to a part of a line

Real Netty applies a law "to a part, as a result of minimization": the law
matches a subexpression of the line and the suggestion rewrites that part in
place. The kernel offers one site per main operand as well as the whole line, so
a step that used to need a zoom in, an application and a zoom out is one
application on the outer line. -/

/-- `x ∧ (y ∨ y)`, whose second main operand idempotence folds. -/
def part : Expr := bin .and (var "x") (bin .or (var "y") (var "y"))

/-- Idempotence does not match `x ∧ (y ∨ y)` at all: its main operator is `∧`,
not `∨`. So the step below is not a whole-line match under any reading. -/
theorem idempotence_misses_the_whole_line :
    Expr.matchAll (bin .or (mvar "a") (mvar "a")) part [] = [] := by decide

/-- It does match the second main operand, and the suggestion rewrites that
part in place, leaving `x` alone. -/
def minimize : List Cmd :=
  [ .start .boolean .same part,
    .applyNamed "idempotent" (some (.eq, bin .and (var "x") (var "y"))) ]

theorem minimize_proves :
    proved minimize = some (bin .eq part (bin .and (var "x") (var "y"))) := by decide

theorem minimize_complete :
    ((session.steps minimize).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide

/-! ### A law applied to a contiguous segment of an association

The document reads `x ∧ y ∧ z` as having the part `y ∧ z` just as it has the part
`y`, so a contiguous run of two or more operands of an association is a site of
its own. An associative operator puts all of its operands in one position, so a
run of them is in that same position: the type, the direction and the connective
a rewrite there writes are word for word those of a single main operand, and the
soundness argument is the one minimization already had. -/

/-- `x ∧ y ∧ y ∧ z`, whose middle two operands idempotence folds. -/
def segmentLine : Expr :=
  bin .and (bin .and (bin .and (var "x") (var "y")) (var "y")) (var "z")

/-- The segments of a four-operand association: every contiguous run of two or
three of its operands. A run of one is a main operand and the run of all four is
the line, so neither is listed. -/
theorem segmentLine_segments :
    segmentLine.segments = [(0, 2), (0, 3), (1, 2), (1, 3), (2, 2)] := by decide

/-- A two-operand association has no segments at all: `x ∧ (y ∨ y)` has the two
main operands `minimize` already reaches, and nothing between them. -/
theorem a_pair_has_no_segments : part.segments = [] := by decide

/-- Idempotence matches neither the whole line — no sharing out of
`x ∧ y ∧ y ∧ z` makes its two halves equal … -/
theorem idempotence_misses_the_whole_association :
    Expr.matchAll (bin .and (mvar "a") (mvar "a")) segmentLine [] = [] := by decide

/-- … nor any single main operand, which are the bare identifiers `x`, `y`, `y`,
`z`. So neither site the kernel had before this can fold the repetition. -/
theorem idempotence_misses_every_operand :
    segmentLine.operands.all
      (fun o => Expr.matchAll (bin .and (mvar "a") (mvar "a")) o [] == []) = true := by decide

/-- The segment `y ∧ y` it does match, and the suggestion folds it where it
stands, leaving `x` and `z` alone. -/
def segmentFold : List Cmd :=
  [ .start .boolean .same segmentLine,
    .applyNamed "idempotent"
      (some (.eq, bin .and (bin .and (var "x") (var "y")) (var "z"))) ]

theorem segmentFold_proves :
    proved segmentFold
      = some (bin .eq segmentLine (bin .and (bin .and (var "x") (var "y")) (var "z"))) := by
  decide

theorem segmentFold_complete :
    ((session.steps segmentFold).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide

/-- And it is the only way idempotence reaches `x ∧ y ∧ z` from that line: one
suggestion, from the one segment that matches. -/
theorem segmentFold_is_the_only_fold :
    ((session.steps [.start .boolean .same segmentLine]).toOption.map fun d =>
      (d.suggestions.filter fun s =>
        s.law == "idempotent" && s.result == bin .and (bin .and (var "x") (var "y")) (var "z")).length)
      = some 1 := by decide

/-- And the suggestion is *credited to the run it rewrites*: `Suggestion.part`
carries the site, which is what ranks a step by how specific its place is and
what lets a window draw which part of the line a step would rewrite. The fold is
credited to `y ∧ y`, the run of two operands from the first; a law that reads the
whole line is credited to the whole line. -/
theorem segmentFold_is_credited_to_the_run :
    ((session.steps [.start .boolean .same segmentLine]).toOption.map fun d =>
      ((d.suggestions.filter fun s =>
          s.law == "idempotent"
            && s.result == bin .and (bin .and (var "x") (var "y")) (var "z")).map
        Suggestion.part,
       (d.suggestions.filter fun s =>
          s.law == "double negation" && s.result == neg (neg segmentLine)).map
        Suggestion.part))
      = some ([.segment 1 2], [.whole]) := by decide

/-- `×` is associative, so it has segments, and its operands are neutral — the
document's position table leaves `×` out, since a factor is monotonic only when
the other is nonnegative. So a segment of it is a neutral site whatever the
level's direction: `=` inside, and `=` in the margin outside. That is the
position table read for a run of operands exactly as it is read for one. -/
theorem times_segments_are_neutral :
    (Doc.sites { ty := .number, dir := .down, start := 0 }
        (bin .mul (bin .mul (var "n") (var "m")) (var "k"))).filterMap
      (fun s => match s.part with
        | .segment start len => some (start, len, s.pos, s.dir)
        | _ => none)
      = [(0, 2, .neutral, .same), (1, 2, .neutral, .same)] := by decide

/-! ### Numbers: the directions are `≤ = ≥`, and a negative position turns them

Nothing about the kernel is boolean; the direction machinery is the same at
every type. Here is the same machinery at the number type, with a law list of
one law, showing that zooming in to the subtrahend of `n - m` — a negative
position — turns the direction from `≤` to `≥`. -/

/-- `x + 0 = x`. -/
def numberIdentity : Law :=
  { name := "identity", vars := ["x"], stmt := bin .eq (bin .add (mvar "x") (num 0)) (mvar "x") }

/-- `x ≤ x + 1`, a law whose main operator is a direction rather than `=`. -/
def numberSuccessor : Law :=
  { name := "successor", vars := ["x"],
    stmt := bin .le (mvar "x") (bin .add (mvar "x") (num 1)) }

/-- A session whose whole law list is those two laws. -/
def numberSession : Doc := { laws := [numberIdentity, numberSuccessor] }

/-- Start at `n - m` going down, zoom in to `m`, rewrite it to `m + 0`, and
zoom back out. -/
def number : List Cmd :=
  [ .start .number .down (bin .sub (var "n") (var "m")),
    .zoomIn (.operand 1),
    .applyNamed "identity" (some (.eq, bin .add (var "m") (num 0))),
    .zoomOut ]

/-- The subtrahend is in a negative position, so the subproof's direction is
`≥` where the proof's was `≤`. -/
theorem number_direction_turns :
    ((numberSession.steps (number.take 2)).toOption.bind
      fun d => d.frame?.map Frame.dir) = some .up := by decide

/-- The subproof proves an equality, so zooming out writes `=`, and the whole
calculation proves `n - m = n - (m + 0)`. -/
theorem number_proves :
    provedIn numberSession number
      = some (bin .eq (bin .sub (var "n") (var "m"))
                      (bin .sub (var "n") (bin .add (var "m") (num 0)))) := by decide

/-! ### A unit the line never writes

`BinOp.identity` names `0` as the unit of `+`, so a law written with it can read
a line that left it out. This is the one shape that matching modulo identity
adds and nothing else can: the line is not an addition at all, and no
rearranging of operands will make it one. -/

/-- `x + 0 ≤ x + 1`, a law written with the unit. -/
def numberUnit : Law :=
  { name := "unit successor", vars := ["x"],
    stmt := bin .le (bin .add (mvar "x") (num 0)) (bin .add (mvar "x") (num 1)) }

/-- A session whose whole law list is that one law. -/
def unitSession : Doc := { laws := [numberUnit] }

/-- Against the bare line `n`, the law reads `n` as `n + 0` and offers
`n + 1` — the only suggestion there is, and one no syntactic match could
make. -/
theorem numberUnit_elides_the_zero :
    ((unitSession.steps [.start .number .down (var "n")]).toOption.map fun d =>
      d.suggestions.map fun s => (s.op, s.result))
      = some [(.le, bin .add (var "n") (num 1))] := by decide

/-- And the step can be taken: `n ≤ n + 1`, with the unit never written. -/
def numberUnitProof : List Cmd :=
  [ .start .number .down (var "n"),
    .applyNamed "unit successor" (some (.le, bin .add (var "n") (num 1))) ]

theorem numberUnit_proves :
    provedIn unitSession numberUnitProof
      = some (bin .le (var "n") (bin .add (var "n") (num 1))) := by decide

/-! ### A part in a negative position, without zooming

`successor` is a `≤` law, and the subtrahend of `n - m` is in a negative
position, so applying it there turns the step around: the margin gets `≥` at
the outer level even though the law wrote `≤` at the part. This is the same
turning `number` above makes with a zoom in and a zoom out, in one step on the
outer line. -/

/-- `n - m ≥ n - (m + 1)`, by `successor` on the subtrahend. -/
def numberMinimize : List Cmd :=
  [ .start .number .up (bin .sub (var "n") (var "m")),
    .applyNamed "successor"
      (some (.ge, bin .sub (var "n") (bin .add (var "m") (num 1)))) ]

theorem numberMinimize_proves :
    provedIn numberSession numberMinimize
      = some (bin .ge (bin .sub (var "n") (var "m"))
                      (bin .sub (var "n") (bin .add (var "m") (num 1)))) := by decide

/-- The turning is the only thing the position can do here: at the whole line,
whose direction is `≥`, `successor`'s `≤` is not allowed in the margin at all,
so the only suggestion it makes is the one on the part. -/
theorem numberMinimize_is_the_only_successor_step :
    ((numberSession.steps [.start .number .up (bin .sub (var "n") (var "m"))]).toOption.map
      fun d => (d.suggestions.filter (·.law == "successor")).map fun s => (s.op, s.result))
      = some [(.ge, bin .sub (var "n") (bin .add (var "m") (num 1)))] := by decide

/-! ### The display collapses

A proof written by zooming keeps lines a reader does not need. The document
collapses two such patterns, and `Doc.shownLines` is that collapse: which lines
a display draws, at what depth, and with what law name at the end of them. The
document itself keeps every line, so what is checked here is the *drawing*. -/

/-- What a display draws: for each line it shows, the depth it is drawn at, its
margin connective, its formula and the name at the end of it. -/
def shown (cs : List Cmd) : Option (List (Nat × Option BinOp × Expr × String)) :=
  (session.steps cs).toOption.map fun d =>
    d.shownLines.map fun s =>
      (s.depth, (d.lines[s.index]!).conn, (d.lines[s.index]!).expr, s.note)

/-- The long way round to `x ∧ y`: zoom in to `y ∨ y`, fold it there, and zoom
back out — the four lines that applying a law to a *part* replaces with two. -/
def fold : List Cmd :=
  [ .start .boolean .same part,
    .zoomIn (.operand 1),
    .applyNamed "idempotent" (some (.eq, var "y")),
    .zoomOut ]

theorem fold_proves :
    proved fold = some (bin .eq part (bin .and (var "x") (var "y"))) := by decide

/-- The document keeps all four lines … -/
theorem fold_keeps_its_four_lines :
    ((session.steps fold).toOption.map fun d => d.lines.size) = some 4 := by decide

/-- … and the display draws two: the subproof was a single law application, so
it folds into the line it was zoomed in from and `idempotent` moves up onto
that line. Lines 1 and 2 are not drawn; line 3 still answers to `focus 3`. -/
theorem fold_collapses :
    ((session.steps fold).toOption.map Doc.shownLines)
      = some [{ index := 0, depth := 0, note := "idempotent" },
              { index := 3, depth := 0, note := "" }] := by decide

/-- And what is drawn is, line for line, what `minimize` draws: the long way
round and the short way round look the same, which is the point of the fold. -/
theorem fold_shows_what_minimize_shows : shown fold = shown minimize := by decide

/-- `x ∧ (y ∨ (¬¬z ∧ ¬¬z))`: two levels down there is a two-step subproof, so
the merge of two zooms has something to leave behind. -/
def nest : Expr :=
  bin .and (var "x")
    (bin .or (var "y") (bin .and (neg (neg (var "z"))) (neg (neg (var "z")))))

/-- Zoom in twice, take two steps, and zoom out twice. -/
def merge : List Cmd :=
  [ .start .boolean .same nest,
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .applyNamed "idempotent" (some (.eq, neg (neg (var "z")))),
    .applyNamed "double negation" (some (.eq, var "z")),
    .zoomOut,
    .zoomOut ]

theorem merge_proves :
    proved merge
      = some (bin .eq nest
                (bin .and (var "x") (bin .or (var "y") (var "z")))) := by decide

/-- Seven lines in the document … -/
theorem merge_keeps_its_seven_lines :
    ((session.steps merge).toOption.map fun d => d.lines.size) = some 7 := by decide

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
              { index := 6, depth := 0, note := "" }] := by decide

/-- A merge can expose a fold: the same two zooms with a *one*-step subproof
inside collapse all the way to two lines, the law's name on the first of them.
The pass is a fixpoint, so both collapses run. -/
def mergeThenFold : List Cmd :=
  [ .start .boolean .same
      (bin .and (var "x") (bin .or (var "y") (bin .and (var "z") (var "z")))),
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .applyNamed "idempotent" (some (.eq, var "z")),
    .zoomOut,
    .zoomOut ]

theorem mergeThenFold_collapses :
    ((session.steps mergeThenFold).toOption.map Doc.shownLines)
      = some [{ index := 0, depth := 0, note := "idempotent" },
              { index := 5, depth := 0, note := "" }] := by decide

/-- Nothing is collapsed while the level is still open: after the inner zoom
out of `merge`, the middle level is where the user is working, and all six
lines written so far are drawn. A collapse waits for the matching zoom out. -/
theorem merge_waits_for_the_zoom_out :
    ((session.steps (merge.take 6)).toOption.map fun d =>
      (d.lines.size, d.shownLines.length)) = some (6, 6) := by decide

/-- A gap is never collapsed away: the same fold, but with the subproof's one
step typed in directly instead of taken from a law, keeps all four lines and
its warning sign. -/
def gapInside : List Cmd :=
  [ .start .boolean .same part,
    .zoomIn (.operand 1),
    .direct .eq (var "y"),
    .zoomOut ]

/-- All four lines are drawn, and *two* warning signs are drawn: the one inside
the subproof, on the line the direct entry was made after, and the one the zoom
out carried out to the line it zoomed in from. Nothing folds — the subproof's
step is not a law's. -/
theorem gapInside_is_not_collapsed :
    ((session.steps gapInside).toOption.map fun d =>
      (d.shownLines.length, d.shownLines.map Shown.note))
      = some (4, ["!", "!", "", ""]) := by decide

/-! ### A gap carried out of the subproof that holds it

Zooming out justifies the outer step by the subproof, so a subproof that still
has a gap in it leaves the outer step unjustified too. `Doc.zoomOut` marks the
line it zoomed in from, and the outer level draws the warning sign on the line
just before the splice, which is where the document puts it. -/

/-- The line zoomed in from (line 0) carries a gap of its own, beside the one
line 1 carries inside the subproof. Before this, line 0 carried none and the
outer step showed neither a law name nor a warning sign. -/
theorem gapInside_gaps_the_line_before_the_splice :
    ((session.steps gapInside).toOption.map fun d => (d.gaps, d.note 0))
      = some ([0, 1], "!") := by decide

/-- And the proof does not claim anything: the outer level has a gap in it, so
`Doc.outcome` refuses even though the subproof has been closed. -/
theorem gapInside_proves_nothing : proved gapInside = none := by decide

/-- Re-opening takes the carried gap back with the line that carried it out: a
click on the subproof's bottom line leaves the gap the direct entry made inside
the level, and nothing on the line above it. -/
theorem reopen_takes_the_carried_gap_back :
    ((session.steps (gapInside ++ [.setFocus 2])).toOption.map fun d =>
      (d.depth, d.lines.size, d.gaps)) = some (1, 3, [1]) := by decide

/-- And zooming out again carries it out again, writing the very document the
first zoom out wrote: the splice and the warning sign on the line before it come
back as they were. Going back in and out of a subproof that holds a gap changes
nothing. -/
theorem reopen_then_zoom_out_is_the_same_document :
    (session.steps (gapInside ++ [.setFocus 2, .zoomOut])).toOption
      = (session.steps gapInside).toOption := by decide

/-- A justified subproof splices as it always did. `fold`'s subproof is a single
law application: no gap is carried out, line 0 keeps the law's name — lifted by
the fold — and the proof stands. -/
theorem fold_splices_without_a_gap :
    ((session.steps fold).toOption.map fun d => (d.gaps, d.note 0))
      = some ([], "") := by decide

/-- Neither does a *longer* justified subproof: `merge`'s inner level is two law
steps, and the outer line before the splice is left unannotated, its
justification being the lines inside. -/
theorem merge_splices_without_a_gap :
    ((session.steps merge).toOption.map fun d => (d.gaps, d.note 0))
      = some ([], "") := by decide

/-- Two levels down, the gap is carried out twice: the direct entry gaps line 2
inside the innermost level, the first zoom out gaps line 1, and the second gaps
line 0. A gap does not get lost by being deep. -/
def gapCarries : List Cmd :=
  [ .start .boolean .same
      (bin .and (var "x") (bin .or (var "y") (bin .and (var "z") (var "z")))),
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .direct .eq (var "z"),
    .zoomOut,
    .zoomOut ]

theorem gapCarries_carries_it_all_the_way_out :
    ((session.steps gapCarries).toOption.map fun d => (d.gaps, d.note 0))
      = some ([0, 1, 2], "!") := by decide

/-- The merge would have drawn those six lines as four, and it does not: a
collapse never hides a line a warning sign hangs on, and now there is one at
each level. -/
theorem gapCarries_is_not_collapsed :
    ((session.steps gapCarries).toOption.map fun d =>
      (d.shownLines.length, d.shownLines.map Shown.note))
      = some (6, ["!", "!", "!", "", "", ""]) := by decide

/-- A click that abandons a gappy subproof carries the gap out too, because
`Doc.closeToDepth` closes the levels by running `Doc.zoomOut`: `focus 0` in
place of the two zoom-outs writes the very same document. -/
theorem gapCarries_is_the_same_by_clicking :
    (session.steps (gapCarries.take 4 ++ [.setFocus 0])).toOption.map (fun d => d.lines.toList)
      = (session.steps gapCarries).toOption.map (fun d => d.lines.toList) := by decide

/-! ### A segment as a level: zooming in to a run of operands

A part is not only a place a law is applied to; it is a level you can work
inside. `Cmd.zoomIn` takes a `Part`, so a contiguous segment of an association is
a zoom target as much as a single main operand: the subproof's first line is the
run, left-associated as `Expr.segmentExpr` builds it, its type and direction are
the ones the segment *site* carries, its context is what the operands outside the
run supply, and zooming out splices the bottom line back through the same
`Part.replace` a site rewrite uses. -/

/-- The long way round to `x ∧ y ∧ z`: zoom in to the segment `y ∧ y` — the two
operands from the first — fold it there, and zoom back out. -/
def segmentZoom : List Cmd :=
  [ .start .boolean .same segmentLine,
    .zoomIn (.segment 1 2),
    .applyNamed "idempotent" (some (.eq, var "y")),
    .zoomOut ]

/-- The level the zoom opens has the segment for its first line, built
left-associated as `Expr.segmentExpr` builds it. -/
theorem segmentZoom_opens_the_segment :
    ((session.steps (segmentZoom.take 2)).toOption.map fun d =>
      d.lines.toList.map fun l => (l.depth, l.expr))
      = some [(0, segmentLine), (1, bin .and (var "y") (var "y"))] := by decide

/-- And the frame remembers which run it was, with the type, direction and
position the segment *site* carries — which is what lets the zoom out splice the
subproof back where it came from. -/
theorem segmentZoom_remembers_the_run :
    ((session.steps (segmentZoom.take 2)).toOption.bind fun d =>
      d.frame?.map fun f => (f.ty, f.dir, f.pos, f.part))
      = some (.boolean, .same, .positive, .segment 1 2) := by decide

/-- Zooming in to a segment of a conjunction gains the operands *outside* the
run as context, exactly as zooming in to one operand gains the other three:
here `x` and `z`. -/
theorem segmentZoom_gains_the_others :
    ((session.steps (segmentZoom.take 2)).toOption.map fun d =>
      d.contextLaws.map Law.stmt) = some [var "x", var "z"] := by decide

/-- A segment of `×` is neutral — the document's position table leaves `×` out,
since a factor is monotonic only for a nonnegative other — so zooming in to one
flattens the direction to `=`, whatever the level's was. That is the rule
`times_segments_are_neutral` reads off the site, now read off the level. -/
theorem times_segment_zoom_is_neutral :
    ((session.steps
        [ .start .number .down (bin .mul (bin .mul (var "n") (var "m")) (var "k")),
          .zoomIn (.segment 0 2) ]).toOption.bind fun d =>
      d.frame?.map fun f => (f.ty, f.dir, f.pos)) = some (.number, .same, .neutral) := by decide

/-- The whole line is not a level of its own, so `Part.whole` is refused: it is
the level one is already on. -/
theorem the_whole_line_is_not_a_zoom_target :
    (session.steps [.start .boolean .same segmentLine, .zoomIn .whole]).isOk = false := by decide

/-- It proves what the one-step segment rewrite proves. -/
theorem segmentZoom_proves :
    proved segmentZoom
      = some (bin .eq segmentLine (bin .and (bin .and (var "x") (var "y")) (var "z"))) := by
  decide

theorem segmentZoom_complete :
    ((session.steps segmentZoom).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide

/-- And the line the zoom out splices is, connective and formula, the line
`segmentFold` writes in one step: the long way round and the short way round
write the same thing, because both put the part back through `Part.replace`. -/
theorem segmentZoom_splices_what_the_site_writes :
    ((session.steps segmentZoom).toOption.bind fun d =>
        d.lines.toList.getLast?.map fun l => (l.conn, l.expr))
      = ((session.steps segmentFold).toOption.bind fun d =>
        d.lines.toList.getLast?.map fun l => (l.conn, l.expr)) := by decide

/-- The document keeps all four lines, and the display draws two: the subproof is
a single law application, so it folds into the line it was zoomed in from with
`idempotent` moved up — line for line what `segmentFold` draws. The collapses
needed nothing added for segment zooms. -/
theorem segmentZoom_collapses :
    ((session.steps segmentZoom).toOption.map fun d => (d.lines.size, d.shownLines))
      = some (4, [{ index := 0, depth := 0, note := "idempotent" },
                  { index := 3, depth := 0, note := "" }]) := by decide

theorem segmentZoom_shows_what_segmentFold_shows :
    shown segmentZoom = shown segmentFold := by decide

/-- The scripts `lake exe netty --demo=…` runs, paired with the command lists
checked above; `netty --selftest` compares them. -/
def demos : List (String × String × List Cmd) :=
  [("portation", Demo.portation, portation),
   ("discharge", Demo.discharge, discharge),
   ("gap", Demo.gap, gap),
   ("minimize", Demo.minimize, minimize),
   ("segment", Demo.segment, segmentFold),
   ("segfold", Demo.segfold, segmentZoom),
   ("fold", Demo.fold, fold),
   ("merge", Demo.merge, merge)]

end Replay
end Netty
