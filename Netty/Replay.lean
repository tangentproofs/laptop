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

Three more replays are checked the same way: one that zooms in to a
subexpression and uses the context that zooming in supplies, one that leaves a
gap by direct entry and then closes it, and one that applies a law to a *part*
of a line instead of to the whole of it.

`Netty.Demo` holds these same four proofs as *scripts*, which is what
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
    .zoomIn 1,
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

/-! ### Matching modulo associativity

The document says that clicking on any operand of `a + b + c` zooms in to it,
with no need of associative laws. Applying a law reads a line the same way:
`specialization`, `a ∧ b ⇒ a`, matches `x ∧ y ∧ z` — which is `(x ∧ y) ∧ z` —
with `a := x` and `b := y ∧ z` as readily as with `a := x ∧ y` and `b := z`. -/

/-- `x ∧ y ∧ z`, read as `(x ∧ y) ∧ z`. -/
def conjunction : Expr := bin .and (bin .and (var "x") (var "y")) (var "z")

/-- What the laws named `name` suggest for a proof of one line. -/
def suggestedBy (name : String) (dir : Dir) (e : Expr) : List (BinOp × Expr) :=
  match (session.steps [.start .boolean dir e]).toOption with
  | some d => (d.suggestions.filter (·.law == name)).map fun s => (s.op, s.result)
  | none => []

/-- Specialization offers both readings, the one whose first segment is
shorter first. Only the second of them was offered before matching went modulo
associativity. -/
theorem specialization_reads_both_ways :
    suggestedBy "specialization" .down conjunction
      = [(.imp, var "x"), (.imp, bin .and (var "x") (var "y"))] := by decide

/-- So does symmetry, whose right side puts the segments back in the other
order: `y ∧ z ∧ x` from the first reading, `z ∧ (x ∧ y)` from the second. -/
theorem symmetry_reads_both_ways :
    suggestedBy "symmetry" .down conjunction
      = [(.eq, bin .and (bin .and (var "y") (var "z")) (var "x")),
         (.eq, bin .and (var "z") (bin .and (var "x") (var "y")))] := by decide

/-- A proof that the reading which is new here really can be taken: one step
from `x ∧ y ∧ z` to `x`, where before it took an associative law first. -/
def assoc : List Cmd :=
  [ .start .boolean .down conjunction,
    .applyNamed "specialization" (some (.imp, var "x")) ]

theorem assoc_proves : proved assoc = some (bin .imp conjunction (var "x")) := by decide

theorem assoc_complete :
    ((session.steps assoc).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide

/-- A pattern operand that is not a law variable takes one operand and no
more: `a ∧ (b ∨ c)` cannot read `x ∧ y ∧ z`, because no segment of it is a
disjunction. -/
theorem no_match_without_a_law_variable :
    Expr.matchAll (bin .and (mvar "a") (bin .or (mvar "b") (mvar "c"))) conjunction [] = [] := by
  decide

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
    .zoomIn 1,
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

/-- The scripts `lake exe netty --demo=…` runs, paired with the command lists
checked above; `netty --selftest` compares them. -/
def demos : List (String × String × List Cmd) :=
  [("portation", Demo.portation, portation),
   ("discharge", Demo.discharge, discharge),
   ("gap", Demo.gap, gap),
   ("minimize", Demo.minimize, minimize)]

end Replay
end Netty
