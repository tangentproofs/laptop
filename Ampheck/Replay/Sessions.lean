import Ampheck.Replay
import Ampheck.Laws

/-!
# The replays' sessions over the shipped law lists

The documents the replays of `Ampheck.Replay.Zoom` … `Ampheck.Replay.Matching`
start from: the full boolean list (`session`), and the short lists cut from the
shipped ones that keep a replay about one law cheap. The commands themselves, and
the sessions built from laws written out by hand, are in `Ampheck.Replay`.
-/

namespace Ampheck
namespace Replay

open Expr (var mvar num bin neg)

/-! ### `a ⇒ (b ⇒ a)`, by portation and specialization -/

/-- A session with the shipped boolean laws and nothing else. -/
def session : Doc := { laws := Laws.boolean }

/-- Running a list of commands and asking what the proof proves. -/
def proved (cs : List Cmd) : Option Expr := provedIn session cs

/-- The lines of a finished replay, for the record. -/
def lines (cs : List Cmd) : Option (List (Option BinOp × Expr)) :=
  (session.steps cs).toOption.map fun d => d.lines.toList.map fun l => (l.conn, l.expr)

/-! ### Conditional laws at the number level -/

/-- The boolean laws together with the small number list. -/
def conditionalSession : Doc := { laws := Laws.boolean ++ Laws.number }

/-! ### The conditional reading at the boolean level -/

/-- The three shipped laws this proof needs, and nothing else. What is witnessed
below is the *context's* own conditional reading, and a short list makes that
plain — and keeps a nine-command replay inside the kernel's budget. -/
def ponensSession : Doc :=
  { laws := Laws.boolean.filter fun l => l.name == "reflexive" || l.name == "base" }

/-! ### Supplying a law variable by hand -/

/-- The three shipped laws this proof needs, and nothing else. -/
def dialogSession : Doc :=
  { laws := Laws.boolean.filter fun l =>
      l.name == "monotonic" || l.name == "reflexive" || l.name == "base" }

/-! ### `if … then … else … fi` -/

/-- The five Case laws, and nothing else: what is witnessed below is the form and
the laws about it, and a short list says so and keeps the replays cheap. -/
def condSession : Doc :=
  { laws := Laws.boolean.filter fun l =>
      l.name == "case base" || l.name == "case idempotent" || l.name == "case analysis"
        || l.name == "case reversal" }

/-! ### `∀ids: d· b` and `∃ids: d· b` -/

/-- The shipped quantifier laws, and the one boolean law the proof inside a body
uses: seven lines, so that these replays compute a suggestion list of a few rows
and not of a few hundred (item 22). -/
def quantSession : Doc :=
  { laws := Laws.quantifier ++ Laws.boolean.filter fun l => l.name == "double negation" }

/-! ### Matching modulo associativity, symmetry and the identity -/

/-- What the laws named `name` suggest for a proof of one line. -/
def suggestedBy (name : String) (dir : Dir) (e : Expr) : List (BinOp × Expr) :=
  match (session.steps [.start .boolean dir e]).toOption with
  | some d => (d.suggestions.filter (·.law == name)).map fun s => (s.op, s.result)
  | none => []

/-! ### A law applied to a contiguous segment of an association -/

/-- The two shipped laws the segment scripts below name, and nothing else.

Every claim they make is about *those* laws — what `idempotent` folds, where the
fold is credited, what the two ways round write and draw — so a shorter list says
the same thing and says it plainly. It also says it quickly: a `decide` that
replays a proof computes the whole suggestion list at every step, and under the
full list that is several hundred rows a step. The surveys that really are about
the whole list (`suggestions_are_ranked`,
`shipped_boolean_conditional_readings_are_all_greyed`) keep `session`. -/
def segmentSession : Doc :=
  { laws := Laws.boolean.filter fun l =>
      l.name == "idempotent" || l.name == "double negation" }

/-! ### The display collapses -/

/-- What a display draws under the whole shipped law list. -/
def shown (cs : List Cmd) : Option (List (Nat × Option BinOp × Expr × String)) :=
  shownIn session cs

end Replay
end Ampheck
