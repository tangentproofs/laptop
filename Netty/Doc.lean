import Netty.Law

/-!
# The proof document

A Netty calculation is a sequence of lines with a *direction* in the left
margin, and it can be zoomed in to a *part* of the line before the focus, which
starts a subproof of its own with its own direction, its own type and its own
context. This module is that document, the pure transitions on it, and the
suggestions the tool offers for the next line. It is the whole kernel: the
command line in `NettyMain` is argument handling and printing.

## Directions and what a proof proves

For each type there are three directions, spelled `⇒ = ⇐` for booleans and
`≤ = ≥` for numbers. The direction limits the connectives that may stand in
the margin; it does not say what the proof proves. That is read off the
connectives that actually occur (the document's rules):

* all `=` — the proof proves `topline = bottomline`;
* at least one `≤` and no `<` — `topline ≤ bottomline`; and so on.

and in the special case that a proof proves `a = ⊤` or `a ⇐ ⊤`, it proves `a`;
if it proves `a = ⊥` or `a ⇒ ⊥`, it proves `¬a`.

## The zoom stack

`Doc.lines` is the whole document in reading order, each line tagged with its
nesting `depth`; `Doc.stack` is the levels that are still open, innermost
first. Zooming in appends the chosen part as the first line of a new level
and pushes a frame carrying that level's type, direction, position and context.
Zooming out pops the frame and appends, to the level below, the line we zoomed in
from with the chosen part replaced by the bottom line of the subproof — one
`Part`, put back by `Part.replace`, whichever kind of part it was.

Because every line of a still-open level lies after every line of the levels
below it, appending or inserting at the current level never disturbs an index
recorded in a frame.

## Suggestions, and laws applied to a part

A suggestion comes from matching a law's variant against the line before the
focus — either against the whole of it, or against one of its *parts*, which is
the document's applying a law "to a part, as a result of minimization". A part
rewrite writes the line back with that part replaced, and takes for its margin
connective the one that zooming in to the part, applying the law and zooming out
would have written: the part's position turns the direction on the way in
(`Dir.zoom`) and turns it back on the way out, so a step that is the part's
direction inside is the level's direction outside, and a neutral position admits
only `=`. That is why no new soundness argument is needed here. See `Doc.sites`,
`Doc.rewriteAt` and `Doc.suggestions`.

The parts are the *main operands* of the line — what a single `zoomIn` reaches
and a display draws as separate pieces — and, when the main operator is
associative, every contiguous *segment* of the association: a run of two or more
consecutive operands, shorter than the whole line. The document reads `x ∧ y ∧ z`
as having the part `y ∧ z` just as it has the part `y`, so a law that matches two
of three conjuncts folds them where they stand and leaves the third alone
(`Expr.segments`, `Expr.replaceSegment`, `Doc.Part`). An associative operator
puts all of its operands in one position, so a run of them is in that same
position, and the direction and type of a segment site are word for word those of
a single operand of the same association — the soundness argument is the one
above, unchanged. Segments come after the single operands, and a rewrite that
merely repeats the line is dropped as before, so a longer suggestion list is the
whole of the difference a user sees.

A part is also a level you can work *inside*: `Cmd.zoomIn` takes a `Part`, so
zooming in to the segment `y ∧ z` of `x ∧ y ∧ z` opens a subproof whose first
line is that segment, left-associated as `Expr.segmentExpr` builds it, with the
type and direction the segment site carries and the context the operands outside
the run supply. Zooming out splices the bottom of that subproof back through the
same `Part.replace` a site rewrite uses, so the long way round — zoom in, apply,
zoom out — writes the very line the one-step site rewrite writes, and `Part` is
the single place that says what a part *is*. `Part.whole` is refused: it is the
level one is already on. Deeper positions are still reached by zooming in again.

## Focus

There is always exactly one focus, just after the line `Doc.focus`. Moving it
back is how a gap left by direct entry is filled: taking a suggestion that
reproduces the line already below the focus replaces the warning sign with the
law's name.

The document lets a click land *anywhere*, and so does `Cmd.setFocus`: the line
may be at an outer level, and the zoom stack is then recomputed so that the
line's level is the innermost open one again. The recompute is a run of
zoom-outs (`Doc.closeToDepth`) — the state the user could have reached by
closing those levels themselves — so each abandoned subproof still puts its
bottom line back into the line it was zoomed in from, and the direction, type
and context that come with the focus are the ones that level always had. The
one place a click cannot go is into a subproof that has already been zoomed out
of: that level is closed, and re-opening one is not something the kernel does.
`Doc.canFocus` is the predicate, and it is what the API reports as
`focusable`.

## Gaps

`Line.gap` marks a logical gap between that line and the next: a step that no
law licenses. Direct entry creates one. `Doc.outcome` refuses to say what a
proof with a gap proves.

## The display collapses

A proof that was written by zooming keeps more lines than it needs to be read
by. The document collapses two of those patterns, and so does this kernel —
not by throwing lines away, but by a pass over the document that says which
lines a display draws, at what depth, and with what law name at the end of
them (`Doc.shownLines`). The document itself is untouched, so a saved proof is
the whole proof, the script language still calls a line by its index in
`Doc.lines`, and nothing about applying a law changes.

The two collapses are:

* **a subproof that is a single law application folds into its parent line**,
  with the law's name moved up onto that line — the two lines the zoom in and
  the one step wrote are not drawn at all, and the line the zoom out wrote
  follows the parent directly. What is left is exactly what applying the law to
  a *part* of the parent line would have drawn (`Doc.sites`), so the long way
  round and the short way round are drawn alike; and
* **two zoom-ins matched by two zoom-outs merge into one zoom step**: a level
  whose only lines are the one a zoom in wrote and the one a zoom out wrote has
  done nothing but hold a subproof, so that subproof is drawn one level out and
  the two scaffolding lines are not drawn.

Both are honest because both only remove lines that a rewriting of the step
would not have written in the first place, and both leave every line that
carries a law name or a warning sign. Neither ever hides the focus, a line
with a gap, or a line of a level that is still open: a collapse fires only
where the matching zoom-out has already been written, and `Doc.canFocus`
refuses a closed level anyway. The pass is a fixpoint, so a threefold zoom
merges twice and then folds.
-/

namespace Netty

/-- One of the three directions of a type: `⇒ = ⇐` for booleans, `≤ = ≥` for
numbers. -/
inductive Dir
  /-- `⇒` for booleans, `≤` for numbers. -/ | down
  /-- `=`. -/                               | same
  /-- `⇐` for booleans, `≥` for numbers. -/ | up
  deriving Repr, DecidableEq, Inhabited

/-- A direction together with whether it is strict, which is what a proof's
connectives add up to. -/
structure Rel where
  /-- Which way the proof goes. -/ dir : Dir
  /-- Whether some connective was `<` or `>`. -/ strict : Bool
  deriving Repr, DecidableEq, Inhabited

namespace BinOp

/-- The relation a margin connective expresses. -/
def rel? : BinOp → Option Rel
  | eq => some ⟨.same, false⟩
  | imp | le => some ⟨.down, false⟩
  | lt => some ⟨.down, true⟩
  | rimp | ge => some ⟨.up, false⟩
  | gt => some ⟨.up, true⟩
  | _ => none

/-- The type a margin connective belongs to; `=` belongs to all of them. -/
def connTy : BinOp → Option Ty
  | imp | rimp => some .boolean
  | lt | gt | le | ge => some .number
  | _ => none

end BinOp

namespace Rel

/-- How the relation is written at a given type. -/
def op (ty : Ty) (r : Rel) : BinOp :=
  match r.dir, ty with
  | .same, _ => .eq
  | .down, .boolean => .imp
  | .up, .boolean => .rimp
  | .down, .number => if r.strict then .lt else .le
  | .up, .number => if r.strict then .gt else .ge

/-- What a chain of connectives adds up to: `none` when it mixes directions,
which the direction discipline is there to prevent. -/
def combine (rs : List Rel) : Option Rel :=
  rs.foldl
    (fun acc r => acc.bind fun a =>
      if r.dir == .same then some a
      else if a.dir == .same then some ⟨r.dir, r.strict⟩
      else if a.dir == r.dir then some ⟨a.dir, a.strict || r.strict⟩
      else none)
    (some ⟨.same, false⟩)

end Rel

namespace Dir

/-- How the direction is written at a given type. -/
def symbol (ty : Ty) : Dir → String
  | down => match ty with | .boolean => "⇒" | .number => "≤"
  | same => "="
  | up => match ty with | .boolean => "⇐" | .number => "≥"

/-- Whether a connective may stand in the margin under this direction, at this
type. `=` is allowed under every direction; a direction allows itself and its
strict form; nothing else. -/
def allows (d : Dir) (ty : Ty) (o : BinOp) : Bool :=
  match o.rel? with
  | some r =>
      (r.dir == .same || r.dir == d) && (o.connTy == none || o.connTy == some ty)
  | none => false

/-- The direction of the subproof created by zooming in to an operand in the
given position (the document's five rules). -/
def zoom (d : Dir) (p : Pos) : Dir :=
  match d, p with
  | same, _ => same
  | _, .neutral => same
  | _, .positive => d
  | down, .negative => up
  | up, .negative => down

end Dir

namespace Expr

/-- Push a negation one step inwards, as the document's context table does.
`negate e` is `¬e` rewritten so that the outermost connective is not a
negation, where that is possible. -/
def negate : Expr → Expr
  | neg a => a
  | bin .and a b => bin .or (neg a) (neg b)
  | bin .or a b => bin .and (neg a) (neg b)
  | bin .eq a b => bin .ne a b
  | bin .ne a b => bin .eq a b
  | bin .imp a b => bin .and a (neg b)
  | bin .rimp a b => bin .and (neg a) b
  | e => neg e

/-- Split a conjunction into its conjuncts: a context that is a conjunction is
gained as one law per conjunct. -/
def splitAnd : Expr → List Expr
  | bin .and a b => splitAnd a ++ splitAnd b
  | e => [e]

/-- The facts a zoom in to the run of `len` main operands of `e` starting at
`start` adds to the context (the document's table). Zooming in to operands of
`∧` gains the others; of `∨`, their negations; of `a ⇒ b` on `a`, `¬b`, and on
`b`, `a`; and dually for `⇐`. Nothing else contributes a context.

A run of more than one operand is only ever a run of an *association*, and the
two operators whose context depends on which operand was chosen — `⇒` and `⇐` —
are not associations, so for them `start` is the operand index and `len` is one,
exactly as before. -/
def contextOfRange (e : Expr) (start len : Nat) : List Expr :=
  match e with
  | bin op _ _ =>
      let ops := operands e
      let others := (List.range ops.length).filterMap fun j =>
        if start ≤ j && j < start + len then none else ops[j]?
      match op with
      | .and => others.flatMap splitAnd
      | .or => others.flatMap (fun o => splitAnd (negate o))
      | .imp =>
          match ops[0]?, ops[1]? with
          | some l, some r => if start == 0 then splitAnd (negate r) else splitAnd l
          | _, _ => []
      | .rimp =>
          match ops[0]?, ops[1]? with
          | some l, some r => if start == 0 then splitAnd r else splitAnd (negate l)
          | _, _ => []
      | _ => []
  | _ => []

/-- The facts a zoom in to the `i`-th main operand of `e` adds to the context:
the run of one operand at `i`. -/
def contextOf (e : Expr) (i : Nat) : List Expr := contextOfRange e i 1

end Expr

/-- Which part of a line a site is. -/
inductive Part
  /-- The whole line. -/
    | whole
  /-- The `i`-th main operand. -/
    | operand (i : Nat)
  /-- A contiguous run of `len` main operands of an association, starting at the
  `start`-th: `len` is at least two and less than the whole association, so a
  segment is neither a single operand nor the line (`Expr.segments`). -/
    | segment (start len : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace Part

/-- The subexpression of `line` this part is; `none` when the part is not there.
The whole line is itself. -/
def exprOf : Part → Expr → Option Expr
  | whole, line => some line
  | operand i, line => line.operands[i]?
  | segment start len, line => line.segmentExpr start len

/-- The position this part occupies in `line`. The whole line is in no position
at all, and counts as `positive`, which is what leaves a direction alone. -/
def posOf : Part → Expr → Pos
  | whole, _ => .positive
  | operand i, line => line.operandPos i
  | segment _ _, line => line.segmentPos

/-- The type of this part of `line`, falling back to `parent` — the type of the
level the line is on — when nothing in the part settles it. -/
def tyOf : Part → Expr → Ty → Ty
  | whole, _, parent => parent
  | operand i, line, parent => line.operandTy i parent
  | segment _ _, line, parent => line.segmentTy parent

/-- The facts zooming in to this part of `line` adds to the context. The whole
line adds none: it is the level one is already on. -/
def contextOf : Part → Expr → List Expr
  | whole, _ => []
  | operand i, line => Expr.contextOf line i
  | segment start len, line => Expr.contextOfRange line start len

/-- Put `r` where this part of `line` stood. `none` for the whole line, which is
not put back into anything, and `none` when the part is not there to replace. -/
def replace : Part → Expr → Expr → Option Expr
  | whole, _, _ => none
  | operand i, line, r => line.replaceOperand i r
  | segment start len, line, r => line.replaceSegment start len r

/-- How a script names this part: an operand by its number, a segment by
`start:length`. This is the argument `zoom` takes, so a window that offers a
part to a click offers this string and cannot mean anything else by it. -/
def render : Part → String
  | whole => "the whole line"
  | operand i => toString i
  | segment start len => s!"{start}:{len}"

/-- Which run of main operands this part is: where it starts, and how many it
takes. The whole line is not a run of operands at all, and counts as `(0, 0)`. -/
def span : Part → Nat × Nat
  | whole => (0, 0)
  | operand i => (i, 1)
  | segment start len => (start, len)

/-- This part of `line`, rendered as it stands in `line.render`: one main
operand carries exactly the parentheses `Expr.operandTexts` gives it, and a run
of them is those texts with the main operator between, so a part reads in a
window as it reads in the line. -/
def textIn : Part → Expr → String
  | whole, line => line.render
  | operand i, line => (line.operandTexts)[i]?.getD ""
  | segment start len, line =>
      String.intercalate s!" {line.mainOp} " (((line.operandTexts).drop start).take len)

/-- Whether this part is a level of its own — something `Cmd.zoomIn` can open a
subproof on. The whole line is not: it is the level one is already on. -/
def zoomable : Part → Bool
  | whole => false
  | _ => true

end Part

/-- A line of the proof. `why` names what produced it: a law's name, or one of
`direct entry`, `zoom in`, `zoom out`; the first line of the whole proof has
none. `gap` marks a logical gap between this line and the next. -/
structure Line where
  /-- How deeply the line is nested in subproofs; the outermost level is `0`. -/
  depth : Nat
  /-- The connective in the left margin; `none` on the first line of a level. -/
  conn : Option BinOp := none
  /-- The formula. -/
  expr : Expr
  /-- What produced the line. -/
  why : String := ""
  /-- Whether the step from this line to the next is unjustified. -/
  gap : Bool := false
  /-- On the first line of a level, that level's type — so that a closed
  subproof can still be printed after its frame has been popped. -/
  ty : Option Ty := none
  /-- On the first line of a level, that level's direction. -/
  dir : Option Dir := none
  deriving Repr, DecidableEq, Inhabited

/-- A level of the zoom stack that is still open. -/
structure Frame where
  /-- The type of this level's lines. -/
  ty : Ty
  /-- This level's direction. -/
  dir : Dir
  /-- The index of this level's first line. -/
  start : Nat
  /-- The line we zoomed in from; `none` for the outermost level. -/
  zoomLine : Option Nat := none
  /-- Which part of that line we zoomed in to, and so where the bottom of this
  level goes back. The outermost level was not zoomed in to at all, and its part
  is `whole`: the line itself. -/
  part : Part := .whole
  /-- Its position, which decides this level's direction and the connective
  that zooming out will use. -/
  pos : Pos := .positive
  /-- The laws this level's zoom in added to the context. -/
  ctx : List Law := []
  deriving Repr, DecidableEq, Inhabited

/-- A proof session: the law lists in force, the lines in reading order, the
levels still open (innermost first) and the focus. -/
structure Doc where
  /-- The laws loaded from law files. -/
  laws : List Law := []
  /-- Every line written so far, in reading order. -/
  lines : Array Line := #[]
  /-- The open levels, innermost first; empty until the proof is started. -/
  stack : List Frame := []
  /-- The focus sits just after this line. -/
  focus : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- What the tool offers as a possible next line. `holes` are the law variables
that matching left unconstrained — the document's "small dialog box" — which
the kernel will not apply until they are supplied. -/
structure Suggestion where
  /-- The name of the law it comes from. -/
  law : String
  /-- The connective it would put in the margin. -/
  op : BinOp
  /-- The line it would write. -/
  result : Expr
  /-- Law variables the match left unconstrained. -/
  holes : List String
  deriving Repr, DecidableEq, Inhabited

/-- A place in the line before the focus where a law may be applied: the whole
line, one of its main operands, or a contiguous segment of its association.

Applying a law to anything but the whole line is what the document calls
applying it "to a part, as a result of minimization". The step it makes is the
one a zoom in, a single application and a zoom out would make, so the numbers a
site carries are the ones the zoom stack would compute: the part's type and
direction are what zooming in to it gives (`Expr.operandTy`, `Expr.segmentTy`,
`Dir.zoom`), and the connective the step writes in the outer margin is what
zooming out of it would write. That is why no new soundness argument is needed
here — only the old one, spelled without the two lines that zooming would have
added to the proof.

The parts are one level deep (`Doc.parts`): the main operands, which a display
draws as separate pieces (`Expr.operandTexts`), and the runs of two or more of
them that an *associative* main operator makes available, since the document
reads `x ∧ y ∧ z` as having the part `y ∧ z` just as it has the part `y`. An
associative operator puts all of its operands in one position, so a run of them is
in that same position and the direction story is word for word the one for a
single operand. Every one of them is also a `Cmd.zoomIn` target, and a site reads
its expression, type, direction and position off the same `Part` the zoom does.
Deeper positions are still reached by zooming in. -/
structure Site where
  /-- The subexpression a law is matched against. -/
  expr : Expr
  /-- Its type. -/
  ty : Ty
  /-- The direction that holds there. -/
  dir : Dir
  /-- Its position in the line; `positive` for the whole line, which is not in
  any position at all. -/
  pos : Pos
  /-- Which part of the line it is. -/
  part : Part
  deriving Repr, DecidableEq, Inhabited

/-- A line as a display draws it, after the collapses of `Doc.shownLines`.

It is not a new kind of line: it names a line of `Doc.lines` by the index the
script language knows it by, and adds the two things a collapse changes — the
depth the line is drawn at, which merging two zooms lowers, and the name
written at the end of it, which folding a one-step subproof moves up. -/
structure Shown where
  /-- Its index in `Doc.lines`. -/
  index : Nat
  /-- The depth it is drawn at, which may be less than the line's own. -/
  depth : Nat
  /-- What is written at the end of it: the law that justifies the step to the
  next line drawn at this depth, or `!` where there is a gap. -/
  note : String
  deriving Repr, DecidableEq, Inhabited

/-- A command: every change to a document is one of these, and every one of
them is a pure function on the document. -/
inductive Cmd
  /-- Enter the type, direction and first line. -/
    | start (ty : Ty) (dir : Dir) (e : Expr)
  /-- Take the `n`-th suggestion. -/
    | apply (n : Nat)
  /-- Take the applicable suggestion from the named law; when several apply,
  `expect` says which by giving the line it would write. -/
    | applyNamed (name : String) (expect : Option (BinOp × Expr))
  /-- Type the next line in directly, leaving a gap. -/
    | direct (op : BinOp) (e : Expr)
  /-- Zoom in to a part of the line before the focus: a main operand, or a
  contiguous segment of its association. `Part.whole` is refused — it is the
  level one is already on. -/
    | zoomIn (part : Part)
  /-- Zoom out of the innermost level. -/
    | zoomOut
  /-- Move the focus to just after the given line, at whatever level it is on,
  closing the levels that sit below it. -/
    | setFocus (line : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- What a finished proof proves. -/
structure Outcome where
  /-- The first line. -/
  top : Expr
  /-- The relation the connectives add up to. -/
  rel : BinOp
  /-- The last line. -/
  bottom : Expr
  /-- `top rel bottom`, read specially when the bottom line is `⊤` or `⊥`. -/
  proved : Expr
  deriving Repr, DecidableEq, Inhabited

/-- Keep the first occurrence of each element. -/
private def dedup {α} [BEq α] (xs : List α) : List α :=
  (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

/-- `Option` to `Except`, so that the command transitions can explain
themselves. -/
def orElseError {α} (msg : String) : Option α → Except String α
  | some a => .ok a
  | none => .error msg

namespace Doc

/-- The innermost open level. -/
def frame? (d : Doc) : Option Frame := d.stack.head?

/-- The nesting depth of the innermost open level. -/
def depth (d : Doc) : Nat := d.stack.length - 1

/-- The line the focus sits after. -/
def focusLine? (d : Doc) : Option Line := d.lines[d.focus]?

/-- The index of the next line after `i` at `i`'s own level: the first later
line that is not nested more deeply, provided it has not left the level. -/
def nextSibling (d : Doc) (i : Nat) : Option Nat :=
  match d.lines[i]? with
  | none => none
  | some l =>
      match (List.range d.lines.size).find? fun j => j > i && (d.lines[j]!).depth ≤ l.depth with
      | some j => if (d.lines[j]!).depth == l.depth then some j else none
      | none => none

/-- The index of the first line after `i` at the innermost level, if any. -/
def nextAtLevel (d : Doc) (i : Nat) : Option Nat := d.nextSibling i

/-- The indices of this level's lines, in order. -/
def levelLines (d : Doc) : List Nat :=
  match d.frame? with
  | some f => (List.range d.lines.size).filter fun j => j ≥ f.start && (d.lines[j]!).depth == d.depth
  | none => []

/-- The lines of the outermost level, in order. -/
def rootLines (d : Doc) : List Line :=
  d.lines.toList.filter fun l => l.depth == 0

/-- The indices of the lines that a gap follows. -/
def gaps (d : Doc) : List Nat :=
  (List.range d.lines.size).filter fun j => (d.lines[j]!).gap

/-- Replace a line. -/
def withLine (d : Doc) (i : Nat) (l : Line) : Doc :=
  { d with lines := d.lines.set! i l }

/-- Insert a line just after the focus — that is, immediately before the next
line of this level, or at the end — and leave the focus on it. -/
def insertAfterFocus (d : Doc) (l : Line) : Doc :=
  let at_ := (d.nextAtLevel d.focus).getD d.lines.size
  { d with lines := (d.lines.toList.insertIdx at_ l).toArray, focus := at_ }

/-- The laws the zoom stack has added to the context, innermost first. -/
def contextLaws (d : Doc) : List Law := d.stack.flatMap (·.ctx)

/-- Every law in force: the context first, then the loaded law lists. -/
def allLaws (d : Doc) : List Law := d.contextLaws ++ d.laws

/-- The parts of the line `e` that a law may be applied to, or that a zoom can
open a level on: the whole line first, then each main operand in order, then each
contiguous segment of its association (`Expr.segments`, which is empty unless the
main operator is associative and has more than two operands). -/
def parts (e : Expr) : List Part :=
  .whole :: (List.range e.operands.length).map Part.operand
    ++ e.segments.map fun (start, len) => .segment start len

/-- The places a law may be applied to in the line `e` of a level whose frame is
`f`, one per part (`Doc.parts`). Each carries what zooming in to that part would
compute — its expression, its type, the direction that holds there and its
position — so that a site rewrite and a zoom in agree by construction. -/
def sites (f : Frame) (e : Expr) : List Site :=
  (parts e).filterMap fun part =>
    (part.exprOf e).map fun sub =>
      let p := part.posOf e
      { expr := sub, ty := part.tyOf e f.ty, dir := f.dir.zoom p, pos := p, part := part }

/-- The line that rewriting the part at `s` to `r` writes, and the connective
the step puts in the outer margin. `none` when the part cannot be put back.

For the whole line the connective is the variant's own. For a part — a main
operand or a segment of an association — it is what zooming out would write: `=`
when the rewrite was an equality or the part's position is neutral, and otherwise
the level's own direction, since the part's position has already turned the
direction once on the way in, so a step that is a direction inside is that same
direction outside. A segment goes back left-associated, exactly as `rebuildOp`
writes an association. -/
def rewriteAt (f : Frame) (line : Expr) (s : Site) (o : BinOp) (r : Expr) :
    Option (BinOp × Expr) :=
  match s.part with
  | .whole => some (o, r)
  | part => do
      let e ← part.replace line r
      let rel ← o.rel?
      let out : Rel :=
        if s.pos == .neutral || rel.dir == .same then ⟨.same, false⟩ else ⟨f.dir, false⟩
      return (out.op f.ty, e)

/-- The suggestions for the line after the focus: for every place of the line
before the focus (`Doc.sites`) and every variant of every law in force whose
connective that place's direction allows, the result of matching the place
against the variant's left side and putting the variant's right side back.

A place is the whole line, one of its main operands, or a contiguous segment of
its association, so a law applies "to a part, as a result of minimization" as
well as to the line entire: `a ∨ a = a` takes `x ∧ (y ∨ y)` to `x ∧ y` in one
step, where before it took a zoom in and a zoom out, and `a ∧ a = a` takes
`x ∧ y ∧ y ∧ z` to `x ∧ y ∧ z`, which no rewrite of the whole line or of a single
operand can reach. Whole-line suggestions come first, then the single operands,
then the segments.

Matching is modulo associativity, so one variant can match one place in several
ways — `a ∧ b ⇒ a` reads `x ∧ y ∧ z` as `x ∧ (y ∧ z)` and as `(x ∧ y) ∧ z` —
and each way is a suggestion of its own. Suggestions that leave law variables
unconstrained come last, and a suggestion that would merely repeat the line —
`a ⇐ a` from reflexivity, say — is dropped. -/
def suggestions (d : Doc) : List Suggestion :=
  match d.frame?, d.focusLine? with
  | some f, some line =>
      let raw := (sites f line.expr).flatMap fun site =>
        d.allLaws.flatMap fun l =>
          l.variants.flatMap fun v =>
            if !(site.dir.allows site.ty v.op) then []
            else (Expr.matchAll v.lhs site.expr []).filterMap fun σ =>
              match rewriteAt f line.expr site v.op (v.rhs.instantiate σ) with
              | some (o, r) =>
                  if r == line.expr then none
                  else some { law := v.law, op := o, result := r, holes := r.mvars }
              | none => none
      let ds := dedup raw
      ds.filter (·.holes.isEmpty) ++ ds.filter (fun s => !s.holes.isEmpty)
  | _, _ => []

/-- Write a suggestion into the focus. When the line already below the focus is
exactly what the suggestion offers, no line is added: the suggestion justifies
the step that was there, and the warning sign becomes the law's name. -/
def applySuggestion (d : Doc) (s : Suggestion) : Except String Doc := do
  if !s.holes.isEmpty then
    throw s!"the suggestion leaves {String.intercalate ", " s.holes} unconstrained"
  let fl ← orElseError "the proof has not been started" d.focusLine?
  match d.nextAtLevel d.focus with
  | some j =>
      let nl := d.lines[j]!
      if nl.conn == some s.op && nl.expr == s.result then
        return (d.withLine j { nl with why := s.law }).withLine d.focus { fl with gap := false }
      else
        let line : Line :=
          { depth := d.depth, conn := some s.op, expr := s.result, why := s.law, gap := fl.gap }
        return (d.withLine d.focus { fl with gap := false }).insertAfterFocus line
  | none =>
      let line : Line :=
        { depth := d.depth, conn := some s.op, expr := s.result, why := s.law, gap := false }
      return (d.withLine d.focus { fl with gap := false }).insertAfterFocus line

/-- Zoom out of the innermost level: append, to the level below, the line we
zoomed in from with the chosen part replaced by the bottom line of the subproof
(`Part.replace`, so a segment goes back left-associated as `Expr.rebuildOp`
writes an association), and pop the frame. The subproof's own lines stay in the
document, which is what the `ty` and `dir` a level's first line carries are for.

The connective the new line gets follows the document's three rules: `=` when
the part's position is neutral or the subproof proved an equality, and the
parent level's own direction otherwise. Zooming out of a level with a single
line is an undo, as the document says: the line goes away again. -/
def zoomOut (d : Doc) : Except String Doc :=
  match d.stack with
  | f :: parent :: rest => do
      if d.focus + 1 != d.lines.size then
        throw "zoom out only from the last line; move the focus there first"
      let zl ← orElseError "this level was not entered by zooming in" f.zoomLine
      let idxs := d.levelLines
      if idxs.length ≤ 1 then
        -- "Zooming out immediately after zooming in is the same as undo."
        return { d with lines := d.lines.pop, stack := parent :: rest, focus := zl }
      let rels := idxs.filterMap fun j => (d.lines[j]!).conn.bind BinOp.rel?
      let rel ← orElseError "the subproof mixes directions" (Rel.combine rels)
      let newRel : Rel :=
        if f.pos == .neutral || rel.dir == .same then ⟨.same, false⟩ else ⟨parent.dir, false⟩
      let bottom := (d.lines[idxs.getLast!]!).expr
      let zoomExpr := (d.lines[zl]!).expr
      let e ← orElseError "the subproof cannot be put back into its line"
        (f.part.replace zoomExpr bottom)
      let idx := d.lines.size
      return { d with
        lines := d.lines.push
          { depth := d.depth - 1, conn := some (newRel.op parent.ty), expr := e,
            why := "zoom out" }
        stack := parent :: rest
        focus := idx }
  | [_] => .error "the outermost proof cannot be zoomed out of"
  | [] => .error "the proof has not been started"

/-- Whether the focus may be moved to just after line `i`.

Any line of any *open* level will do — the document lets a click land anywhere,
and focusing a line below the innermost level closes the levels between it and
that line (`Doc.closeToDepth`). What cannot be focused is a line of a subproof
that has already been zoomed out of: its level is closed, and re-opening one is
not something the kernel does. Those are the lines deeper than the innermost
open level, and the lines that lie before the first line of the open level at
their own depth — the ones belonging to an earlier, closed subproof at that
depth. -/
def canFocus (d : Doc) (i : Nat) : Bool :=
  !d.stack.isEmpty &&
    (match d.lines[i]? with
     | none => false
     | some l =>
         -- The stack is innermost first, so the open level at depth `k` is the
         -- frame `d.depth - k` frames in.
         l.depth ≤ d.depth &&
           (match d.stack[d.depth - l.depth]? with
            | some f => i ≥ f.start
            | none => false))

/-- Close the open levels below depth `target`, exactly as a run of zoom-outs
would: each one puts its subproof's bottom line back into the line it was zoomed
in from. This is what lets the focus land on a line of an outer level — the
document's click that can go anywhere — without a document model that knows how
to be zoomed in to two places at once.

Zooming out reads a level's *bottom* line and refuses to run unless the focus is
on it. The focus we have been asked for is at an outer level, so it is leaving
this one in any case, and moving it to the bottom line first loses nothing.

The fuel is the number of open levels, one unit spent per level closed. -/
def closeToDepth (d : Doc) (target : Nat) : Except String Doc :=
  go d.stack.length d
where
  go : Nat → Doc → Except String Doc
    | 0, d => .ok d
    | fuel + 1, d =>
        if d.depth ≤ target then .ok d
        else do
          let d := { d with focus := d.lines.size - 1 }
          go fuel (← d.zoomOut)

/-- Run one command. Every change a user can make to a proof is one of these,
and this is the only way a `Doc` changes. -/
def step (d : Doc) : Cmd → Except String Doc
  | .start ty dir e =>
      if d.stack.isEmpty then
        .ok { d with
          lines := #[{ depth := 0, expr := e, ty := some ty, dir := some dir }]
          stack := [{ ty := ty, dir := dir, start := 0 }]
          focus := 0 }
      else .error "the proof has already been started"
  | .apply n => do
      let s ← orElseError s!"there is no suggestion {n}" d.suggestions[n]?
      d.applySuggestion s
  | .applyNamed name expect => do
      let ok := d.suggestions.filter fun s =>
        s.law == name && s.holes.isEmpty &&
          (match expect with
           | some (o, e) => s.op == o && s.result == e
           | none => true)
      match ok with
      | [s] => d.applySuggestion s
      | [] => throw s!"no applicable suggestion from a law named ‘{name}’"
      | _ => throw s!"‘{name}’ offers {ok.length} applicable suggestions here; \
        name the line it should write, or choose one by number"
  | .direct op e => do
      let f ← orElseError "the proof has not been started" d.frame?
      if !(f.dir.allows f.ty op) then
        throw s!"the direction {f.dir.symbol f.ty} does not allow ‘{op.symbol}’"
      let fl ← orElseError "the proof has not been started" d.focusLine?
      let hasNext := (d.nextAtLevel d.focus).isSome
      let line : Line :=
        { depth := d.depth, conn := some op, expr := e, why := "direct entry",
          gap := hasNext && fl.gap }
      return (d.withLine d.focus { fl with gap := true }).insertAfterFocus line
  | .zoomIn part => do
      let f ← orElseError "the proof has not been started" d.frame?
      if d.focus + 1 != d.lines.size then
        throw "zoom in only from the last line; move the focus there first"
      if !part.zoomable then
        throw "the whole line is the level you are on; zoom in to a part of it"
      let fl ← orElseError "the proof has not been started" d.focusLine?
      let sub ← orElseError s!"line {d.focus} has no part {part.render}"
        (part.exprOf fl.expr)
      let pos := part.posOf fl.expr
      let idx := d.lines.size
      let subTy := part.tyOf fl.expr f.ty
      let subDir := f.dir.zoom pos
      return { d with
        lines := d.lines.push
          { depth := d.depth + 1, expr := sub, why := "zoom in",
            ty := some subTy, dir := some subDir }
        stack := { ty := subTy, dir := subDir, start := idx,
                   zoomLine := some d.focus, part := part, pos := pos,
                   ctx := (part.contextOf fl.expr).map Law.context } :: d.stack
        focus := idx }
  | .zoomOut => d.zoomOut
  | .setFocus n => do
      if d.stack.isEmpty then throw "the proof has not been started"
      let l ← orElseError s!"there is no line {n}" d.lines[n]?
      if !d.canFocus n then
        throw s!"line {n} belongs to a subproof that has been zoomed out of; \
          the focus cannot move back into one"
      -- Closing the levels below the line leaves untouched the frame of the
      -- level the line is in — `Doc.zoomOut` rebuilds no frame but the one it
      -- pops — so `canFocus`, asked before, still holds after.
      let d ← d.closeToDepth l.depth
      return { d with focus := n }

/-- Run a whole script. -/
def steps (d : Doc) (cs : List Cmd) : Except String Doc :=
  cs.foldlM (fun acc c => acc.step c) d

/-- What the proof proves, or why it does not prove anything yet. -/
def outcome (d : Doc) : Except String Outcome := do
  let f ← orElseError "the proof has not been started" d.stack.getLast?
  if d.stack.length != 1 then
    throw "the proof is still zoomed in; zoom out first"
  match d.gaps with
  | j :: _ => throw s!"there is a gap after line {j}"
  | [] => pure ()
  let ls := d.rootLines
  let rel ← orElseError "the proof mixes directions"
    (Rel.combine (ls.filterMap fun l => l.conn.bind BinOp.rel?))
  let top ← orElseError "the proof has no lines" ls.head?
  let bottom ← orElseError "the proof has no lines" ls.getLast?
  let op := rel.op f.ty
  let proved :=
    if bottom.expr == .top && (op == .eq || op == .rimp) then top.expr
    else if bottom.expr == .bot && (op == .eq || op == .imp) then .neg top.expr
    else .bin op top.expr bottom.expr
  return { top := top.expr, rel := op, bottom := bottom.expr, proved := proved }

/-! ### The display collapses

What a display draws is not quite `Doc.lines`. Two patterns of lines that
zooming writes carry nothing a reader needs, and the document collapses them;
`Doc.shownLines` is that collapse, as a pass over the document rather than a
change to it. See the module header for what the two are and why they are
honest. -/

/-- The name to write at the end of line `i`: the law that justifies the step
to the next line at the same level, or a warning sign where there is a gap.
`zoom in` and `zoom out` are movements of the display, not laws, and are not
written. -/
def note (d : Doc) (i : Nat) : String :=
  match d.lines[i]? with
  | none => ""
  | some l =>
      if l.gap then "!"
      else match d.nextSibling i with
        | some j =>
            let w := (d.lines[j]!).why
            if w == "zoom in" || w == "zoom out" || w == "" then "" else w
        | none => ""

/-- Whether a line's `why` names a law, rather than one of the words the kernel
writes for a movement of the display or for a line the user typed in. Only a
line whose step is a law application may be folded away, because only its name
can be moved up. -/
def isLawStep (w : String) : Bool :=
  !(w.isEmpty || w == "zoom in" || w == "zoom out" || w == "direct entry")

/-- Why line `i` was written. -/
def whyOf (d : Doc) (i : Nat) : String := (d.lines[i]?).elim "" Line.why

/-- Whether a gap follows line `i`. -/
def gapOf (d : Doc) (i : Nat) : Bool := (d.lines[i]?).elim false Line.gap

/-- Whether line `i` may be hidden by a collapse: never the focus, and never a
line a gap follows, so that no warning sign and no place a user is working can
be collapsed away. -/
def mayHide (d : Doc) (i : Nat) : Bool := i != d.focus && !d.gapOf i

/-- Every line, before any collapse: drawn at its own depth, with the name the
document writes at the end of it. -/
def shownAll (d : Doc) : List Shown :=
  (List.range d.lines.size).map fun i =>
    { index := i, depth := (d.lines[i]!).depth, note := d.note i }

/-- Fold a subproof that is a single law application into the line it was
zoomed in from, moving the law's name up onto that line.

The pattern is four lines drawn in a row: a line at depth `k`, the line a zoom
in wrote at depth `k+1`, one line at depth `k+1` that a law wrote, and the line
the matching zoom out wrote back at depth `k`. The two middle lines go, and the
name of the law is written at the end of the first — which is exactly what
applying that law to a *part* of the first line would have drawn. -/
def foldHere (d : Doc) : List Shown → Option (List Shown)
  | s0 :: s1 :: s2 :: s3 :: rest =>
      let k := s0.depth
      let w := d.whyOf s2.index
      if s0.note.isEmpty && s1.depth == k + 1 && s2.depth == k + 1 && s3.depth == k
          && d.whyOf s1.index == "zoom in" && d.whyOf s3.index == "zoom out"
          && isLawStep w && !d.gapOf s0.index
          && d.mayHide s1.index && d.mayHide s2.index then
        some ({ s0 with note := w } :: s3 :: rest)
      else none
  | _ => none

/-- Merge two zoom-ins matched by two zoom-outs into one zoom step.

The pattern is a level at depth `k` whose only two lines are the one a zoom in
wrote and the one a zoom out wrote, holding a single subproof at depth `k+1`,
and itself closed by a zoom out at depth `k-1`. That level held nothing of its
own, so its two lines go and its subproof is drawn one level further out. -/
def mergeHere (d : Doc) : List Shown → Option (List Shown)
  | s0 :: rest =>
      let k := s0.depth
      let inner := rest.takeWhile fun s => s.depth > k
      match k, inner, rest.dropWhile (fun s => s.depth > k) with
      | k' + 1, i0 :: _, sq :: sp :: tl =>
          if s0.note.isEmpty && sq.note.isEmpty
              && d.whyOf s0.index == "zoom in" && d.whyOf i0.index == "zoom in"
              && i0.depth == k + 1 && sq.depth == k && sp.depth == k'
              && d.whyOf sq.index == "zoom out" && d.whyOf sp.index == "zoom out"
              && (inner.filter fun s => s.depth == k + 1 && d.whyOf s.index == "zoom in").length == 1
              && d.mayHide s0.index && d.mayHide sq.index then
            some ((inner.map fun s => { s with depth := s.depth - 1 }) ++ sp :: tl)
          else none
      | _, _, _ => none
  | [] => none

/-- The first collapse that applies, scanning the drawn lines from the top.

A merge is tried before a fold at the same place, because a merge can expose a
fold and not the other way round: two zooms around a one-step subproof merge to
one zoom step, and that step then folds into the line above it. Folding first
would fold the inner subproof into the middle level and leave the middle level
standing. -/
def collapseStep (d : Doc) : List Shown → Option (List Shown)
  | [] => none
  | s :: rest =>
      match mergeHere d (s :: rest) with
      | some out => some out
      | none =>
          match foldHere d (s :: rest) with
          | some out => some out
          | none => (collapseStep d rest).map (s :: ·)

/-- The lines a display draws: every line of the document, at the depth and
with the name the collapses leave it, and without the lines they hide.

The pass is run to a fixpoint — each collapse can expose another, so a
threefold zoom merges twice and then folds — with the number of lines for fuel,
which is more than enough because every collapse hides two lines. -/
def shownLines (d : Doc) : List Shown :=
  go d.lines.size d.shownAll
where
  go : Nat → List Shown → List Shown
    | 0, ss => ss
    | fuel + 1, ss =>
        match collapseStep d ss with
        | some ss' => go fuel ss'
        | none => ss

end Doc
end Netty
