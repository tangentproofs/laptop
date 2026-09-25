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

## Conditional laws

A law whose consequent is a relation — `x ≤ x + y ⇐ 0 ≤ y`, or
`(a ⇒ b) ⇒ (a ∧ c ⇒ b ∧ c)` — has a reading in which that relation stands in the
margin and the antecedent is left over as a premise (`Law.conditional`). For a
number law it is the only reading a number line can take, its own main operator
`⇐` being one no number margin admits; for a boolean law it is a second reading
beside the one its own operator gives, kept from burying that one by the two
guards `Law.conditional` describes — conditional readings last in `Law.variants`,
so a dedup keeps the reading that needs nothing, and `Doc.rank` putting every
step that needs nothing first.

Either way, `Doc.suggestions` asks the laws in force whether they settle the
premise (`Law.settles`,
which is the same match the pane would make on a line holding the premise, so a
`context` law that zooming in supplied settles a domain condition such as
`0 ≤ y`). A settled premise is no premise: the step is an ordinary step. An
unsettled one is offered *with* the premise, and taking it leaves the document's
warning sign on the line the step was taken from, with the premise recorded there
(`Line.premise`) as what would close it. That is the document's type-checker and
gap: what the kernel can discharge it discharges, and what it cannot it says out
loud rather than passing over. `Doc.rank` puts a step that needs nothing before a
step that leaves a gap.

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

## Ranking the suggestions

Every widening of matching has made the list longer: modulo associativity,
symmetry and the identity element, then every main operand and every contiguous
segment of an association as a place a law may be applied to. `Doc.rank` puts the
list in order, by a heuristic that is written down rather than learned, so that
the same line and the same laws always give the same list and a number a user
reads off the pane means the same thing the next time. Most important key first:
applicable before unconstrained, then fewer unconstrained variables, then the
shorter line the step writes, then the more specific place (the whole line, the
single operands, the shorter runs, the longer runs), then the order the law file
itself is in. The shorter line outranks the place because that is what the order
is for: a fold only a run of operands can make would otherwise sit behind every
rearrangement of the whole line. `Doc.rank` has the whole rule and the reason for
each part of it. Nothing there decides whether a step is *sound* — every
suggestion in the list is one the kernel would take — so the order is free to be
a guess about usefulness and nothing more.

## Focus

There is always exactly one focus, just after the line `Doc.focus`. Moving it
back is how a gap left by direct entry is filled: taking a suggestion that
reproduces the line already below the focus replaces the warning sign with the
law's name.

The document lets a click land *anywhere*, and so does `Cmd.setFocus`: the line
may be at an outer level, or inside a subproof that has already been zoomed out
of, and the zoom stack is recomputed so that the line's level is the innermost
open one again. `Doc.refocus` is the whole move, and it is made of two inverse
steps and nothing else:

* `Doc.closeToDepth` closes levels, as a run of zoom-outs the user could have
  made themselves, so each abandoned subproof still puts its bottom line back
  into the line it was zoomed in from; and
* `Doc.reopenStep` re-opens the last closed one, as the exact inverse of a
  zoom-out: the line that zoom-out wrote goes away again and the frame is
  rebuilt from what the level's first line carries — its type, its direction and
  the part of the line above it was opened on — so the direction, type and
  context that come with the focus are the ones that level always had.

Because both are steps the user could have taken, the state a click reaches is
one they could have reached by zooming, and a later zoom-out splices from it
exactly as it would have then, gap and all.

What a click cannot reach is a line whose subproof was closed *before* later
work was written: taking that subproof back out from under the work would undo
it, so the kernel refuses. `Doc.canFocus` is that refusal — it is defined as
`Doc.refocus` succeeding, so the two cannot disagree — and it is what the API
reports as `focusable`, with `Doc.reopensOn` saying which of the two moves a
click would make.

## Gaps

`Line.gap` marks a logical gap between that line and the next: a step that no
law licenses. Direct entry creates one, and so does a conditional law whose
premise nothing in force settles — that one records the premise beside the gap
(`Line.premise`), since a gap with a known reason is worth more than a bare
warning sign. `Doc.outcome` refuses to say what a proof with a gap proves,
whichever kind it is.

A gap is carried *out* of the subproof it was left in. Zooming out splices a
level's bottom line back into the line it was zoomed in from, and if that level
still holds a gap then the step from the line we zoomed in from to the spliced
line is not licensed either — the subproof is the justification, and it has a
hole in it. So `Doc.zoomOut` marks a gap on the line it zoomed in from
(`Doc.openGaps` says whether there is one to carry), and the outer level draws
the warning sign on the line just before the splice, which is where the
document puts it. A subproof with no gaps splices as it always did: a single
law application still folds with its name lifted, and a longer justified
subproof still leaves the outer step unannotated, its justification being the
lines inside.

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
carries a law name or a warning sign. Neither ever hides the focus or a line
with a gap (`Doc.mayHide`), and a collapse fires only where the matching
zoom-out has already been written, so no line of an open level is ever hidden.
A collapsed subproof is therefore not there to be clicked on, and re-opening
reaches the subproofs a display draws — which is every subproof of more than
one step. The other direction takes care of itself: re-opening leaves the focus
inside the level, and a level holding the focus is never collapsed. The pass is
a fixpoint, so a threefold zoom merges twice and then folds.
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
  -- Zooming in to a branch of `if c then t else e fi` may assume the condition,
  -- or its negation: the other branch is not reached there. That is the document's
  -- table for the form, and the argument is the one for `⇒` — strengthening the
  -- then-branch under `c` strengthens `c ∧ t`, which is the only way the whole is
  -- reached when `c` holds. The condition itself gains nothing.
  | cond c _ _ =>
      if start == 1 && len == 1 then splitAnd c
      else if start == 2 && len == 1 then splitAnd (negate c)
      else []
  -- "For the body, we gain the context `v: d`" — the document's Scope section,
  -- said there of the function `〈v:d→b〉`, and a quantifier binds the same way: one
  -- context law per identifier the quantifier binds. The domain gains nothing,
  -- since it is outside the scope of what is bound — the document says it "cannot
  -- mention `v`", and `Netty.Parser` refuses one that does.
  | quant _ ids d _ =>
      if start == 1 && len == 1 then ids.map fun v => bin .mem (var v) d
      else []
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

/-- How specific this part is, as a number to sort by: the whole line is `0`, a
single main operand `1`, and a run of operands its own length. So the whole line
comes before the operands, the operands before the runs, and a shorter run before
a longer one — smaller means more specific, and more specific comes first
(`Doc.rank`). -/
def rank : Part → Nat
  | whole => 0
  | operand _ => 1
  | segment _ len => len

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
  /-- On the first line of a level, the part of the line above that the zoom in
  opened it on — so that a closed subproof can be re-entered after its frame has
  been popped, the frame being rebuilt from the part (`Doc.reopenStep`). -/
  part : Option Part := none
  /-- When the step from this line to the next was licensed by a *conditional*
  law whose premise the laws in force did not settle, that premise: what is left
  to prove. It is what the gap on this line is a gap *for*. -/
  premise : Option Expr := none
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
that matching left unconstrained — the document's "small dialog box" — which the
kernel will not apply until they are supplied. They are supplied by name, as the
`bind` of `Cmd.apply`; the kernel never guesses one. -/
structure Suggestion where
  /-- The name of the law it comes from. -/
  law : String
  /-- The connective it would put in the margin. -/
  op : BinOp
  /-- The line it would write. -/
  result : Expr
  /-- Law variables the match left unconstrained. -/
  holes : List String
  /-- For a conditional reading of a law (`Law.conditional`), the premise that
  the laws in force did not settle: taking this step leaves a gap, and this is
  what would close it. `none` when the step needs nothing — either the reading
  was unconditional, or its premise is settled and the step is an ordinary
  one. -/
  premise : Option Expr := none
  /-- The place of the line the step rewrites: the whole line, one main operand,
  or a contiguous segment of the association. Two places can write one and the
  same line, and then the step is offered once, credited to the first of them
  (`Doc.suggestions`); what this field is for is the *order* the suggestions come
  in, where it is the key after the length of the line (`Doc.rank`). -/
  part : Part
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
  /-- Take the `n`-th suggestion, supplying the law variables the match left
  unconstrained — the document's small dialog box. With no bindings this is the
  command it always was. -/
    | apply (n : Nat) (bind : Subst := [])
  /-- Take the applicable suggestion from the named law; when several apply,
  `expect` says which by giving the line it would write. `bind` supplies the law
  variables the match left unconstrained, and then `expect` is the line the
  suggestion writes *after* they are supplied. -/
    | applyNamed (name : String) (expect : Option (BinOp × Expr)) (bind : Subst := [])
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

/-- Keep the first element with each `key`. -/
private def dedupBy {α β} [BEq β] (key : α → β) (xs : List α) : List α :=
  (xs.foldl (fun acc x => if acc.any (fun y => key y == key x) then acc else x :: acc) []).reverse

/-- Put `k` into a list of numbers that is already sorted, before the first one
it is not greater than — so an equal number already there stays before it. -/
private def insertNat (k : Nat) : List Nat → List Nat
  | [] => [k]
  | j :: js => if k ≤ j then k :: j :: js else j :: insertNat k js

/-- Sort a list of numbers, smallest first. -/
private def sortNats : List Nat → List Nat
  | [] => []
  | k :: ks => insertNat k (sortNats ks)

/-- Reorder `xs` so that a smaller `key` comes first, keeping the order `xs`
already had among elements of equal key.

It is one pass over `xs` per distinct key value, which is a handful wherever it
is used here, and — unlike a comparison sort — it is plainly structurally
recursive, which is what lets `decide` run a whole session inside Lean's kernel
(`Netty.Replay`). Being stable is what lets several of these compose into one
order: run for the least important key first and the most important key last, and
each pass keeps what the passes before it decided. -/
private def stableBy {α} (key : α → Nat) (xs : List α) : List α :=
  (sortNats (dedup (xs.map key))).flatMap fun k => xs.filter fun x => key x == k

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

/-- The gaps left inside the innermost open level: the lines a gap follows at
or after that level's first line. Every line from there on belongs to this
level or to a subproof of it, and a subproof that was zoomed out of has already
left its own gap on a line of this level, so this is every gap the level's
calculation still has in it. -/
def openGaps (d : Doc) : List Nat :=
  match d.frame? with
  | some f => d.gaps.filter (· ≥ f.start)
  | none => []

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

/-- Put the suggestions in the order a window offers them, and `apply #N`
numbers them in.

It is a heuristic, and it is written down here rather than learned: the same line
and the same laws always give the same list, so a number a user reads off the
pane means the same thing the next time they see it. Most important key first:

1. **Applicable before unconstrained.** A suggestion whose match left a law
   variable free cannot be applied until the variable is supplied, so every
   suggestion that *can* be taken comes before every suggestion that cannot.
   This is the split the pane already drew, as greyed rows at the end.
2. **Fewer unconstrained variables first.** Among the suggestions that cannot yet
   be taken, the one that needs one variable supplied is nearer to being a step
   than the one that needs three. (Zero is fewest, so this key already says what
   key 1 says; both are written down because both are promises.)
3. **The shorter line first.** A calculation is usually looking for the step that
   makes the line smaller — `x ∧ y ∧ y ∧ z = x ∧ y ∧ z` rather than
   `x ∧ y ∧ y ∧ z = ¬¬(x ∧ y ∧ y ∧ z)` — and every law that can fold a line has
   a variant that can pad it, so the padding buries the folding unless the fold
   is what floats.
4. **The more specific place first** (`Part.rank`): the whole line, then the
   single main operands, then the contiguous runs of operands, shortest run
   first. Among steps that write a line of the same length, a step on the whole
   line is the one a reader of the proof sees as one step, and a step on a run of
   three operands is the most surgical thing the kernel offers.
5. **Then the order the suggestions were made in**, which is: the context's laws
   before the loaded ones, the law list's own order within that, the variants of
   a law in order, and the readings of one variant in the order `Expr.matchAll`
   finds them (the ones needing no rearrangement first). So the last word belongs
   to the law file, which is the one part of the order a user writes themselves.

Key 3 outranks key 4 because that is what the order is *for*. When the place came
first, every rearrangement of the whole line came before any step on a part of
it, and a fold that only a run of operands can make sat where nobody would find
it: on `x ∧ y ∧ y ∧ z` under the shipped law list,
`x ∧ y ∧ y ∧ z = x ∧ y ∧ z` was the 124th of 227 suggestions, behind some hundred
ways of reassociating and commuting the whole line. With the shorter line first it
is the 3rd, behind two contractions of the same length that `distributive` makes
on the whole line.

Nothing here decides *whether* a step is sound — every suggestion in the list is
one the kernel would take — so the order is free to be a guess about usefulness
and nothing more. -/
def rank (ss : List Suggestion) : List Suggestion :=
  -- Least important key first: each pass keeps the order the passes before it
  -- left, so the last pass has the first word. The applicable/unconstrained pass
  -- is implied by the one that counts the free variables; it is kept so that the
  -- composition reads as the rule above is written.
  stableBy (fun s => if s.holes.isEmpty then 0 else 1)
    (stableBy (fun s => if s.premise.isNone then 0 else 1)
      (stableBy (fun s => s.holes.length)
        (stableBy (fun s => s.result.size)
          (stableBy (fun s => s.part.rank) ss))))

/-- The suggestions for the line after the focus: for every place of the line
before the focus (`Doc.sites`) and every variant of every law in force whose
connective that place's direction allows, the result of matching the place
against the variant's left side and putting the variant's right side back.

A place is the whole line, one of its main operands, or a contiguous segment of
its association, so a law applies "to a part, as a result of minimization" as
well as to the line entire: `a ∨ a = a` takes `x ∧ (y ∨ y)` to `x ∧ y` in one
step, where before it took a zoom in and a zoom out, and `a ∧ a = a` takes
`x ∧ y ∧ y ∧ z` to `x ∧ y ∧ z`, which no rewrite of the whole line or of a single
operand can reach.

Matching is modulo associativity, so one variant can match one place in several
ways — `a ∧ b ⇒ a` reads `x ∧ y ∧ z` as `x ∧ (y ∧ z)` and as `(x ∧ y) ∧ z` —
and each way is a suggestion of its own. A suggestion that would merely repeat
the line — `a ⇐ a` from reflexivity, say — is dropped, two places that write one
and the same line are offered once, and what is left is put in the order
`Doc.rank` describes. -/
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
                  else
                    -- A conditional reading carries its premise, instantiated by
                    -- the same match. A premise the laws in force settle is no
                    -- premise at all; one that still mentions a law variable is
                    -- not even statable, so its variables are holes as the
                    -- result's are.
                    let q := v.premise.map (·.instantiate σ)
                    let left := match q with
                      | some q => if Law.settles d.allLaws q then none else some q
                      | none => none
                    some { law := v.law, op := o, result := r,
                           holes := (r.mvars ++ (left.elim [] Expr.mvars)).eraseDups,
                           premise := left, part := site.part }
              | none => none
      -- Two places can write one line: rewriting `x ∧ y` inside `x ∧ y ∧ z` and
      -- rewriting the whole line can come to the same thing. That is one step,
      -- not two, so it is offered once — credited to the first place that made
      -- it, which is the most general of them, `Doc.sites` offering the whole
      -- line before a part and a shorter run before a longer.
      rank (dedupBy (fun s => (s.law, s.op, s.result)) raw)
  | _, _ => []

/-- Write a suggestion into the focus. When the line already below the focus is
exactly what the suggestion offers, no line is added: the suggestion justifies
the step that was there, and the warning sign becomes the law's name. -/
def applySuggestion (d : Doc) (s : Suggestion) (bind : Subst := []) : Except String Doc := do
  -- The bindings are the document's small dialog box: they supply the law
  -- variables that matching left unconstrained. Supplying one is not a new kind
  -- of step and needs no new argument for soundness — matching pinned some of
  -- the law's variables and the law holds for *every* instantiation of the rest,
  -- so any expression may stand in their place. All they do is instantiate.
  for (n, _) in bind do
    if !s.holes.contains n then
      throw s!"this suggestion has no unconstrained variable ‘{n}’\
        {if s.holes.isEmpty then "" else s!"; it leaves {String.intercalate ", " s.holes}"}"
  let result := s.result.instantiate bind
  -- A premise is asked again after the bindings, because supplying a variable can
  -- turn a premise the laws in force could not settle into one they can.
  let premise := (s.premise.map (·.instantiate bind)).bind fun q =>
    if Law.settles d.allLaws q then none else some q
  let holes := (result.mvars ++ (premise.elim [] Expr.mvars)).eraseDups
  if !holes.isEmpty then
    throw s!"the suggestion leaves {String.intercalate ", " holes} unconstrained; \
      supply them by name"
  let fl ← orElseError "the proof has not been started" d.focusLine?
  -- A conditional reading whose premise the laws in force did not settle leaves
  -- the document's warning sign, on the line the step is taken from, and records
  -- the premise there: the same gap direct entry leaves, with its reason written
  -- down. A step that needs nothing clears the sign as it always did.
  let here : Line := { fl with gap := premise.isSome, premise := premise }
  match d.nextAtLevel d.focus with
  | some j =>
      let nl := d.lines[j]!
      if nl.conn == some s.op && nl.expr == result then
        return (d.withLine j { nl with why := s.law }).withLine d.focus here
      else
        -- The new line goes between, so any gap this line already carried — and
        -- what it was for — belongs to the step from the new line on.
        let line : Line :=
          { depth := d.depth, conn := some s.op, expr := result, why := s.law,
            gap := fl.gap, premise := fl.premise }
        return (d.withLine d.focus here).insertAfterFocus line
  | none =>
      let line : Line :=
        { depth := d.depth, conn := some s.op, expr := result, why := s.law, gap := false }
      return (d.withLine d.focus here).insertAfterFocus line

/-- Zoom out of the innermost level: append, to the level below, the line we
zoomed in from with the chosen part replaced by the bottom line of the subproof
(`Part.replace`, so a segment goes back left-associated as `Expr.rebuildOp`
writes an association), and pop the frame. The subproof's own lines stay in the
document, which is what the `ty` and `dir` a level's first line carries are for.

The connective the new line gets follows the document's three rules: `=` when
the part's position is neutral or the subproof proved an equality, and the
parent level's own direction otherwise. Zooming out of a level with a single
line is an undo, as the document says: the line goes away again.

A subproof that still holds a gap is itself a gap at the level below — its
bottom line does not follow from its first one — so the line we zoomed in from
is marked with a gap of its own, and the outer level draws the warning sign on
the line just before the splice. A level with no gaps splices exactly as
before. (The undo case needs no such mark: a level of one line has had no step
taken in it, and only a step can leave a gap.) -/
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
      let lines :=
        if d.openGaps.isEmpty then d.lines
        else d.lines.set! zl { d.lines[zl]! with gap := true }
      return { d with
        lines := lines.push
          { depth := d.depth - 1, conn := some (newRel.op parent.ty), expr := e,
            why := "zoom out" }
        stack := parent :: rest
        focus := idx }
  | [_] => .error "the outermost proof cannot be zoomed out of"
  | [] => .error "the proof has not been started"

/-- Whether line `i` belongs to a level that is *open*: its depth is one the
stack still has, and it lies at or after that level's first line. The lines this
refuses belong to a subproof that has been zoomed out of — deeper than the
innermost open level, or before the first line of the open level at their own
depth, which is to say in an earlier, closed subproof at that depth. Those are
the lines `Doc.reopenStep` may be able to bring back. -/
def inOpenLevel (d : Doc) (i : Nat) : Bool :=
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

/-- Undo the last zoom-out: re-open the subproof whose bottom line the last line
of the document splices back, and leave the focus on that bottom line.

This is the exact inverse of `Doc.zoomOut`, which is what makes the state it
reaches one the user could have reached by zooming and never left. The line the
zoom out wrote goes away again; the frame is rebuilt from what the level's first
line carries — its type, its direction and the part of the line above that the
zoom in opened it on — with the position and the context recomputed from that
part, exactly as `Cmd.zoomIn` computed them, off a line the zoom out did not
change. So the frame is the one that level always had, down to its context laws.

The gap that the zoom out may have written on the line it zoomed in from is
taken off again. That is exactly the flag the zoom out wrote: the last line of a
level never carries a gap — a gap marks the step from a line to the *next* one,
and there is none — so the line was clean when the zoom in left it, and nothing
between then and the zoom out could have marked it.

Re-opening is refused when the last line of this level is not the zoom out's:
work has been written since, and taking the subproof back out from under it
would undo that work. -/
def reopenStep (d : Doc) : Except String Doc := do
  if d.stack.isEmpty then throw "the proof has not been started"
  if d.lines.size < 3 then throw "there is no closed subproof to re-open here"
  let last := d.lines.size - 1
  let ll := d.lines[last]!
  if ll.depth != d.depth then
    throw "there is no closed subproof to re-open at this level"
  if ll.why != "zoom out" then
    throw "the last line of this level was not written by zooming out; the \
      subproof before it cannot be re-opened without undoing that work"
  let bottom := last - 1
  if (d.lines[bottom]!).depth != d.depth + 1 then
    throw "there is no closed subproof to re-open here"
  let zl ← orElseError "there is no closed subproof to re-open here"
    ((List.range bottom).reverse.find? fun j => (d.lines[j]!).depth ≤ d.depth)
  if (d.lines[zl]!).depth != d.depth then
    throw "the closed subproof does not sit inside a line of this level"
  let start := zl + 1
  let fl := d.lines[start]!
  if fl.depth != d.depth + 1 || fl.why != "zoom in" then
    throw "there is no closed subproof to re-open here"
  let subTy ← orElseError "the closed subproof records no type" fl.ty
  let subDir ← orElseError "the closed subproof records no direction" fl.dir
  let part ← orElseError "the closed subproof records no part to re-open it on" fl.part
  let zle := (d.lines[zl]!).expr
  let pos := part.posOf zle
  return { d with
    lines := d.lines.pop.set! zl { d.lines[zl]! with gap := false }
    stack := { ty := subTy, dir := subDir, start := start, zoomLine := some zl,
               part := part, pos := pos,
               ctx := (part.contextOf zle).map Law.context } :: d.stack
    focus := bottom }

/-- Move the focus to just after line `n`, wherever in the proof that line is.

The document lets a click land anywhere, and so does this. Three things may have
to happen first, in this order:

* levels that start after the line are closed, as a run of zoom-outs
  (`Doc.closeToDepth` does the same for a line below the innermost level);
* levels the line is inside that have been zoomed out of are re-opened, one
  `Doc.reopenStep` each, innermost last — so a click goes back into a subproof
  the user had left, with that level innermost again and its context in force;
* any levels still open below the line's own are closed.

Each phase is bounded: closing spends a level, re-opening spends the line the
zoom out wrote. What is refused is a line whose subproof was closed *before*
later work was written — re-opening it would mean taking that work back — and
the refusal is what `Doc.canFocus` reports, so the window can grey exactly the
lines a click cannot reach. -/
def refocus (d : Doc) (n : Nat) : Except String Doc := do
  if d.stack.isEmpty then throw "the proof has not been started"
  let l ← orElseError s!"there is no line {n}" d.lines[n]?
  let d ← closePhase d.stack.length d
  let d ← reopenPhase d.lines.size d
  if !d.inOpenLevel n then
    throw s!"line {n} belongs to a subproof that was closed before later work \
      was written; the focus cannot go back into it without undoing that work"
  let d ← d.closeToDepth l.depth
  return { d with focus := n }
where
  /-- Close the levels that begin after the line we are going to. -/
  closePhase : Nat → Doc → Except String Doc
    | 0, d => .ok d
    | fuel + 1, d =>
        match d.frame? with
        | none => .ok d
        | some f =>
            if f.start ≤ n then .ok d
            else do
              let d := { d with focus := d.lines.size - 1 }
              closePhase fuel (← d.zoomOut)
  /-- Re-open the closed levels the line is inside, outermost first. -/
  reopenPhase : Nat → Doc → Except String Doc
    | 0, d => .ok d
    | fuel + 1, d =>
        match d.lines[n]? with
        | none => .ok d
        | some l =>
            if l.depth ≤ d.depth then .ok d
            else
              match d.frame? with
              | none => .ok d
              | some f =>
                  if f.start > n then
                    throw s!"line {n} belongs to a subproof that was closed \
                      before later work was written; the focus cannot go back \
                      into it without undoing that work"
                  else do reopenPhase fuel (← d.reopenStep)

/-- Whether the focus may be moved to just after line `i`: whether
`Doc.refocus` would take it there. The predicate is the move succeeding, so the
window greys a line exactly when clicking it would be refused. -/
def canFocus (d : Doc) (i : Nat) : Bool := (d.refocus i).toOption.isSome

/-- Whether moving the focus to line `i` would re-open a subproof that has been
zoomed out of, rather than stay in or close down to an open level. This is what
lets a client say which of the two a click would do. -/
def reopensOn (d : Doc) (i : Nat) : Bool := !d.inOpenLevel i && d.canFocus i

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
  | .apply n bind => do
      let s ← orElseError s!"there is no suggestion {n}" d.suggestions[n]?
      d.applySuggestion s bind
  | .applyNamed name expect bind => do
      -- With no bindings this is what it always was: the suggestions that can be
      -- taken as they stand. With bindings it is the suggestions whose every
      -- unconstrained variable the bindings supply, and `expect` is then the line
      -- the suggestion writes once they are supplied.
      let ok := d.suggestions.filter fun s =>
        s.law == name &&
          (if bind.isEmpty then s.holes.isEmpty
           else s.holes.all fun h => (bind.lookup h).isSome) &&
          (match expect with
           | some (o, e) => s.op == o && s.result.instantiate bind == e
           | none => true)
      match ok with
      | [s] => d.applySuggestion s bind
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
          gap := hasNext && fl.gap, premise := if hasNext then fl.premise else none }
      -- The gap this line now carries is the direct entry's own, which no premise
      -- would close; whatever it carried before moves down with the line it was
      -- a gap before.
      return (d.withLine d.focus { fl with gap := true, premise := none }).insertAfterFocus line
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
            ty := some subTy, dir := some subDir, part := some part }
        stack := { ty := subTy, dir := subDir, start := idx,
                   zoomLine := some d.focus, part := part, pos := pos,
                   ctx := (part.contextOf fl.expr).map Law.context } :: d.stack
        focus := idx }
  | .zoomOut => d.zoomOut
  | .setFocus n => d.refocus n

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
