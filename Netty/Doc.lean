import Netty.Law

/-!
# The proof document

A Netty calculation is a sequence of lines with a *direction* in the left
margin, and it can be zoomed in to a main operand of the line before the focus,
which starts a subproof of its own with its own direction, its own type and its
own context. This module is that document, the pure transitions on it, and the
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
first. Zooming in appends the chosen operand as the first line of a new level
and pushes a frame carrying that level's type, direction and context. Zooming
out pops the frame and appends, to the level below, the line we zoomed in from
with the chosen operand replaced by the bottom line of the subproof.

Because every line of a still-open level lies after every line of the levels
below it, appending or inserting at the current level never disturbs an index
recorded in a frame.

## Focus

There is always exactly one focus, just after the line `Doc.focus`. It can be
moved to any earlier line *of the innermost level*, which is how a gap left by
direct entry is filled: taking a suggestion that reproduces the line already
below the focus replaces the warning sign with the law's name. Moving the focus
across levels, which real Netty allows, would mean recomputing the zoom stack
and is not done here.

## Gaps

`Line.gap` marks a logical gap between that line and the next: a step that no
law licenses. Direct entry creates one. `Doc.outcome` refuses to say what a
proof with a gap proves.
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

/-- The facts a zoom in to the `i`-th main operand of `e` adds to the context
(the document's table). Zooming in to an operand of `∧` gains the others; of
`∨`, their negations; of `a ⇒ b` on `a`, `¬b`, and on `b`, `a`; and dually for
`⇐`. Nothing else contributes a context. -/
def contextOf (e : Expr) (i : Nat) : List Expr :=
  match e with
  | bin op _ _ =>
      let ops := operands e
      let others := (List.range ops.length).filterMap fun j =>
        if j == i then none else ops[j]?
      match op with
      | .and => others.flatMap splitAnd
      | .or => others.flatMap (fun o => splitAnd (negate o))
      | .imp =>
          match ops[0]?, ops[1]? with
          | some l, some r => if i == 0 then splitAnd (negate r) else splitAnd l
          | _, _ => []
      | .rimp =>
          match ops[0]?, ops[1]? with
          | some l, some r => if i == 0 then splitAnd r else splitAnd (negate l)
          | _, _ => []
      | _ => []
  | _ => []

end Expr

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
  /-- Which main operand of that line we zoomed in to. -/
  operand : Nat := 0
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
  /-- Zoom in to the `i`-th main operand of the line before the focus. -/
    | zoomIn (operand : Nat)
  /-- Zoom out of the innermost level. -/
    | zoomOut
  /-- Move the focus to just after the given line. -/
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

/-- The suggestions for the line after the focus: for every variant of every
law in force whose connective the direction allows, the result of matching the
line before the focus against the variant's left side. Matching is modulo
associativity, so one variant can match in several ways — `a ∧ b ⇒ a` reads
`x ∧ y ∧ z` as `x ∧ (y ∧ z)` and as `(x ∧ y) ∧ z` — and each way is a
suggestion of its own. Suggestions that leave law variables unconstrained come
last, and a suggestion that would merely repeat the line — `a ⇐ a` from
reflexivity, say — is dropped. -/
def suggestions (d : Doc) : List Suggestion :=
  match d.frame?, d.focusLine? with
  | some f, some line =>
      let raw := d.allLaws.flatMap fun l =>
        l.variants.flatMap fun v =>
          if !(f.dir.allows f.ty v.op) then []
          else (Expr.matchAll v.lhs line.expr []).filterMap fun σ =>
            let r := v.rhs.instantiate σ
            if r == line.expr then none
            else some { law := v.law, op := v.op, result := r, holes := r.mvars }
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
  | .zoomIn i => do
      let f ← orElseError "the proof has not been started" d.frame?
      if d.focus + 1 != d.lines.size then
        throw "zoom in only from the last line; move the focus there first"
      let fl ← orElseError "the proof has not been started" d.focusLine?
      let sub ← orElseError s!"line {d.focus} has no main operand {i}" fl.expr.operands[i]?
      let pos := fl.expr.operandPos i
      let idx := d.lines.size
      let subTy := fl.expr.operandTy i f.ty
      let subDir := f.dir.zoom pos
      return { d with
        lines := d.lines.push
          { depth := d.depth + 1, expr := sub, why := "zoom in",
            ty := some subTy, dir := some subDir }
        stack := { ty := subTy, dir := subDir, start := idx,
                   zoomLine := some d.focus, operand := i, pos := pos,
                   ctx := (Expr.contextOf fl.expr i).map Law.context } :: d.stack
        focus := idx }
  | .zoomOut =>
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
          -- The document's three rules for the connective the new line gets.
          let newRel : Rel :=
            if f.pos == .neutral || rel.dir == .same then ⟨.same, false⟩ else ⟨parent.dir, false⟩
          let bottom := (d.lines[idxs.getLast!]!).expr
          let zoomExpr := (d.lines[zl]!).expr
          let e ← orElseError "the subproof cannot be put back into its line"
            (zoomExpr.replaceOperand f.operand bottom)
          let idx := d.lines.size
          return { d with
            lines := d.lines.push
              { depth := d.depth - 1, conn := some (newRel.op parent.ty), expr := e,
                why := "zoom out" }
            stack := parent :: rest
            focus := idx }
      | [_] => .error "the outermost proof cannot be zoomed out of"
      | [] => .error "the proof has not been started"
  | .setFocus n => do
      let f ← orElseError "the proof has not been started" d.frame?
      let l ← orElseError s!"there is no line {n}" d.lines[n]?
      if n < f.start || l.depth != d.depth then
        throw "the focus can only move within the innermost level of the proof"
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

end Doc
end Netty
