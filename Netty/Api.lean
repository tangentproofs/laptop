import Netty.Json
import Netty.Script

/-!
# A request/response service over a proof session

The kernel's panes are text, and its script language is text, which is all a
terminal needs. A window with three panes needs one thing more: the *document*
behind those panes, in a form something other than Lean can draw — where each
line knows its depth, its margin connective, its main operands, the parts a
click may zoom in to and how the script language names each of them, and each
suggestion knows its number.

That is all this module is. A request is one JSON object; the answer is one
JSON object carrying the whole state of the session after it. Nothing here
decides anything about a proof: `cmd` hands its argument to
`Netty.Parser.scriptLine`, so a client can do exactly what a script can do and
nothing else, and every change still goes through `Netty.Doc.step`.

## The requests

```
{"op": "state"}                the session as it stands
{"op": "cmd",  "arg": "..."}   run one line of the script language
{"op": "demo", "arg": "..."}   restart, replaying a built-in demonstration
{"op": "reset"}                restart with the same laws and no proof
{"op": "save"}                 the proof file, as text, in "save"
{"op": "load", "arg": "..."}   restart from the text of a proof file
```

An `"id"` is echoed back so a client may have several requests outstanding.
The answer is `{"id", "ok", "error", "state", "save"}`; `state` is the session
*after* the request, and after a failed request it is the session unchanged,
so a client can always draw the answer it gets.

The file commands of the script language — `laws`, `load` and `save` with a
path — are refused here: this service is spoken to over a socket by a program
that is not Lean, and it does not open files on that program's say-so. Loading
and saving a proof go through `load` and `save`, which carry the text itself.
-/

namespace Netty
namespace Api

open Lean (Json ToJson FromJson toJson fromJson?)

/-- A part of a line, as a window names and draws it: a zoom target on the line
before the focus (`LineView.zooms`), or the place a suggestion would rewrite
(`SuggestionView.site`).

`name` is what the kernel calls the part (`Netty.Part.render`), so a window
offers a zoom by handing back the very argument `zoom` takes: a single main
operand by its number, a contiguous segment of an association by `start:length`.
The client does not compose that string, which is what keeps a click, a
suggestion's site and a script zoom from ever meaning different things by the
same part. The whole line is a part too — it is where most suggestions apply —
and `span` counts no operands for it, so `len = 0` is how a client tells it from
a run; it never appears among the zoom targets, being the level one is already
on. -/
structure PartView where
  /-- What `zoom` calls it: `"1"`, or `"1:2"` for a segment; `"the whole line"`
  for the whole line, which is not a zoom target. -/
  name : String
  /-- The part, rendered as it stands in the line. -/
  text : String
  /-- Which main operand the run starts at; `0` for the whole line. -/
  start : Nat
  /-- How many main operands it takes: `1` for a single operand, two or more
  for a segment of an association, and `0` for the whole line. -/
  len : Nat
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-- A line of the proof, as a client draws it. -/
structure LineView where
  /-- Its index in `Doc.lines`, which is what the script language calls it. -/
  index : Nat
  /-- How deeply it is drawn in subproofs — its own depth, unless merging two
  zooms into one lifted it a level. -/
  depth : Nat
  /-- The margin connective, or `""` on the first line of a level. -/
  conn : String
  /-- The direction of the level this line opens, or `""`. -/
  dir : String
  /-- The whole line, rendered. -/
  expr : String
  /-- `"neg"`, `"bin"` or `"atom"`: whether `op` is written before the one main
  operand, between them, or not at all. -/
  kind : String
  /-- The main operator's symbol, or `""`. -/
  op : String
  /-- The main operands, rendered as they stand in `expr`. -/
  parts : List String
  /-- The parts a click may zoom in to, in the kernel's own order: each main
  operand, then each contiguous segment of the association. Empty unless this
  line can be zoomed in to at all, which is what `zoomable` says. -/
  zooms : List PartView
  /-- What produced the line. -/
  why : String
  /-- Whether the step to the next line is unjustified. -/
  gap : Bool
  /-- What is written at the end of the line: the law that justifies the step
  to the next one, or a warning sign. -/
  note : String
  /-- Whether the focus sits just after this line. -/
  focused : Bool
  /-- Whether the focus may be moved here. A line of an outer level may be: the
  kernel closes the levels below it, as a run of zoom-outs would. So may a line
  of a subproof that has been zoomed out of, which the kernel re-opens — unless
  work has been written since it was closed, which re-opening would undo. -/
  focusable : Bool
  /-- Whether moving the focus here would re-open a subproof that has been
  zoomed out of, rather than stay in an open level or close down to one. -/
  reopens : Bool
  /-- Whether this line can be zoomed in to: whether `zooms` offers anything. -/
  zoomable : Bool
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-- A suggestion, as a client draws it. -/
structure SuggestionView where
  /-- Its number, which is what `apply #N` calls it. -/
  index : Nat
  /-- The law it comes from. -/
  law : String
  /-- The connective it would put in the margin. -/
  op : String
  /-- The line it would write. -/
  result : String
  /-- Law variables the match left unconstrained; a suggestion with any of
  these cannot be applied. -/
  holes : List String
  /-- The place on the line before the focus that this step rewrites: the whole
  line, one of its main operands, or a contiguous run of them. It is named as
  the zoom targets are named, so a window can draw the site of a suggestion and
  the target of a click as the same part of the same line, which is what they
  are (`Doc.sites`). -/
  site : PartView
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-- The whole state of a session: enough to draw the three panes, and nothing
a client has to remember between requests. -/
structure StateView where
  /-- Whether the proof has been started. -/
  started : Bool
  /-- The line the focus sits after. -/
  focus : Nat
  /-- The nesting depth of the innermost open level. -/
  depth : Nat
  /-- The type of the innermost open level: `"boolean"`, `"number"` or `""`. -/
  ty : String
  /-- The direction of the innermost open level, as it is written at its
  type. -/
  dir : String
  /-- The connectives the innermost level's direction allows in the margin,
  which is what a direct entry may choose from. -/
  conns : List String
  /-- The lines the display draws, in reading order: every line of the
  document except the ones the collapses hide. -/
  lines : List LineView
  /-- The laws the zoom stack has added, innermost level first. -/
  context : List String
  /-- The suggestions for the line after the focus. -/
  suggestions : List SuggestionView
  /-- What the proof proves, or why it does not prove anything yet. -/
  outcome : String
  /-- Whether it proves something. -/
  proved : Bool
  /-- Whether there is anything to undo. -/
  canUndo : Bool
  /-- Whether the innermost level can be zoomed out of. -/
  canZoomOut : Bool
  /-- How many laws are loaded, not counting the context. -/
  lawCount : Nat
  /-- The proof pane as the command line prints it. -/
  proofPane : String
  /-- The context pane as the command line prints it. -/
  contextPane : String
  /-- The suggestions pane as the command line prints it. -/
  suggestPane : String
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-- One request. -/
structure Request where
  /-- Echoed back in the answer. -/
  id : Nat := 0
  /-- Which request this is. -/
  op : String
  /-- Its argument: a script line, a demonstration's name, or a proof file. -/
  arg : String := ""
  deriving Repr, DecidableEq, Inhabited, ToJson

/-- One answer. -/
structure Response where
  /-- The `id` of the request this answers. -/
  id : Nat
  /-- Whether the request was carried out. -/
  ok : Bool
  /-- Why it was not, or `""`. -/
  error : String
  /-- The session after the request — unchanged, when it failed. -/
  state : StateView
  /-- The text of a proof file, for `save`; `""` otherwise. -/
  save : String
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-- Read a request. Only `op` is required. -/
def Request.ofJson (j : Json) : Except String Request := do
  let op ← j.getObjValAs? String "op"
  return { op := op
           id := (j.getObjValAs? Nat "id").toOption.getD 0
           arg := (j.getObjValAs? String "arg").toOption.getD "" }

/-- How a type is named in the protocol. -/
def tyName : Ty → String
  | .boolean => "boolean"
  | .number => "number"

/-- A part of `line`, named and rendered as a window draws it. One function, so
a zoom target and a suggestion's site cannot disagree about what a part is
called or how it reads. -/
def partView (line : Expr) (p : Part) : PartView :=
  let (start, len) := p.span
  { name := p.render, text := p.textIn line, start := start, len := len }

/-- One line of the proof, as a client draws it: a line the display collapses
leave standing (`Doc.shownLines`), at the depth and with the name they leave it
with. Its `index` is still its index in the document, which is what `focus N`
calls it, so a collapse never changes what a click means. -/
def lineView (d : Doc) (s : Shown) : LineView :=
  let i := s.index
  let l := d.lines[i]!
  let focused := i == d.focus && !d.stack.isEmpty
  -- Only the last line of the innermost open level can be zoomed in to, and
  -- then every zoomable part of it can be — the main operands and the segments
  -- of its association, exactly what `Doc.sites` offers a law.
  let zs : List PartView :=
    if focused && i + 1 == d.lines.size then
      (Doc.parts l.expr).filterMap fun p =>
        if !p.zoomable then none
        else (p.exprOf l.expr).map fun _ => partView l.expr p
    else []
  { index := i
    depth := s.depth
    conn := match l.conn with | some o => o.symbol | none => ""
    dir := match l.conn, l.ty, l.dir with
      | none, some ty, some dir => dir.symbol ty
      | _, _, _ => ""
    expr := l.expr.render
    kind := match l.expr with
      | .neg _ => "neg"
      | .bin _ _ _ => "bin"
      | _ => "atom"
    op := l.expr.mainOp
    parts := l.expr.operandTexts
    zooms := zs
    why := l.why
    gap := l.gap
    note := s.note
    focused := focused
    focusable := d.canFocus i
    reopens := d.reopensOn i
    zoomable := !zs.isEmpty }

/-- The whole state of a session. -/
def stateView (s : Session) : StateView :=
  let d := s.doc
  { started := !d.stack.isEmpty
    focus := d.focus
    depth := d.depth
    ty := match d.frame? with | some f => tyName f.ty | none => ""
    dir := match d.frame? with | some f => f.dir.symbol f.ty | none => ""
    conns := match d.frame? with
      | some f => ([BinOp.eq, .imp, .rimp, .lt, .gt, .le, .ge].filter
          (f.dir.allows f.ty ·)).map BinOp.symbol
      | none => []
    lines := d.shownLines.map (lineView d)
    context := d.contextLaws.map (·.stmt.render)
    suggestions :=
      let line := (d.focusLine?.map Line.expr).getD .top
      (List.range d.suggestions.length).map fun i =>
        let g := d.suggestions[i]!
        { index := i, law := g.law, op := g.op.symbol, result := g.result.render,
          holes := g.holes, site := partView line g.part }
    outcome := d.renderOutcome
    proved := d.outcome.toOption.isSome
    canUndo := !s.history.isEmpty
    canZoomOut := d.stack.length > 1
    lawCount := d.laws.length
    proofPane := d.renderProof
    contextPane := d.renderContext
    suggestPane := d.renderSuggestions }

/-- Carry out a request: the session after it, and the text of a proof file
when it asked for one. The laws in force survive `reset`, `demo` and `load`,
because they came from the command line that started the service. -/
def handle (s : Session) (r : Request) : Except String (Session × Option String) :=
  match r.op with
  | "state" => .ok (s, none)
  | "reset" => .ok ({ doc := { laws := s.doc.laws } }, none)
  | "save" => .ok (s, some (saveText s.doc))
  | "load" => do
      let d ← loadText r.arg
      return ({ doc := { d with laws := s.doc.laws } }, none)
  | "demo" => do
      let text ← orElseError
        s!"there is no demonstration named ‘{r.arg}’; there are \
          {String.intercalate ", " (Demo.all.map (·.1))}"
        (Demo.all.lookup r.arg)
      let cs ← Parser.script text
      -- The demonstration's own printing commands have nothing to print to;
      -- its document commands are replayed one at a time, so that a user can
      -- undo back through them.
      let s' ← cs.foldlM
        (fun acc (_, c) => match c with | .doc dc => acc.step dc | _ => .ok acc)
        ({ doc := { laws := s.doc.laws } } : Session)
      return (s', none)
  | "cmd" => do
      let c ← orElseError "there is no command on this line" (← Parser.scriptLine r.arg)
      match c with
      | .doc dc => return (← s.step dc, none)
      | .undo => return (← s.undo, none)
      -- The answer carries all three panes and the outcome already.
      | .proof | .suggest | .context | .check _ => return (s, none)
      | .laws _ | .load _ | .save _ =>
          throw "this service does not open files; load and save carry the \
            proof itself"
  | op => .error s!"there is no request ‘{op}’"

/-- Answer one request: the session after it, and the answer. -/
def respond (s : Session) (r : Request) : Session × Response :=
  match handle s r with
  | .ok (s', save) =>
      (s', { id := r.id, ok := true, error := "", state := stateView s',
             save := save.getD "" })
  | .error e =>
      (s, { id := r.id, ok := false, error := e, state := stateView s, save := "" })

/-- Answer one line of the protocol: a request as JSON in, an answer as a
single line of JSON out. A line that is not a request is itself answered, with
the session unchanged, so that a client never waits for an answer that will not
come. -/
def respondText (s : Session) (line : String) : Session × String :=
  let j := do Request.ofJson (← Json.parse line)
  match j with
  | .ok r =>
      let (s', resp) := respond s r
      (s', (toJson resp).compress)
  | .error e =>
      let resp : Response :=
        { id := 0, ok := false, error := s!"this is not a request: {e}",
          state := stateView s, save := "" }
      (s, (toJson resp).compress)

end Api
end Netty
