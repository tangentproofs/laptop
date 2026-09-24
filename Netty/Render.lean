import Netty.Doc

/-!
# The three panes, in text

Netty's calculation window is three panes: the proof, the laws the context
supplies, and the suggestions for the next line. A headless kernel still has
all three; it prints them instead of drawing them.

The proof pane follows the document's layout. The direction of a level stands
in a box on the level's first line, later lines carry their connective, and the
name of the law that produced a line is written at the end of the line
*before* it — so a name reads as "and now, by this law, …". A warning sign `!`
takes the place of the name where there is a logical gap; the suggestions pane
says of a step that would leave one what it would leave to prove. Subproofs are
indented instead of being drawn with the document's corner brackets, and the
focus is marked in the gutter.

The lines it draws are `Doc.shownLines`, the document after the display
collapses, so a subproof that is a single law application is drawn as its
parent line with the law's name at the end of it, and two zoom-ins matched by
two zoom-outs are drawn as one zoom step.
-/

namespace Netty

/-- Pad on the right to at least `n` characters. -/
private def padTo (n : Nat) (s : String) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- Pad on the left to at least `n` characters. -/
private def padLeft (n : Nat) (s : String) : String :=
  String.ofList (List.replicate (n - s.length) ' ') ++ s

/-- Drop trailing spaces. -/
private def dropTrailingSpaces (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (· == ' ')).reverse

namespace Doc

/-- The proof pane, as the display collapses leave it (`Doc.shownLines`): a
line that a collapse hides is not printed, a line the merge of two zooms lifts
is indented one level less, and a law's name folded up from a subproof stands
at the end of the line it was folded into. The number in the gutter is always
the line's own index in the document, which is what the script language calls
it. -/
def renderProof (d : Doc) : String :=
  if d.lines.isEmpty then "(no proof yet)" else
  let shown := d.shownLines
  let cell := fun (s : Shown) =>
    let l := d.lines[s.index]!
    let margin :=
      match l.conn, l.ty, l.dir with
      | some o, _, _ => "  " ++ o.symbol ++ " "
      | none, some ty, some dir => " [" ++ dir.symbol ty ++ "]"
      | none, _, _ => "    "
    String.ofList (List.replicate (2 * s.depth) ' ') ++ margin ++ " " ++ l.expr.render
  let width := (shown.map (fun s => (cell s).length)).foldl Nat.max 0
  String.intercalate "\n" <| shown.map fun s =>
    let mark := if s.index == d.focus && !d.stack.isEmpty then ">" else " "
    let row := mark ++ padLeft 4 (toString s.index) ++ "  " ++ padTo width (cell s)
    if s.note.isEmpty then dropTrailingSpaces row else row ++ "   " ++ s.note

/-- The context pane: the laws the zoom stack has added, innermost level
first. -/
def renderContext (d : Doc) : String :=
  match d.contextLaws with
  | [] => "(no context)"
  | ls => String.intercalate "\n" (ls.map fun l => "  " ++ l.stmt.render)

/-- The suggestions pane: what each applicable law would write next, with what
the match left unconstrained and — for a conditional law whose premise the laws
in force did not settle — what taking the step would leave to prove. A row that
names a premise is a row that leaves the document's warning sign, and says so
before it is taken. -/
def renderSuggestions (d : Doc) : String :=
  match d.suggestions with
  | [] => "(no suggestions)"
  | ss =>
      let width := (ss.map fun s => (s.op.symbol ++ " " ++ s.result.render).length).foldl Nat.max 0
      String.intercalate "\n" <| (List.range ss.length).map fun i =>
        let s := ss[i]!
        let body := padTo width (s.op.symbol ++ " " ++ s.result.render)
        let holes :=
          if s.holes.isEmpty then ""
          else "   (" ++ String.intercalate ", " s.holes ++ " unconstrained)"
        let premise :=
          match s.premise with
          | some q => "   (leaves a gap: " ++ q.render ++ ")"
          | none => ""
        padLeft 4 (toString i) ++ "  " ++ body ++ "   " ++ s.law ++ holes ++ premise

/-- What the proof proves, or why it does not prove anything yet. -/
def renderOutcome (d : Doc) : String :=
  match d.outcome with
  | .error e => "not proved: " ++ e
  | .ok o =>
      let rel := "proves " ++ o.top.render ++ " " ++ o.rel.symbol ++ " " ++ o.bottom.render
      if o.proved == Expr.bin o.rel o.top o.bottom then rel
      else rel ++ ", that is, proves " ++ o.proved.render

end Doc
end Netty
