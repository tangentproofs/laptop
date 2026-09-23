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
takes the place of the name where there is a logical gap. Subproofs are
indented instead of being drawn with the document's corner brackets, and the
focus is marked in the gutter.
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

/-- The name to write at the end of line `i`: the law that justifies the step
to the next line at the same level, or a warning sign where there is a gap. -/
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

/-- The proof pane. -/
def renderProof (d : Doc) : String :=
  if d.lines.isEmpty then "(no proof yet)" else
  let idxs := List.range d.lines.size
  let cell := fun (i : Nat) =>
    let l := d.lines[i]!
    let margin :=
      match l.conn, l.ty, l.dir with
      | some o, _, _ => "  " ++ o.symbol ++ " "
      | none, some ty, some dir => " [" ++ dir.symbol ty ++ "]"
      | none, _, _ => "    "
    String.ofList (List.replicate (2 * l.depth) ' ') ++ margin ++ " " ++ l.expr.render
  let width := (idxs.map (fun i => (cell i).length)).foldl Nat.max 0
  String.intercalate "\n" <| idxs.map fun i =>
    let mark := if i == d.focus && !d.stack.isEmpty then ">" else " "
    let row := mark ++ padLeft 4 (toString i) ++ "  " ++ padTo width (cell i)
    let n := d.note i
    if n.isEmpty then dropTrailingSpaces row else row ++ "   " ++ n

/-- The context pane: the laws the zoom stack has added, innermost level
first. -/
def renderContext (d : Doc) : String :=
  match d.contextLaws with
  | [] => "(no context)"
  | ls => String.intercalate "\n" (ls.map fun l => "  " ++ l.stmt.render)

/-- The suggestions pane: what each applicable law would write next. -/
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
        padLeft 4 (toString i) ++ "  " ++ body ++ "   " ++ s.law ++ holes

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
