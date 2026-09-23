import Lean
import Netty.Law

/-!
# The law lists the kernel ships with

Netty's law lists are plain text files, created and edited like any other. The
boolean list — the "Binary" laws of aPToP §11.3.1 — lives in
`Netty/laws/boolean.laws`, and is the file a user would copy to start their own.

That file is also the *definition* of `Netty.Laws.boolean`: the elaborator
`lawFile%` reads it, parses it with `Netty.Parser.lawFile`, and emits the
resulting `List Law` as a literal. So there is one text of the laws, not two,
and the list is ordinary data that Lean can compute with — which is what lets
`boolean_isTautology` below check, by evaluation in the kernel, that every law
the tool ships with is true under every boolean assignment to its variables.

A law file that fails to parse is a compile error, so a malformed law cannot
reach a user. (Lean does not track the `.laws` file as a build dependency; run
`lake build --rebuild Netty.Laws` after editing it, or just touch this file.)
-/

namespace Netty

namespace Quoting

/-- Quote a `BinOp` as a term. -/
private def binOp : BinOp → Lean.Ident
  | .and => Lean.mkCIdent ``BinOp.and
  | .or => Lean.mkCIdent ``BinOp.or
  | .imp => Lean.mkCIdent ``BinOp.imp
  | .rimp => Lean.mkCIdent ``BinOp.rimp
  | .eq => Lean.mkCIdent ``BinOp.eq
  | .ne => Lean.mkCIdent ``BinOp.ne
  | .lt => Lean.mkCIdent ``BinOp.lt
  | .gt => Lean.mkCIdent ``BinOp.gt
  | .le => Lean.mkCIdent ``BinOp.le
  | .ge => Lean.mkCIdent ``BinOp.ge
  | .add => Lean.mkCIdent ``BinOp.add
  | .sub => Lean.mkCIdent ``BinOp.sub
  | .mul => Lean.mkCIdent ``BinOp.mul

/-- Quote an expression as a term. -/
private def expr : Expr → Lean.Term
  | .var n => Lean.Syntax.mkCApp ``Expr.var #[Lean.quote n]
  | .num n => Lean.Syntax.mkCApp ``Expr.num #[Lean.quote n]
  | .mvar n => Lean.Syntax.mkCApp ``Expr.mvar #[Lean.quote n]
  | .top => Lean.mkCIdent ``Expr.top
  | .bot => Lean.mkCIdent ``Expr.bot
  | .neg a => Lean.Syntax.mkCApp ``Expr.neg #[expr a]
  | .bin o l r => Lean.Syntax.mkCApp ``Expr.bin #[binOp o, expr l, expr r]

/-- Quote a law as a term. -/
def lawTerm (l : Law) : Lean.Term :=
  Lean.Syntax.mkCApp ``Law.mk #[Lean.quote l.name, Lean.quote l.vars, expr l.stmt]

end Quoting

open Lean Elab Term in
/-- `lawFile% "path"` reads a law file relative to the Lean source file it
appears in, parses it at elaboration time, and elaborates to the resulting
`List Law`. -/
elab "lawFile% " p:str : term => do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD (System.FilePath.mk ".")
  let path := dir / p.getString
  let text ← IO.FS.readFile path
  match Netty.Parser.lawFile text with
  | .error e => throwError s!"{path}: {e}"
  | .ok ls =>
      let terms := (ls.map Netty.Quoting.lawTerm).toArray
      elabTerm (← `([$terms,*])) none

namespace Laws

/-- The boolean law list: the "Binary" laws of aPToP §11.3.1. -/
def boolean : List Law := lawFile% "laws/boolean.laws"

end Laws

set_option maxRecDepth 4000 in
/-- Every law the kernel ships with is a boolean tautology: it evaluates to
`⊤` under every assignment of `⊤`/`⊥` to its variables. Checked by evaluation
in Lean's kernel, so a law file line that is merely plausible cannot slip in.

This is the kernel's justification for offering a law as a suggestion. It does
not yet say that *applying* a law is sound — that a step licensed by matching
preserves the relation the margin claims — which is the next theorem to have. -/
theorem boolean_isTautology : Laws.boolean.all Law.isTautology = true := by decide
end Netty
