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
  | .mem => Lean.mkCIdent ``BinOp.mem

/-- Quote a `Quant` as a term. -/
private def quant : Quant → Lean.Ident
  | .all => Lean.mkCIdent ``Quant.all
  | .ex => Lean.mkCIdent ``Quant.ex

/-- Quote an expression as a term. -/
private def expr : Expr → Lean.Term
  | .var n => Lean.Syntax.mkCApp ``Expr.var #[Lean.quote n]
  | .num n => Lean.Syntax.mkCApp ``Expr.num #[Lean.quote n]
  | .mvar n => Lean.Syntax.mkCApp ``Expr.mvar #[Lean.quote n]
  | .top => Lean.mkCIdent ``Expr.top
  | .bot => Lean.mkCIdent ``Expr.bot
  | .neg a => Lean.Syntax.mkCApp ``Expr.neg #[expr a]
  | .bin o l r => Lean.Syntax.mkCApp ``Expr.bin #[binOp o, expr l, expr r]
  | .cond c x y => Lean.Syntax.mkCApp ``Expr.cond #[expr c, expr x, expr y]
  | .quant k ids d b =>
      Lean.Syntax.mkCApp ``Expr.quant #[quant k, Lean.quote ids, expr d, expr b]

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

/-- The quantifier law list, `Netty/laws/quantifier.laws`: `∀` and `∃` with an
explicit domain.

It is a list of its own and not part of `boolean`, for two reasons. The suggestion
pane computes every reading of every law in force for every place of a line, so a
law a user is not quantifying over is a cost on every step they take; and — see
`quantifier_isBeyondTheBooleanEvaluator` — these laws are not checked the way the
boolean ones are, which a reader should not have to untangle from a list that is. -/
def quantifier : List Law := lawFile% "laws/quantifier.laws"

/-- A small number law list, `Netty/laws/number.laws`. It is not the whole of
§11.3.2 and does not pretend to be: it exists so that the conditional readings of
a law (`Law.conditional`) have something to work with at the number level, and so
that a user has a number law file to copy. -/
def number : List Law := lawFile% "laws/number.laws"

end Laws

set_option maxRecDepth 4000 in
/-- Every law the kernel ships with is a boolean tautology: it evaluates to
`⊤` under every assignment of `⊤`/`⊥` to its variables. Checked by evaluation
in Lean's kernel, so a law file line that is merely plausible cannot slip in.

This is the kernel's justification for offering a law as a suggestion. It does
not yet say that *applying* a law is sound — that a step licensed by matching
preserves the relation the margin claims — which is the next theorem to have. -/
theorem boolean_isTautology : Laws.boolean.all Law.isTautology = true := by decide

set_option maxRecDepth 100000 in
/-- Every number law the kernel ships with holds under every assignment of
`-2 … 2` to its variables, checked by evaluation in the kernel.

This is weaker than `boolean_isTautology` and the difference matters: a boolean
law has finitely many assignments, so checking them all *decides* the law, while
a number law has infinitely many and a false law can hold on a small range. It is
evidence, not a proof, and it is the most the kernel can say without arithmetic,
which is out of scope here. The number laws are therefore trusted as
transcribed, and this checks that none of them is wrong in a way that shows up on
small integers. -/
theorem number_holdsOnInts :
    Laws.number.all (Law.holdsOnInts [-2, -1, 0, 1, 2]) = true := by decide

/-- Not one of the quantifier laws is checked, and this is the line that says so.

`Expr.evalBool` returns `none` on a quantifier, because an assignment of `⊤`/`⊥`
to names cannot decide one: what `∀x: d· b` says depends on the bunch `d`, and the
kernel has no theory of bunches. `Law.isTautology` is therefore `false` on every
law of the list — not because any of them is false, but because the evaluator
cannot reach them. They are transcribed from aPToP and trusted, which is weaker
than `number_holdsOnInts`, itself weaker than `boolean_isTautology`.

Stating it as a theorem is not a virtue claimed; it is the hole, pinned down. If a
later commit gives the evaluator a finite domain to work with, this theorem breaks
and has to be replaced by a real check, which is the point of writing it this way
round. -/
theorem quantifier_isBeyondTheBooleanEvaluator :
    Laws.quantifier.all (fun l => !l.isTautology) = true := by decide

/-- What *can* be checked of the quantifier laws mechanically: each of them is a
law the kernel can read as a step — its main operator can stand in a left margin —
and each of them declares exactly the law variables it uses, so no identifier of
one is a stray, and no name a quantifier binds has leaked into the list of law
variables. That last is what would break: a bound name treated as a law variable
would unify with anything at all. -/
theorem quantifier_wellFormed :
    Laws.quantifier.all (fun l =>
      (match l.stmt with | .bin o _ _ => o.isMargin | _ => false)
        && l.vars == l.stmt.mvars && l.stmt.vars.isEmpty) = true := by decide
end Netty
