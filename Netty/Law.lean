import Netty.Parser

/-!
# Laws, their variants, and matching

A *law* is an optional name and a boolean expression, exactly as the Netty
document describes a line of a law file. The expression's identifiers are
universally quantified: the document notes that the law written `a ∧ b ⇒ a` is
really `∀a, b: bool· a ∧ b ⇒ a`, and that its application is what unification
with the line before the focus decides. A law file line may make that
quantifier explicit (`∀a, b· a ∧ b ⇒ a`); otherwise every identifier of the
line is taken to be quantified. A law with *no* quantified variables is a
ground fact about particular identifiers — that is what the laws in the
context pane are.

## Variants

The document: "For each law, there are potentially six variants. If the main
operator can appear in the left margin of a proof, then the reversed law is a
variant … And any law has a variant with `=T` appended and another with `T=`
prepended." So `a ∧ b ⇒ a` has the six variants

```
a ∧ b ⇒ a        a ⇐ a ∧ b
(a ∧ b ⇒ a) = ⊤  (a ⇐ a ∧ b) = ⊤
⊤ = (a ∧ b ⇒ a)  ⊤ = (a ⇐ a ∧ b)
```

and a law whose main operator cannot appear in the margin has only the two
`⊤` variants. A variant is a triple `lhs op rhs` with `op` a direction; the
line before the focus is matched against `lhs`, and `rhs` under the resulting
substitution is what the suggestion offers.

## Matching

Matching is one-way: law variables (`Expr.mvar`) are the only things that bind,
so a law about `a` and a proof about `a` cannot capture one another.

It is *modulo associativity*. The document says that clicking any operand of
`a + b + c` zooms in to it, with no need of associative laws; applying a law
reads a line the same way, so the law `a ∧ b ⇒ a` sees `x ∧ y ∧ z` as
`x ∧ (y ∧ z)` as readily as `(x ∧ y) ∧ z`. When a pattern and a line are
associations of the same associative operator, both are flattened
(`Expr.flattenOp`), and every way of cutting the line's operands into as many
non-empty *contiguous* segments as the pattern has operands is tried, each
segment rebuilt left-associated (`Expr.rebuildOp`). A pattern operand that is
not a law variable can only take a segment of one operand: the pattern was
flattened too, so no operand of it is an association of that same operator,
and an association is all a longer segment can be.

A match can therefore succeed in more than one way — `a ∧ b ⇒ a` applied to
`x ∧ y ∧ z` offers `x` and `x ∧ y`, where before it offered only `x ∧ y` —
so `Expr.matchAll` returns every way, shortest first segment first, and the
suggestion pane shows one suggestion for each. Nothing else about matching has
changed: it is not modulo symmetry, so `x ∧ y` does not match `y ∧ x`, and it
is not modulo the identity element.

The recursion is bounded by fuel rather than by a well-founded measure, and the
fuel is the pattern's size. One unit is spent per level of the pattern — every
recursive call is on an operand of the pattern, whose height is one less — and
an expression's height is at most its size, so the fuel cannot run out. Fuel is
what keeps the matcher *structurally* recursive, and that is what lets `decide`
run a whole proof session inside Lean's kernel in `Netty.Replay`.

## Soundness

`Law.isTautology` decides whether a law with at most eight variables is true
under every boolean assignment. It is what `Netty.Laws` uses to check, inside
Lean, that every law the kernel ships with really is a law.
-/

namespace Netty

/-- A law: an optional name, its universally quantified variables, and its
statement, in which those variables appear as `Expr.mvar`. -/
structure Law where
  /-- The law's name; `""` when the law file gave none. -/
  name : String := ""
  /-- The universally quantified variables. -/
  vars : List String := []
  /-- The statement, with `vars` appearing as `Expr.mvar`. -/
  stmt : Expr
  deriving Repr, DecidableEq, Inhabited

/-- One of the (at most six) ways a law can be read as a proof step: match a
line against `lhs`, and the next line is `rhs` joined by the direction `op`. -/
structure Variant where
  /-- The name of the law this variant comes from. -/
  law : String
  /-- What the line before the focus must match. -/
  lhs : Expr
  /-- The connective that will stand in the left margin. -/
  op : BinOp
  /-- What the next line will be. -/
  rhs : Expr
  deriving Repr, DecidableEq, Inhabited

/-- A binding of law variables to expressions. -/
abbrev Subst := List (String × Expr)

namespace Expr

/-- Bind a law variable to an expression, if that agrees with what it is bound
to already. -/
def bindMVar (n : String) (e : Expr) (σ : Subst) : List Subst :=
  match σ.lookup n with
  | some e' => if e' == e then [σ] else []
  | none => [(n, e) :: σ]

/-- Match one operand of the pattern against one non-empty contiguous segment
of the line's operands, using `m` for a segment of length one.

A longer segment is an association of `op`, and the pattern's operands were
flattened, so none of them is one: only a law variable can take it. -/
def matchSegment (m : Expr → Expr → Subst → List Subst) (op : BinOp)
    (p : Expr) (es : List Expr) (σ : Subst) : List Subst :=
  match es with
  | [e] => m p e σ
  | _ =>
      match p, rebuildOp op es with
      | mvar n, some e => bindMVar n e σ
      | _, _ => []

/-- Match the pattern's operands against the line's, each pattern operand
taking a non-empty contiguous segment and `one` matching it against that
segment. The recursion is on the pattern's operands, which is why `one` is a
parameter: `matchFuel`'s own recursion is on its fuel. -/
def matchSegments (one : Expr → List Expr → Subst → List Subst) :
    List Expr → List Expr → Subst → List Subst
  | [], [], σ => [σ]
  | [], _ :: _, _ => []
  | _ :: _, [], _ => []
  | [p], es, σ => one p es σ
  | p :: ps, e :: es, σ =>
      -- `p` takes `e` and `k` of the operands after it; what is left must
      -- still give each remaining pattern operand an operand of its own.
      (List.range (es.length + 1 - ps.length)).flatMap fun k =>
        (one p (e :: es.take k) σ).flatMap fun σ' =>
          matchSegments one ps (es.drop k) σ'

/-- Every way of matching the pattern `pat` against `e`, extending `σ`. Only
`mvar` binds, and an association of an associative operator is matched modulo
associativity. The fuel is spent one unit per level of the pattern. -/
def matchFuel : Nat → Expr → Expr → Subst → List Subst
  | 0, _, _, _ => []
  | _ + 1, mvar n, e, σ => bindMVar n e σ
  | _ + 1, var n, var m, σ => if n == m then [σ] else []
  | _ + 1, num n, num m, σ => if n == m then [σ] else []
  | _ + 1, top, top, σ => [σ]
  | _ + 1, bot, bot, σ => [σ]
  | f + 1, neg a, neg b, σ => matchFuel f a b σ
  | f + 1, bin o l r, bin o' l' r', σ =>
      if o != o' then []
      else if o.assoc then
        matchSegments (matchSegment (matchFuel f) o)
          (flattenOp o (bin o l r)) (flattenOp o (bin o' l' r')) σ
      else (matchFuel f l l' σ).flatMap fun σ' => matchFuel f r r' σ'
  | _ + 1, _, _, _ => []

/-- Every way of matching the pattern `pat` against `e`, extending `σ`. -/
def matchAll (pat e : Expr) (σ : Subst) : List Subst := matchFuel pat.size pat e σ

/-- The first way of matching `pat` against `e`, when there is one. -/
def matchWith (pat e : Expr) (σ : Subst) : Option Subst := (matchAll pat e σ).head?

/-- Replace the law variables bound by `σ`; leave the rest alone. -/
def instantiate (σ : Subst) : Expr → Expr
  | mvar n => match σ.lookup n with | some e => e | none => mvar n
  | neg a => neg (instantiate σ a)
  | bin o l r => bin o (instantiate σ l) (instantiate σ r)
  | e => e

end Expr

namespace Law

/-- The law itself and, when its main operator is a direction, the law with
that direction reversed. -/
def forms (l : Law) : List Expr :=
  match l.stmt with
  | .bin o a b =>
      if o.isMargin then
        match o.flip with
        | some f => [l.stmt, .bin f b a]
        | none => [l.stmt]
      else [l.stmt]
  | _ => [l.stmt]

/-- The variants of a law: its forms that are already directions, plus each
form with `= ⊤` appended and with `⊤ =` prepended. -/
def variants (l : Law) : List Variant :=
  -- "Laws are not required to have names; any law without a name is labelled
  -- ‘unnamed law’."
  let name := if l.name.isEmpty then "unnamed law" else l.name
  let direct := l.forms.filterMap fun s =>
    match s with
    | .bin o a b => if o.isMargin then some ⟨name, a, o, b⟩ else none
    | _ => none
  let tops := l.forms.flatMap fun s =>
    [(⟨name, s, .eq, .top⟩ : Variant), ⟨name, .top, .eq, s⟩]
  direct ++ tops

/-- Every assignment of `true`/`false` to the given names. -/
def assignments : List String → List (List (String × Bool))
  | [] => [[]]
  | n :: ns => (assignments ns).flatMap fun σ => [(n, true) :: σ, (n, false) :: σ]

/-- Whether the law is true under every boolean assignment to its variables
and identifiers. Laws with more than eight names are not checked. -/
def isTautology (l : Law) : Bool :=
  let names := l.stmt.mvars ++ l.stmt.vars
  names.length ≤ 8 &&
    (assignments names).all fun σ => l.stmt.evalBool σ == some true

/-- The ground law that a zoom-in adds to the context. -/
def context (e : Expr) : Law := { name := "context", vars := [], stmt := e }

/-- Write the law back in law-file notation. The quantifier is printed only
when the default reading — every identifier of the line is quantified — would
not reproduce the law. -/
def render (l : Law) : String :=
  let needsQuantifier := l.vars != l.stmt.mvars || l.stmt.vars != []
  (if l.name.isEmpty then "" else l.name ++ ": ")
    ++ (if needsQuantifier then "∀" ++ String.intercalate ", " l.vars ++ "· " else "")
    ++ l.stmt.render

instance : ToString Law := ⟨render⟩

end Law

namespace Parser

/-- Read the law variables of an explicit `∀a, b·` prefix. -/
private def lawVars : List Tok → List String → Except String (List String × List Tok)
  | .dot :: rest, acc => .ok (acc.reverse, rest)
  | .ident n :: rest, acc => lawVars rest (n :: acc)
  | .comma :: rest, acc => lawVars rest acc
  | t :: _, _ => .error s!"unexpected ‘{t}’ among the law variables"
  | [], _ => .error "expected ‘·’ after the law variables"

/-- Parse the statement of a law: an optional `∀…·` prefix and an expression.
Without the prefix, every identifier of the expression is quantified. -/
def lawBody (s : String) : Except String (List String × Expr) := do
  let ts ← tokenize s
  match ts with
  | .univ :: rest =>
      let (names, body) ← lawVars rest []
      let e ← exprOfToks body
      .ok (names, e.generalize names)
  | _ =>
      let e ← exprOfToks ts
      let ns := e.vars
      .ok (ns, e.generalize ns)

/-- Parse one line of a law file. Blank lines and lines whose first
non-blank character is `#` are comments and yield nothing. A law's name is
whatever precedes the first `:`; the name may contain spaces. -/
def lawLine (s : String) : Except String (Option Law) := do
  let t := trim s
  if t.isEmpty || beginsWith t '#' then return none
  let (name, body) :=
    match t.splitOn ":" with
    | first :: rest@(_ :: _) => (trim first, String.intercalate ":" rest)
    | _ => ("", t)
  let (vars, stmt) ← lawBody body
  return some { name := name, vars := vars, stmt := stmt }

/-- Parse a whole law file. -/
def lawFile (text : String) : Except String (List Law) :=
  go 1 (text.splitOn "\n") []
where
  go : Nat → List String → List Law → Except String (List Law)
    | _, [], acc => .ok acc.reverse
    | n, line :: rest, acc =>
        match lawLine line with
        | .error e => .error s!"law file line {n}: {e}"
        | .ok none => go (n + 1) rest acc
        | .ok (some l) => go (n + 1) rest (l :: acc)

end Parser

/-- Write a list of laws back as the text of a law file. -/
def renderLawFile (laws : List Law) : String :=
  String.intercalate "\n" (laws.map Law.render) ++ "\n"

end Netty
