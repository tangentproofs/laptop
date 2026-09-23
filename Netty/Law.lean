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
so a law about `a` and a proof about `a` cannot capture one another. Matching
is syntactic, up to the left-associated reading of an associative operator; a
law `a ∧ b` matches `x ∧ y ∧ z` with `a := x ∧ y` and `b := z`, but not with
`a := x`. Matching modulo associativity is a later refinement.

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

/-- Match the pattern `pat` against `e`, extending `σ`. Only `mvar` binds. -/
def matchWith : Expr → Expr → Subst → Option Subst
  | mvar n, e, σ =>
      match σ.lookup n with
      | some e' => if e' == e then some σ else none
      | none => some ((n, e) :: σ)
  | var n, var m, σ => if n == m then some σ else none
  | num n, num m, σ => if n == m then some σ else none
  | top, top, σ => some σ
  | bot, bot, σ => some σ
  | neg a, neg b, σ => matchWith a b σ
  | bin o l r, bin o' l' r', σ =>
      if o == o' then (matchWith l l' σ).bind (fun σ' => matchWith r r' σ') else none
  | _, _, _ => none

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
