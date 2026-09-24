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

A law of the form `Q ⇒ P` or `P ⇐ Q` has one more reading, the *conditional* one
(`Law.conditional`), where it is `P` and not the implication that stands in the
margin, with `Q` left over as a premise. `x ≤ x + y ⇐ 0 ≤ y` is a step a boolean
line can take as it is written — its main operator is `⇐` — and only this reading
makes it a step a *number* line can take, `≤` being a number direction. The
premise is not a new kind of obligation: `Doc.suggestions` asks whether the laws
in force settle it (`Law.settles`), and if they do not, taking the step leaves the
same gap direct entry leaves, with the premise recorded as what would close it.

## Matching

Matching is one-way: law variables (`Expr.mvar`) are the only things that bind,
so a law about `a` and a proof about `a` cannot capture one another.

It is *modulo associativity, symmetry and the identity element* — the three
things the document says a user need not write an associative, symmetry or
identity law to get. The document says that clicking any operand of `a + b + c`
zooms in to it, with no need of associative laws; applying a law reads a line
the same way.

**Associativity.** When the pattern is an association of an associative
operator, both it and the line are flattened (`Expr.flattenOp`) and the line's
operands are shared out among the pattern's, each group rebuilt left-associated
(`Expr.rebuildOp`). So `a ∧ b ⇒ a` sees `x ∧ y ∧ z` as `x ∧ (y ∧ z)` as readily
as `(x ∧ y) ∧ z`. A pattern operand that is not a law variable can only take one
operand: the pattern was flattened too, so no operand of it is an association of
that same operator, and an association is all a longer group can be.

**Symmetry.** For an operator the document declares symmetric (`BinOp.comm`:
`∧ ∨ = ⧧` and `+ ×`), the group a pattern operand takes need not be contiguous:
`Expr.shares` offers every sub-list of what is left, each keeping the line's own
order inside it. So `a ∧ b ⇒ a` reads `x ∧ y ∧ z` as `y ∧ (x ∧ z)` and offers
`y`, and `x ∧ y` matches `y ∧ x`. A symmetric operator that is *not* an
association — `=` and `⧧` — is matched by trying its two operands both ways
round instead.

**The identity element.** For an operator the document names a unit for
(`BinOp.identity`: `⊤` for `∧`, `⊥` for `∨`, `0` for `+`, `1` for `×`), a
pattern operand that *is* that unit may take no operands at all, so a law
written `x + 0` reads the line `n`; and a unit the line writes may be struck out
of it (`Expr.lineForms`), so `a ∧ a` reads `x ∧ ⊤ ∧ x`. Only a pattern operand
that is literally the unit may take nothing — a law variable never quietly binds
to a unit the line does not mention, which is what keeps `a ∧ b ⇒ a` from
matching every line there is.

Readings that need no rearrangement are offered first: `Expr.shares` puts the
contiguous prefixes, shortest first, before the sub-lists that only symmetry
allows. A match can succeed in many ways, so `Expr.matchAll` returns every one
of them — deduplicated, since symmetry and the identity can reach the same
substitution by more than one route — and the suggestion pane shows one
suggestion for each.

None of this is a new *step*: a law is still applied by matching a line and
writing the variant's right side, and the line and the matched left side differ
only by an associativity, a symmetry or a unit, all of which are equalities. So
no soundness argument is added — which is what `netty --selftest` checks by
evaluation, every suggestion the whole law list offers for a battery of lines
having to be a true step.

The recursion is bounded by fuel rather than by a well-founded measure, and the
fuel is the pattern's size. One unit is spent per level of the pattern — every
recursive call is on an operand of the pattern, whose height is one less — and
an expression's height is at most its size, so the fuel cannot run out. Fuel is
what keeps the matcher *structurally* recursive, and that is what lets `decide`
run a whole proof session inside Lean's kernel in `Netty.Replay`. A line that is
not an association of the pattern's operator at all is rejected before any of
the sharing out begins, unless the pattern mentions that operator's unit, so the
common case costs what it always did.

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
  /-- What must hold for the step to be licensed, for a *conditional* reading of
  a law (`Law.conditional`); `none` for the readings that need nothing. -/
  premise : Option Expr := none
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

/-- Match one operand of the pattern against the operands of the line it has
been given, using `m` when it is given exactly one.

Several operands are an association of `op`, and the pattern's operands were
flattened, so none of them is one: only a law variable can take them. *No*
operand is `op`'s identity element, where the document names one — that is
matching modulo identity, and it is how a law that mentions `⊤` in `a ∧ ⊤`
reads a line that left it out. Only a pattern operand that *is* the identity may
take none, so a law variable never quietly binds to a unit the line does not
mention. -/
def matchSegment (m : Expr → Expr → Subst → List Subst) (op : BinOp)
    (p : Expr) (es : List Expr) (σ : Subst) : List Subst :=
  match es with
  | [] =>
      match op.identity with
      | some u => if p == u then [σ] else []
      | none => []
  | [e] => m p e σ
  | _ =>
      match p, rebuildOp op es with
      | mvar n, some e => bindMVar n e σ
      | _, _ => []

/-- Every sub-list of `es`, paired with what is left over, both keeping the
line's own order. -/
def subLists : List Expr → List (List Expr × List Expr)
  | [] => [([], [])]
  | e :: rest => (subLists rest).flatMap fun (c, r) => [(e :: c, r), (c, e :: r)]

/-- The ways of giving one pattern operand some of the line's operands, with
the rest left over, in the order they are offered.

The contiguous *prefixes* come first, shortest first: those are the readings
associativity alone gives, and a reading that needs no rearrangement is always
offered before one that does. When the operator is symmetric every other
sub-list follows, each keeping the line's own order inside it — that is matching
modulo symmetry, and it is why `a ∧ b ⇒ a` can read `x ∧ y ∧ z` as `y ∧ (x ∧ z)`
and so offer `y`. -/
def shares (comm : Bool) (es : List Expr) : List (List Expr × List Expr) :=
  let pres := (List.range (es.length + 1)).map fun k => (es.take k, es.drop k)
  if comm then pres ++ (subLists es).filter (fun s => !pres.contains s) else pres

/-- Match the pattern's operands against the line's, each pattern operand
taking some of them and `one` matching it against those. The recursion is on the
pattern's operands, which is why `one` is a parameter: `matchFuel`'s own
recursion is on its fuel. -/
def matchSegments (comm : Bool) (one : Expr → List Expr → Subst → List Subst) :
    List Expr → List Expr → Subst → List Subst
  | [], es, σ => if es.isEmpty then [σ] else []
  | [p], es, σ => one p es σ
  | p :: ps, es, σ =>
      (shares comm es).flatMap fun (mine, rest) =>
        (one p mine σ).flatMap fun σ' => matchSegments comm one ps rest σ'

/-- The readings of the line `e` as operands of `o`: the flattening, and — when
`o` has an identity element that the line actually writes — the flattening with
those operands struck out. Striking them out is matching modulo identity from
the line's side, so `a ∧ a` reads `x ∧ ⊤ ∧ x`. A line that is nothing but units
is left alone, since striking them all out would leave no line. -/
def lineForms (o : BinOp) (e : Expr) : List (List Expr) :=
  let es := flattenOp o e
  match o.identity with
  | some u =>
      let kept := es.filter (· != u)
      if kept.isEmpty || kept.length == es.length then [es] else [es, kept]
  | none => [es]

/-- Every way of matching the pattern `pat` against `e`, extending `σ`. Only
`mvar` binds; an association is matched modulo associativity, symmetry and the
identity element, following what the document declares of each operator. The
fuel is spent one unit per level of the pattern. -/
def matchFuel : Nat → Expr → Expr → Subst → List Subst
  | 0, _, _, _ => []
  | _ + 1, mvar n, e, σ => bindMVar n e σ
  | _ + 1, var n, var m, σ => if n == m then [σ] else []
  | _ + 1, num n, num m, σ => if n == m then [σ] else []
  | _ + 1, top, top, σ => [σ]
  | _ + 1, bot, bot, σ => [σ]
  | f + 1, neg a, neg b, σ => matchFuel f a b σ
  | f + 1, bin o l r, e, σ =>
      if o.assoc || o.identity.isSome then
        let es := flattenOp o e
        let ps := flattenOp o (bin o l r)
        -- `es` is one operand exactly when the line is not an association of
        -- `o` at all. The pattern has at least two, so all but one of them
        -- would have to take nothing, which only `o`'s own identity may do.
        if es.length == 1 && !ps.any (fun p => o.identity == some p) then []
        else
          (lineForms o e).flatMap fun line =>
            matchSegments o.comm (matchSegment (matchFuel f) o) ps line σ
      else
        match e with
        | bin o' l' r' =>
            if o != o' then []
            else
              (matchFuel f l l' σ).flatMap (fun σ' => matchFuel f r r' σ') ++
                (if o.comm then
                   (matchFuel f l r' σ).flatMap fun σ' => matchFuel f r l' σ'
                 else [])
        | _ => []
  | _ + 1, _, _, _ => []

/-- Keep the first occurrence of each substitution: symmetry and the identity
can find one and the same match by more than one route. -/
def dedupSubst (σs : List Subst) : List Subst :=
  (σs.foldl (fun acc σ => if acc.contains σ then acc else σ :: acc) []).reverse

/-- Every way of matching the pattern `pat` against `e`, extending `σ`. -/
def matchAll (pat e : Expr) (σ : Subst) : List Subst :=
  dedupSubst (matchFuel pat.size pat e σ)

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

/-- The *conditional* readings of a law.

A law of the form `Q ⇒ P` or `P ⇐ Q` whose consequent `P` is itself a relation
that can stand in a left margin gives a step in *that* margin, with `Q` left over
as a premise. So `x ≤ x + y ⇐ 0 ≤ y` lets a number line `x + y` be written `x`
with `≥` in the margin, and a number line `x` be written `x + y` with `≤`,
provided `0 ≤ y`. Its unconditional readings put its own main operator — `⇐`, a
*boolean* connective — in the margin, so without this reading the law is not a
step a number calculation can take at all.

Both directions of the consequent are offered, as `Law.forms` offers both
directions of a law: `a op b` is `b op.flip a`, and a premise that licenses the
one licenses the other.

The reading is generated only where the consequent's connective is one of the
*number* directions, `≤ < ≥ >`. That is where a law is otherwise unusable: a
boolean conditional law is already a step a boolean line can take, its own main
operator `⇒` standing in a boolean margin, so reading it conditionally as well
would offer every such law a second time with a premise attached and bury the
steps that need nothing. `=` belongs to both types and is left out for the same
reason. Reading a boolean conditional law conditionally — which would let
`(a ⇒ b) ⇒ (a ∧ c ⇒ b ∧ c)` rewrite `a ∧ c` to `b ∧ c` under the premise
`a ⇒ b` — is a later round's work, and the ranking key it needs is already
here.

The premise is not a new kind of obligation. `Doc.suggestions` instantiates it
along with the rest of the reading and asks whether the laws in force settle it
(`Law.settles`); if they do, the step is an ordinary step, and if they do not, it
is a step with a gap — the document's warning sign, the same one direct entry
leaves. Nothing is claimed that has not been justified. -/
def conditional (l : Law) : List Variant :=
  let name := if l.name.isEmpty then "unnamed law" else l.name
  -- The number directions: the margin connectives that belong to the number type
  -- and cannot stand in a boolean margin.
  let numberDir : BinOp → Bool := fun o =>
    match o with | .le | .lt | .ge | .gt => true | _ => false
  match l.stmt with
  | .bin .imp q (.bin o a b) | .bin .rimp (.bin o a b) q =>
      if numberDir o then
        { law := name, lhs := a, op := o, rhs := b, premise := some q } ::
          (match o.flip with
           | some f => [{ law := name, lhs := b, op := f, rhs := a, premise := some q }]
           | none => [])
      else []
  | _ => []

/-- The variants of a law: its forms that are already directions, plus each
form with `= ⊤` appended and with `⊤ =` prepended. -/
def variants (l : Law) : List Variant :=
  -- "Laws are not required to have names; any law without a name is labelled
  -- ‘unnamed law’."
  let name := if l.name.isEmpty then "unnamed law" else l.name
  let direct := l.forms.filterMap fun s =>
    match s with
    | .bin o a b =>
        if o.isMargin then some ({ law := name, lhs := a, op := o, rhs := b } : Variant)
        else none
    | _ => none
  let tops := l.forms.flatMap fun s =>
    [({ law := name, lhs := s, op := .eq, rhs := .top } : Variant),
     { law := name, lhs := .top, op := .eq, rhs := s }]
  -- The conditional readings come last, so that when a law can write one and the
  -- same line both with a premise and without, `Doc.suggestions` keeps the one
  -- that needs nothing.
  direct ++ tops ++ l.conditional

/-- Whether the laws in force settle `q` outright: whether one of them has an
unconditional reading that reads `q` and writes `⊤`.

That is the same match the suggestion pane would make on a line holding `q`, so a
premise is discharged exactly when the tool would have offered to write `⊤` for
it in one step — by a law of the list, or by a `context` law that zooming in put
in force, which is where a domain condition such as `0 ≤ y` comes from. One step,
and by an unconditional reading, so the question cannot recur. An unbound law
variable in the reading is no obstacle: the law holds for every instantiation, so
if `q` is an instance of a side that the law equates with `⊤`, `q` is `⊤`. -/
def settles (laws : List Law) (q : Expr) : Bool :=
  laws.any fun l => l.variants.any fun v =>
    v.premise.isNone && v.rhs == .top && (v.op == .eq || v.op == .rimp)
      && !(Expr.matchAll v.lhs q []).isEmpty

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

/-- Every assignment of the given integers to the given names. -/
def intAssignments (vals : List Int) : List String → List (List (String × Int))
  | [] => [[]]
  | n :: ns => (intAssignments vals ns).flatMap fun σ => vals.map fun v => (n, v) :: σ

/-- Whether the law holds under every assignment of `vals` to its variables and
identifiers, read as integers.

This is a *test*, not a decision procedure: a law that is false in general can
hold on a small range of integers, where `Law.isTautology` really settles a
boolean law. It is what the kernel can check about a number law without doing
arithmetic, which is out of scope here, and it is offered as evidence and not as
a proof. Laws with more than four names are not checked. -/
def holdsOnInts (vals : List Int) (l : Law) : Bool :=
  let names := l.stmt.mvars ++ l.stmt.vars
  names.length ≤ 4 &&
    (intAssignments vals names).all fun σ => l.stmt.evalProp σ == some true

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
