import Netty.Expr

/-!
# Programming notation: the rules the kernel computes

aPToP's programming notation is boolean expressions about a prestate `x, y, …`
and a poststate `x′, y′, …`. Four of its definitions cannot be written as a law
of a law file, because a law of a law file rewrites by matching and these
rewrite by *substitution*, or mention every state variable:

* **ok** — `ok = x′=x ∧ y′=y ∧ …`, read either way;
* **assignment** — `x:= e = x′=e ∧ y′=y ∧ …`;
* **sequential composition** — `P. Q = ∃x″, y″, …· P′ ∧ Q″` where `P′` is `P`
  with `x″, y″, …` for `x′, y′, …` and `Q″` is `Q` with `x″, y″, …` for
  `x, y, …`;
* **substitution law** — `x:= e. P = P` with `e` for `x`; over `nat`, when
  `e` may not be a natural number, `x:= e. P = e: nat ∧ P` with `e` for `x`,
  since the assignment then has no final state.

and one law of the quantifier theory needs substitution too:

* **one point** — `∃v: d· v = e ∧ b = e: d ∧ b` with `e` for `v`, when `v` does
  not appear in `e`;

and one that does not substitute but needs to know the domain is not empty:

* **vacuous quantifier** — `∃v: d· b = b` and `∀v: d· b = b` when `v` does not
  appear in `b`, for the domains `int`, `nat` and `bin`.

So these are *rules*: functions from the expression at a place of a line to the
expressions that may replace it, all of them equalities. A rule is offered by the
suggestion pane alongside the laws (`Doc.suggestions`) and cited by name in a
calculation file. Each needs the state the specifications are about, which a
calculation file declares (`state x, y: int`).

A specification may be given a name (`spec R = …`): the rule **definition of R**
replaces `R` by its body and its body by `R`.

## When substitution is allowed

Every rule here is stated in the book for specifications written without
programming notation, and that is the only place the kernel applies it. `x:= e`,
`P. Q` and `ok` mention state variables they do not write (`x:= e` says `y′=y`),
and so does a named specification, so substituting into an expression that holds
one of them would be wrong: the substitution law's `P` and sequential
composition's `P` and `Q` must be free of all of them (`Prog.isPlain`). A
calculation expands them first — by **assignment**, **ok**, or the definition of
a specification — which is how the book proceeds as well.
-/

namespace Netty

/-- The state a specification is about, and the specifications given names. -/
structure Prog where
  /-- The state variables, each with its domain (`int`, `nat`, `bin`, …). -/
  state : List (String × Expr) := []
  /-- The named specifications and their bodies. -/
  specs : List (String × Expr) := []
  deriving Repr, DecidableEq, Inhabited

/-- A rule the kernel computes. -/
inductive Rule
  /-- `ok`. -/ | ok
  /-- `x:= e`. -/ | assignment
  /-- `P. Q`. -/ | seq
  /-- `x:= e. P`. -/ | substitution
  /-- `∃v: d· v = e ∧ b`. -/ | onePoint
  /-- `∃v: d· b` with `v` not in `b`. -/ | vacuous
  /-- A named specification. -/ | definition (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- The name of a variable's final value. -/
def prime (n : String) : String := n ++ "′"

namespace Expr

/-- Whether a name occurs free. -/
def occurs (n : String) (e : Expr) : Bool := e.vars.contains n

/-- A name like `n` not in `avoid`: `n″`, `n‴`, then numbered. -/
def fresh (avoid : List String) (n : String) : String :=
  let cands := [n ++ "″", n ++ "‴"] ++ (List.range 50).map fun k => n ++ "″" ++ toString k
  (cands.find? fun c => !avoid.contains c).getD (n ++ "″?")

/-- Every name that occurs in `e`, free or bound. -/
def allNames : Expr → List String
  | var n => [n]
  | neg a => allNames a
  | bin _ l r => allNames l ++ allNames r
  | cond c x y => allNames c ++ allNames x ++ allNames y
  | quant _ ids d b => ids ++ allNames d ++ allNames b
  | _ => []

/-- Substitute expressions for free identifiers, renaming a quantifier's binder
when it would capture an identifier of what is substituted. The fuel is the
expression's size, which renaming a binder leaves alone. -/
def substFuel : Nat → List (String × Expr) → Expr → Expr
  | 0, _, e => e
  | _ + 1, σ, var n => (σ.lookup n).getD (var n)
  | f + 1, σ, neg a => neg (substFuel f σ a)
  | f + 1, σ, bin o l r => bin o (substFuel f σ l) (substFuel f σ r)
  | f + 1, σ, cond c x y => cond (substFuel f σ c) (substFuel f σ x) (substFuel f σ y)
  | f + 1, σ, quant k ids d b =>
      let σ' := σ.filter fun p => !ids.contains p.1
      let inside := σ'.flatMap fun p => p.2.vars
      let avoid := inside ++ b.allNames ++ ids
      -- A binder that would capture is renamed first.
      let ren := ids.filterMap fun i =>
        if inside.contains i then some (i, fresh avoid i) else none
      let ids' := ids.map fun i => (ren.lookup i).getD i
      let b' := if ren.isEmpty then b else renameVars ren b
      quant k ids' (substFuel f σ d) (substFuel f σ' b')
  | _, _, e => e

/-- Substitute expressions for free identifiers (`substFuel`). -/
def subst (σ : List (String × Expr)) (e : Expr) : Expr := substFuel e.size σ e

/-- The conjunction of a list, `⊤` when it is empty. -/
def conj : List Expr → Expr
  | [] => top
  | e :: es => es.foldl (fun acc x => bin .and acc x) e

/-- The conjuncts of an expression. -/
def conjuncts (e : Expr) : List Expr := flattenOp .and e

end Expr

namespace Prog

/-- Whether an expression is free of programming notation: no `:=`, no `.`,
no `ok`, no named specification. -/
def isPlain (p : Prog) : Expr → Bool
  | .var n => n != "ok" && !(p.specs.any (·.1 == n))
  | .neg a => p.isPlain a
  | .bin o l r => o != .assign && o != .seq && p.isPlain l && p.isPlain r
  | .cond c x y => p.isPlain c && p.isPlain x && p.isPlain y
  | .quant _ _ d b => p.isPlain d && p.isPlain b
  | _ => true

/-- The state variables and then their primes: the parameters of a named
specification. -/
def params (p : Prog) : List String :=
  p.state.map (·.1) ++ p.state.map (prime ·.1)

/-- Whether an expression is certainly an element of a domain: anything is an
`int` or a `bin`, as far as the kernel's expressions go, and a `nat` expression
built from numerals and `nat` state variables by `+` and `×` is a `nat`. -/
def staysIn (p : Prog) (d : Expr) (e : Expr) : Bool :=
  d != .var "nat" || natExpr e
where
  natExpr : Expr → Bool
    | .num _ => true
    | .var v => p.state.lookup v == some (.var "nat")
    | .bin .add a b | .bin .mul a b => natExpr a && natExpr b
    | _ => false

/-- `x′ = e` for `x`, `y′ = y` for every other state variable. -/
def assignBody (p : Prog) (x : String) (e : Expr) : Expr :=
  Expr.conj (p.state.map fun (y, _) =>
    if y == x then .bin .eq (.var (prime y)) e else .bin .eq (.var (prime y)) (.var y))

/-- `x′ = x ∧ y′ = y ∧ …`. -/
def okBody (p : Prog) : Expr :=
  Expr.conj (p.state.map fun (y, _) => .bin .eq (.var (prime y)) (.var y))

/-- `∃x″: X· ∃y″: Y· … P′ ∧ Q″`. -/
def seqBody (p : Prog) (a b : Expr) : Expr :=
  let avoid := a.allNames ++ b.allNames ++ p.state.map (·.1)
  let mids := p.state.map fun (y, d) => (y, d, Expr.fresh avoid y)
  let a' := a.subst (mids.map fun (y, _, m) => (prime y, .var m))
  let b' := b.subst (mids.map fun (y, _, m) => (y, .var m))
  mids.foldr (fun (_, d, m) acc => .quant .ex [m] d acc) (.bin .and a' b')

/-- The run of existential quantifiers at the front of an expression, outermost
first, and what they quantify. -/
def exPrefix : Expr → List (List String × Expr) × Expr
  | .quant .ex ids d b => let (ps, body) := exPrefix b; ((ids, d) :: ps, body)
  | e => ([], e)

/-- The one-point rule on `∃v: d· b`: when a conjunct of `b` is `v = e` or
`e = v` with `v` not in `e`, the quantifier over `v` goes, `e` replaces `v`, and
`e: d` is kept unless the domain is `int` (where every number expression is
an element).

A run of existentials `∃v: d· ∃w: d′· b` is read as one quantifier — the
order of existentials does not matter — so `v` may be pinned by a conjunct of
the innermost body, as sequential composition writes them. Then `e` must
mention none of the identifiers the run binds, which keeps every quantifier's
scope what it was. -/
def onePoint (e : Expr) : List Expr :=
  let (pre, body) := exPrefix e
  let bound := pre.flatMap (·.1)
  let cs := Expr.conjuncts body
  (List.range pre.length).flatMap fun layer =>
    let (ids, d) := pre[layer]!
    ids.flatMap fun v =>
      (List.range cs.length).filterMap fun i => do
        let c ← cs[i]?
        let t ← match c with
          | .bin .eq l r =>
              if l == .var v then some r else if r == .var v then some l else none
          | _ => none
        if bound.any (t.occurs ·) then none
        let rest := (cs.eraseIdx i).map (Expr.subst [(v, t)])
        let mem := if d == .var "int" then [] else [Expr.bin .mem t d]
        let inner := Expr.conj (mem ++ rest)
        let pre' := (pre.set layer (ids.erase v, d)).filter (!·.1.isEmpty)
        some (pre'.foldr (fun (ids', d') acc => .quant .ex ids' d' acc) inner)

/-- The name a rule is cited by. -/
def ruleName : Rule → String
  | .ok => "ok"
  | .assignment => "assignment"
  | .seq => "sequential composition"
  | .substitution => "substitution law"
  | .onePoint => "one point"
  | .vacuous => "vacuous quantifier"
  | .definition n => "definition of " ++ n

/-- The rules in force: the five when there is a state, and a definition per
named specification. -/
def rules (p : Prog) : List Rule :=
  -- A proof that declares no state is not about programs, and is offered what
  -- it always was.
  (if p.state.isEmpty then [] else [.ok, .assignment, .seq, .substitution, .onePoint, .vacuous])
    ++ p.specs.map (.definition ·.1)

/-- What a rule may replace the expression `e` with; every result is equal to
`e`. -/
def apply (p : Prog) : Rule → Expr → List Expr
  | .ok, .var "ok" => if p.state.isEmpty then [] else [p.okBody]
  | .ok, e => if !p.state.isEmpty && e == p.okBody then [.var "ok"] else []
  | .assignment, .bin .assign (.var x) v =>
      if p.state.any (·.1 == x) then [p.assignBody x v] else []
  | .seq, .bin .seq a b =>
      if p.isPlain a && p.isPlain b && !p.state.isEmpty then [p.seqBody a b] else []
  | .substitution, .bin .seq (.bin .assign (.var x) v) b =>
      match p.state.lookup x with
      | some d =>
          if !p.isPlain b then [] else
          -- Over a domain that the expression may leave, the assignment has no
          -- final state at all when it does, so its membership stays as a
          -- conjunct: over `nat`, `m:= m–1. P` is `m–1: nat ∧ P` with `m–1` for
          -- `m`, which is `⊥` when `m` is `0`, as the left side is.
          if p.staysIn d v then [b.subst [(x, v)]]
          else [.bin .and (.bin .mem v d) (b.subst [(x, v)])]
      | none => []
  | .onePoint, e => onePoint e
  -- A domain the kernel knows is not empty, so a quantifier over it that binds
  -- nothing the body mentions can go.
  | .vacuous, .quant k ids d b =>
      if [Expr.var "int", .var "nat", .var "bin"].contains d then
        let used := ids.filter (b.occurs ·)
        if used.length == ids.length then []
        else if used.isEmpty then [b] else [.quant k used d b]
      else []
  | .definition n, e =>
      match p.specs.lookup n with
      | some body => if e == .var n then [body] else if e == body then [.var n] else []
      | none => []
  | _, _ => []

end Prog
end Netty
