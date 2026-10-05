import Lean
import Netty.Proof
import Netty.Tactics

/-!
# Netty proofs as Lean theorems

`netty_proofs "file.calc"` reads a calculation file (`Netty.Proof`), checks each
calculation with the Netty kernel, and then *translates* each calculation into a
Lean theorem and elaborates it. The proof stays written in aPToP's notation, in
the file; Lean sees an ordinary theorem whose proof is a `calc` chain with one
link per line of the calculation.

## The translation

Each identifier becomes a universally quantified variable of the theorem, typed
by how the calculation uses it: `Prop` when it is boolean, `Int` when it is a
number. The operators become their Lean counterparts:

| aPToP | Lean, boolean | Lean, number |
| ----- | ------------- | ------------ |
| `⊤ ⊥` | `True False` | |
| `¬ ∧ ∨` | `¬ ∧ ∨` | |
| `a ⇒ b`, `a ⇐ b` | `a → b`, `b → a` | |
| `a = b`, `a ⧧ b` | `a ↔ b`, `¬(a ↔ b)` | `a = b`, `a ≠ b` |
| `< > ≤ ≥ + - ×` | | `< > ≤ ≥ + - *` |
| `if c then a else b fi` | `(c → a) ∧ (¬c → b)` | `if c then a else b` |
| `∀x: nat· b`, `∃x: nat· b` | `∀ x : Int, 0 ≤ x → b`, `∃ x : Int, 0 ≤ x ∧ b` | |
| `x: nat`, `x: int` | `0 ≤ x`, `True` | |

A margin `⇒` between two lines becomes `Netty.Calc.Imp`, which is `→`, a `⇐`
becomes `Netty.Calc.Rimp`, the converse, and a boolean `=` becomes `↔`; number
margins are Lean's own relations. The links are chained by `Trans`.

## Each step is proved by the law it names

Every law of the shipped lists has a *Lean twin* (`Netty.Twins`), a theorem
stating it, and the kernel records how it took each step (`Cert`): where in the
line the law was applied, which reading of it, and the substitution. The step's
Lean proof is built from that, with no search: the twin instantiated by the
substitution, read the way the step read the law, converted to the place as the
line writes it (`netty_ac`: association, symmetry, units), and carried to the
whole line by congruence or, for a step in a direction, by monotonicity through
exactly the positions the kernel's direction rules went through. A rule's step
(`Netty.Program`) is proved the same way by the rule's tactic (`netty_rule`), and
an earlier theorem cited as a law is its own twin.

Each such proof is tried on its own first (`accepts`). A step with no
certificate — a hint that names no law, such as `arithmetic` — or whose
certificate's proof Lean does not accept is proved by Lean's automation
(`netty_step`) instead, and the command reports, for every theorem, how many
steps came from the twins, how many from rule tactics and how many from
automation, and why.

Finally the chain is turned into the claim, by the rule `Doc.outcome` uses: a
chain `A = … = ⊤` or `A ⇐ … ⇐ ⊤` proves `A`, a chain `A = … = ⊥` or
`A ⇒ … ⇒ ⊥` proves `¬A`, and any other chain proves `A op Z`.
-/


namespace Netty.ToLean

open _root_.Lean (Syntax mkIdent quote Name Term Ident TSyntax)
open _root_.Lean.Elab.Command (CommandElabM CommandElab elabCommand)

/-- The types of the identifiers of an expression, as far as the expression
settles them. -/
abbrev Tys := List (String × Ty)

/-- Record that `n` has type `t`, unless it already has one. -/
def note (n : String) (t : Ty) (env : Tys) : Tys :=
  if (env.lookup n).isSome then env else (n, t) :: env

/-- The type an expression has, from its operator or from what is known of its
identifiers. -/
def tyIn (env : Tys) : Expr → Option Ty
  | .var n => env.lookup n
  | e => e.tyOf?

/-- The type of the elements of a domain, when the kernel knows the domain. -/
def domainTy : Expr → Option Ty
  | .var "nat" | .var "int" => some .number
  | .var "bin" | .var "bool" => some .boolean
  | _ => none

/-- One pass of type inference: walk the expression with the type its place
expects, if the place settles one, noting the type of every identifier met in a
place that does. `bound` are the names a quantifier binds, which are not
identifiers of the theorem. -/
partial def infer (bound : List String) (expect : Option Ty) (env : Tys) : Expr → Tys
  | .var n =>
      match expect with
      | some t => if bound.contains n then env else note n t env
      | none => env
  | .neg a => infer bound (some .boolean) env a
  | .bin o l r =>
      match o.operandTy with
      | some t => infer bound (some t) (infer bound (some t) env l) r
      | none =>
          if o == .mem then infer bound (some .number) env l
          else
            let t := (tyIn env l).orElse fun _ => tyIn env r
            infer bound t (infer bound t env l) r
  | .cond c x y =>
      let t := expect.orElse fun _ => (tyIn env x).orElse fun _ => tyIn env y
      infer bound t (infer bound t (infer bound (some .boolean) env c) x) y
  | .quant _ ids _ b => infer (ids ++ bound) (some .boolean) env b
  | _ => env

/-- The types of the identifiers of a theorem: inference run over the claim
and every line until nothing changes, so that `x = y` learns `x` is a number
from a later `x ≤ 3`. Whatever is still unsettled is boolean. -/
def theoremTys (init : Tys) (es : List Expr) : Tys := Id.run do
  let mut env : Tys := init
  for _ in [0:6] do
    env := es.foldl (fun env e => infer [] (some .boolean) env e) env
  return env

/-- A Lean identifier for an aPToP identifier: primes become `'`. -/
def ident (n : String) : Ident :=
  mkIdent (Name.mkSimple ((n.replace "″" "''").replace "′" "'"))

/-- What a translation knows: the types of the identifiers, the state and the
named specifications, and the renaming of state variables that sequential
composition has made on the way in (`x′` to an intermediate state, say). -/
structure Scope where
  /-- The identifiers' types. -/
  env : Tys
  /-- The state and the named specifications. -/
  prog : Prog
  /-- Names standing for other names. -/
  ren : List (String × String) := []
  /-- How many sequential compositions deep the translation is, for fresh names. -/
  depth : Nat := 0
  /-- The hole of a context (`holeName`), and the identifiers it is applied
  to: the translation of a context writes `H a₁ … aₙ` there. -/
  hole : Option (Ident × List String) := none

/-- The Lean type of a domain's elements. -/
def leanTy : Ty → CommandElabM Term
  | .boolean => `(Prop)
  | .number => `(Int)

/-- The guard a domain puts on a variable of it: `0 ≤ x` for `nat`. -/
def guard (d : Expr) (x : Term) : CommandElabM (Option Term) :=
  match d with
  | .var "nat" => do return some (← `(0 ≤ $x))
  | _ => return none

/-- The hole a context leaves where a law was applied. -/
def holeName : String := "□"

/-- A chain of sequential compositions as its first specification and the
rest, the rest nested to the right. -/
def seqChain (e : Expr) : Expr × Option Expr :=
  match Expr.flattenOp .seq e with
  | a :: rest@(_ :: _) =>
      let r := (rest.dropLast).foldr (fun x acc => Expr.bin .seq x acc) rest.getLast!
      (a, some r)
  | _ => (e, none)

/-- The name an identifier stands for here. -/
def Scope.name (sc : Scope) (n : String) : String := (sc.ren.lookup n).getD n

mutual

/-- Translate an expression of type `ty` into a Lean term. -/
partial def term (sc : Scope) (ty : Ty) : Expr → CommandElabM Term
  | .var n => do
      if n == "ok" && !sc.prog.state.isEmpty then
        return ← term sc .boolean sc.prog.okBody
      if sc.prog.specs.any (·.1 == n) then
        let args := sc.prog.params.map fun v => (ident (sc.name v) : Term)
        return ← `($(ident n) $(args.toArray)*)
      return ident (sc.name n)
  | .num n => `(($(quote n) : Int))
  | .top => `(True)
  | .bot => `(False)
  | .neg a => do `(¬ $(← term sc .boolean a))
  | .bin .assign (.var x) e => term sc .boolean (sc.prog.assignBody x e)
  | .bin .seq a b =>
      -- A chain of compositions is one chain whichever way the line brackets
      -- it, since `.` is associative; it is translated nested to the right, so
      -- that two bracketings of it are the same Lean term.
      match seqChain (.bin .seq a b) with
      | (a', some b') => seqTerm sc a' b'
      | (_, none) => seqTerm sc a b
  | .bin o l r => do
      let env := sc.env
      let lt := match o.operandTy with
        | some t => t
        | none => (tyIn env l).getD ((tyIn env r).getD .boolean)
      if o == .mem then
        let x ← term sc .number l
        return ← match r with
          | .var "nat" => `(0 ≤ $x)
          | .var "int" => `(True)
          | d => throwError s!"Netty: no translation of the domain {d.render}"
      let a ← term sc lt l
      let b ← term sc lt r
      match o, lt with
      | .and, _ => `($a ∧ $b)
      | .or, _ => `($a ∨ $b)
      | .imp, _ => `($a → $b)
      | .rimp, _ => `($b → $a)
      | .eq, .boolean => `(($a = $b))
      | .eq, .number => `($a = $b)
      | .ne, .boolean => `(¬($a = $b))
      | .ne, .number => `($a ≠ $b)
      | .lt, _ => `($a < $b)
      | .gt, _ => `($a > $b)
      | .le, _ => `($a ≤ $b)
      | .ge, _ => `($a ≥ $b)
      | .add, _ => `($a + $b)
      | .sub, _ => `($a - $b)
      | .mul, _ => `($a * $b)
      | o, _ => throwError s!"Netty: no translation of ‘{o.symbol}’ here"
  | .cond c x y => do
      let c' ← term sc .boolean c
      let t := (tyIn sc.env x).getD ((tyIn sc.env y).getD ty)
      let x' ← term sc t x
      let y' ← term sc t y
      match t with
      | .boolean => `((($c' → $x') ∧ (¬$c' → $y')))
      | .number => `((if $c' then $x' else $y'))
  | .quant k ids d b => do
      let dt ← match domainTy d with
        | some t => pure t
        | none => throwError s!"Netty: no translation of the domain {d.render}"
      let sc' := { sc with env := ids.map (·, dt) ++ sc.env,
                           ren := sc.ren.filter fun p => !ids.contains p.1 }
      let body ← term sc' .boolean b
      let lty ← leanTy dt
      ids.foldrM (fun n acc => do
        let x := ident n
        match k, ← guard d x with
        | .all, some g => `(∀ $x:ident : $lty, $g → $acc)
        | .all, none => `(∀ $x:ident : $lty, $acc)
        | .ex, some g => `(∃ $x:ident : $lty, $g ∧ $acc)
        | .ex, none => `(∃ $x:ident : $lty, $acc)) body
  | .mvar n => do
      if n == holeName then
        if let some (h, args) := sc.hole then
          let as ← args.mapM fun v => term sc .boolean (.var v)
          return ← `($h $(as.toArray)*)
      throwError s!"Netty: a law variable ‘{n}’ is left in the proof"

/-- `P. Q`: there is an intermediate state, which is `P`'s final state and
`Q`'s initial one. Rather than substitute into `P` and `Q`, the translation
renames: inside `P` the primed state variables stand for the intermediate
ones, inside `Q` the unprimed ones do. So a named specification called in
either is applied to the right state. -/
partial def seqTerm (sc : Scope) (a b : Expr) : CommandElabM Term := do
  let mids := sc.prog.state.map fun (v, d) => (v, d, s!"{v}_{sc.depth}")
  let scA := { sc with depth := sc.depth + 1,
                       ren := mids.map (fun (v, _, m) => (prime v, m)) ++ sc.ren,
                       env := mids.map (fun (v, _, m) => (m, (sc.env.lookup v).getD .number)) ++ sc.env }
  let scB := { scA with ren := mids.map (fun (v, _, m) => (v, m)) ++ sc.ren }
  let a' ← term scA .boolean a
  let b' ← term scB .boolean b
  -- The same shape as the translation of the sequential composition rule's
  -- expansion (`Prog.seqBody`), `∃x″: d· ∃y″: d· …`, so that the rule's step is
  -- definitional.
  let body ← `($a' ∧ $b')
  mids.foldrM (fun (v, d, m) acc => do
    let lty ← leanTy ((sc.env.lookup v).getD .number)
    let x := ident m
    match ← guard d x with
    | some g => `(∃ $x:ident : $lty, $g ∧ $acc)
    | none => `(∃ $x:ident : $lty, $acc)) body

end

/-- The `calc` relation of a margin connective between two translated lines. -/
def link (ty : Ty) (o : BinOp) (a b : Term) : CommandElabM Term :=
  match o, ty with
  | .eq, .boolean => `(($a ↔ $b))
  | .eq, .number => `($a = $b)
  | .imp, _ => `(Netty.Calc.Imp $a $b)
  | .rimp, _ => `(Netty.Calc.Rimp $a $b)
  | .lt, _ => `($a < $b)
  | .gt, _ => `($a > $b)
  | .le, _ => `($a ≤ $b)
  | .ge, _ => `($a ≥ $b)
  | o, _ => throwError s!"Netty: ‘{o.symbol}’ cannot stand in the margin"

/-- The types the state gives its variables and their primes. -/
def stateTys (p : Prog) : Tys :=
  p.state.flatMap fun (v, d) =>
    let t := (domainTy d).getD .number
    [(v, t), (prime v, t)]

/-- The Lean definition of a named specification: a proposition about the
state variables and their primes. -/
def specCmd (p : Prog) (name : String) (body : Expr) : CommandElabM Syntax := do
  let env := theoremTys (stateTys p) [body]
  let sc : Scope := { env := env, prog := { p with specs := p.specs.filter (·.1 != name) } }
  let b ← term sc .boolean body
  let binders ← p.params.mapM fun n => do
    `(bracketedBinder| ($(ident n) : $(← leanTy ((env.lookup n).getD .number))))
  let bs := binders.toArray
  `(open Classical in def $(ident name):ident $bs* : Prop := $b)

/-! ### Steps proved from the laws' twins

A step the kernel took by a law carries a `Cert`: the line it started from, the
zooms to where the law was applied, the reading of the law and its substitution.
From that the translation builds the step's Lean proof without any search:

* the *context* is the line with the place the law was applied replaced by a
  hole (`plug`), translated as a function of what fills the hole;
* the *leaf* is the law's twin, instantiated by the substitution, read the way
  the step read the law (reversed, `= ⊤`, conditional), and converted from the
  law's left side to the place as the line writes it — which differ only by
  association, symmetry and units (`netty_ac`);
* an equality at the leaf is carried to the whole line by congruence
  (`congrArg`), and an implication by monotonicity (`mono`), following exactly
  the positions the kernel's direction rules followed.

A rule's step (`Netty.Program`) is proved the same way with the rule's tactic
(`netty_rule`) at the leaf; `ok`, assignment, sequential composition and the
definition of a specification are definitional in the translation. A step that
none of this covers — a law without a twin, a context fact, a hint that names
no law — is proved by `netty_step`, and the command says which steps those were.
-/

/-- A law's statement with its law variables as ordinary identifiers. -/
def unMVar : Expr → Expr
  | .mvar n => .var n
  | .neg a => .neg (unMVar a)
  | .bin o l r => .bin o (unMVar l) (unMVar r)
  | .cond c x y => .cond (unMVar c) (unMVar x) (unMVar y)
  | .quant k ids d b => .quant k ids (unMVar d) (unMVar b)
  | e => e

/-- How a step was proved in Lean. -/
inductive How
  /-- From the twins of the laws it names. -/ | twin
  /-- By the tactics of the rules it names. -/ | rule
  /-- By automation, for the reason given. -/ | auto (why : String)
  deriving Inhabited, BEq

/-- Whether an expression holds the hole. -/
def hasHole : Expr → Bool
  | .mvar n => n == holeName
  | .neg a => hasHole a
  | .bin _ l r => hasHole l || hasHole r
  | .cond c x y => hasHole c || hasHole x || hasHole y
  | .quant _ _ d b => hasHole d || hasHole b
  | _ => false

/-- The line `e` with the place a certificate's step rewrote replaced by the
hole: down the zooms of `path`, then the part `site` of the line found there. -/
def plug : Expr → List Part → Part → Option Expr
  | _, [], .whole => some (.mvar holeName)
  | e, [], sp => sp.replace e (.mvar holeName)
  | e, p :: ps, sp => do p.replace e (← plug (← p.exprOf e) ps sp)

/-- Fill the hole. -/
def fill (h : Expr) : Expr → Expr
  | .mvar n => if n == holeName then h else .mvar n
  | .neg a => .neg (fill h a)
  | .bin o l r => .bin o (fill h l) (fill h r)
  | .cond c x y => .cond (fill h c) (fill h x) (fill h y)
  | .quant k ids d b => .quant k ids (fill h d) (fill h b)
  | e => e

/-- The identifiers quantifiers bind on the way to the hole, with their types. -/
def boundToHole : Expr → List (String × Ty)
  | .quant _ ids d b =>
      if hasHole b then ids.map (·, (domainTy d).getD .number) ++ boundToHole b
      else boundToHole d
  | .neg a => boundToHole a
  | .bin _ l r => if hasHole l then boundToHole l else boundToHole r
  | .cond c x y => if hasHole c then boundToHole c else if hasHole x then boundToHole x
      else boundToHole y
  | _ => []

/-- The identifiers a sequential composition renames on the way to the hole:
inside its first specification the primed state variables stand for an
intermediate state, inside its second the unprimed ones do. -/
partial def renamedToHole (p : Prog) : Expr → List String
  | .bin .seq a0 b0 =>
      let (a, b) := match seqChain (.bin .seq a0 b0) with
        | (a', some b') => (a', b')
        | (_, none) => (a0, b0)
      if hasHole a then p.state.map (prime ·.1) ++ renamedToHole p a
      else p.state.map (·.1) ++ renamedToHole p b
  | .quant _ _ d b => if hasHole b then renamedToHole p b else renamedToHole p d
  | .neg a => renamedToHole p a
  | .bin _ l r => if hasHole l then renamedToHole p l else renamedToHole p r
  | .cond c x y => if hasHole c then renamedToHole p c else if hasHole x then renamedToHole p x
      else renamedToHole p y
  | _ => []

/-- The name of the hypothesis that a natural variable is at least zero, as the
theorem's binders and the monotonicity proofs name it. -/
def guardHyp (leanName : String) : Ident := mkIdent (Name.mkSimple ("h_" ++ leanName))

/-- `fun a₁ … aₙ => body`. -/
def lams (as : List (Ident × Term)) (body : Term) : CommandElabM Term :=
  as.foldrM (fun (a, t) acc => `(fun ($a : $t) => $acc)) body

/-- The identifiers `nat` quantifiers bind on the way to the hole. -/
def natBoundToHole : Expr → List String
  | .quant _ ids d b =>
      if hasHole b then (if d == .var "nat" then ids else []) ++ natBoundToHole b
      else natBoundToHole d
  | .neg a => natBoundToHole a
  | .bin _ l r => if hasHole l then natBoundToHole l else natBoundToHole r
  | .cond c x y => if hasHole c then natBoundToHole c else if hasHole x then natBoundToHole x
      else natBoundToHole y
  | _ => []

/-- Monotonicity: from the leaf's implication, an implication between the
context filled one way and the other. `want` is `true` for `C[S] → C[T]` and
`false` for `C[T] → C[S]`; `fwd` says which the leaf gives, `S → T` or `T → S`.
A negative position turns the wanted direction round, as the kernel's direction
rules did on the way in. -/
partial def mono (leaf : Scope → Bool → CommandElabM Term) (sc : Scope) (want : Bool) :
    Expr → CommandElabM Term
  | .mvar n => do
      if n != holeName then throwError "Netty: not a context"
      leaf sc want
  | .neg a => do
      let m ← mono leaf sc (!want) a
      `(fun hn h => hn ($m h))
  | .bin .and l r => do
      if hasHole l then let m ← mono leaf sc want l; `(fun h => And.intro ($m h.1) h.2)
      else let m ← mono leaf sc want r; `(fun h => And.intro h.1 ($m h.2))
  | .bin .or l r => do
      if hasHole l then let m ← mono leaf sc want l; `(Or.imp $m id)
      else let m ← mono leaf sc want r; `(Or.imp id $m)
  | .bin .imp l r => do
      if hasHole r then let m ← mono leaf sc want r; `(fun f x => $m (f x))
      else let m ← mono leaf sc (!want) l; `(fun f x => f ($m x))
  | .bin .rimp l r => do
      -- `l ⇐ r` is `r → l`.
      if hasHole l then let m ← mono leaf sc want l; `(fun f x => $m (f x))
      else let m ← mono leaf sc (!want) r; `(fun f x => f ($m x))
  | .cond c x y => do
      if hasHole c then throwError "Netty: a condition is not a monotonic position"
      if hasHole x then
        let m ← mono leaf sc want x
        `(fun h => And.intro (fun hc => $m (h.1 hc)) h.2)
      else
        let m ← mono leaf sc want y
        `(fun h => And.intro h.1 (fun hc => $m (h.2 hc)))
  | .quant k ids d b => do
      if hasHole d then throwError "Netty: a domain is not a monotonic position"
      let dt := (domainTy d).getD .number
      let sc' := { sc with env := ids.map (·, dt) ++ sc.env,
                           ren := sc.ren.filter fun p => !ids.contains p.1 }
      let m ← mono leaf sc' want b
      ids.foldrM (fun n acc => do
        let x := ident n
        let hx := guardHyp x.getId.toString
        let g ← guard d x
        match k, g with
        | .all, some _ => `(fun f ($x) ($hx) => $acc (f $x $hx))
        | .all, none => `(fun f ($x) => $acc (f $x))
        | .ex, some _ => `(Exists.imp (fun ($x) hgb => (fun ($hx) => And.intro $hx ($acc hgb.2)) hgb.1))
        | .ex, none => `(Exists.imp (fun ($x) => $acc))) m
  | .bin .seq a0 b0 => do
      let (a, b) := match seqChain (.bin .seq a0 b0) with
        | (a', some b') => (a', b')
        | (_, none) => (a0, b0)
      let p := sc.prog
      let mids := p.state.map fun (v, d) => (v, d, s!"{v}_{sc.depth}")
      let scA := { sc with depth := sc.depth + 1,
                           ren := mids.map (fun (v, _, m) => (prime v, m)) ++ sc.ren,
                           env := mids.map (fun (v, _, m) => (m, (sc.env.lookup v).getD .number))
                             ++ sc.env }
      let scB := { scA with ren := mids.map (fun (v, _, m) => (v, m)) ++ sc.ren }
      let inner ← if hasHole a then
          let m ← mono leaf scA want a; `(And.imp $m id)
        else
          let m ← mono leaf scB want b; `(And.imp id $m)
      mids.foldrM (fun (_, d, m) acc => do
        let x := ident m
        let hx := guardHyp x.getId.toString
        match ← guard d x with
        | some _ => `(Exists.imp (fun ($x) hgb => (fun ($hx) => And.intro $hx ($acc hgb.2)) hgb.1))
        | none => `(Exists.imp (fun ($x) => $acc))) inner
  | _ => throwError "Netty: no monotonicity through this operator"

/-- The Lean proof of one application of a law or rule, as a link from `a` to
`b` (the line the certificate wrote, or the written line it stands for) with
the certificate's connective. -/
def certLink (env : Tys) (p : Prog) (ty : Ty) (a b : Expr) (c : Cert) :
    CommandElabM (Term × How) := do
  let s := c.sugg
  let some ctx := plug c.src c.path s.part | throwError "Netty: the place is not in the line"
  if !hasHole ctx then throwError "Netty: the place is not in the line"
  let S := s.site
  let T := s.replacement
  let sc : Scope := { env := env, prog := p }
  -- What the hole is applied to: the identifiers of the place, and the whole
  -- state when the place is written in programming notation.
  let progish := !(p.isPlain S && p.isPlain T)
  let fv := (S.vars ++ T.vars).filter fun n =>
    n != "ok" && !p.specs.any (·.1 == n) && !["int", "nat", "bin", "bool"].contains n
  -- Only what is bound or renamed on the way to the place is abstracted: the
  -- theorem's own identifiers stay themselves, with their hypotheses (`0 ≤ n`
  -- for a natural state variable), which a step over `nat` may need.
  let local_ := (boundToHole ctx).map (·.1) ++ renamedToHole p ctx
  let args := (((if progish then p.params else []) ++ fv).eraseDups).filter local_.contains
  let envH := boundToHole ctx ++ env
  let argTys := args.map fun v => (v, (envH.lookup v).getD .boolean)
  -- The abstracted identifiers that range over `nat`: a renamed natural state
  -- variable, or one a `nat` quantifier binds. The leaf takes their guards too.
  let natBound := natBoundToHole ctx
  let natArgs := args.filter fun v =>
    natBound.contains v || p.state.any fun (x, d) => (x == v || prime x == v) && d == .var "nat"
  let scL : Scope := { env := argTys ++ env, prog := p }
  let sty : Ty := match s.op.connTy with
    | some t => t
    | none => (tyIn scL.env S).getD ((tyIn scL.env T).getD .boolean)
  let S' ← term scL sty S
  let T' ← term scL sty T
  let binders ← argTys.mapM fun (v, t) => do return (ident v, ← leanTy t)
  let guardBinders ← natArgs.mapM fun v => do
    let x := ident v
    return (guardHyp x.getId.toString, ← `(0 ≤ $x))
  -- The leaf: the step at the place, `S` to `T`.
  let (leafProof, how, isEq, fwd) ← match s.rule, s.variant with
    | some _, _ =>
        let pf ← `((show $S' = $T' by netty_rule))
        pure (pf, How.rule, true, true)
    | none, some v => do
        if v.twin.isEmpty then throwError s!"Netty: {v.law} has no Lean twin"
        let σ := s.subst ++ c.bind
        let lawEnv := theoremTys [] [unMVar v.lhs, unMVar v.rhs] ++
          (match v.premise with | some q => theoremTys [] [unMVar q] | none => [])
        let insts ← if v.vars.isEmpty && !v.twinArgs.isEmpty then
            -- An earlier theorem: its twin is applied to the identifiers it is
            -- stated over, and their guards.
            v.twinArgs.flatMapM fun x => do
              let isNat := p.state.any fun (y, d) => (y == x || prime y == x) && d == .var "nat"
              let a ← term scL .boolean (.var x)
              if isNat then return [a, ← `((by assumption))] else return [a]
          else v.vars.mapM fun x => do
            let some e := σ.lookup x | throwError s!"Netty: {v.law} leaves {x} unbound"
            term scL ((tyIn scL.env e).getD ((lawEnv.lookup x).getD .boolean)) e
        let twinId := mkIdent v.twin.toName
        let inst ← `(($twinId $(insts.toArray)*))
        let inst ← if v.kind == "cond" || v.kind == "condFlip" then
            `(($inst (by netty_step))) else pure inst
        let L := v.lhs.instantiate σ
        let L' ← term scL sty L
        let formIsEq := match v.lhs with | .bin .eq _ _ => true | _ => false
        if v.op == .eq then
          let base ← match v.kind with
            | "flip" | "condFlip" => `(($inst).symm)
            | "eqTop" => if v.flipped && formIsEq then `(eq_true ($inst).symm) else `(eq_true $inst)
            | "topEq" =>
                let form := v.rhs
                let fe := match form with | .bin .eq _ _ => true | _ => false
                if v.flipped && fe then `((eq_true ($inst).symm).symm) else `((eq_true $inst).symm)
            | _ => pure inst
          let pf ← if S == L then `((show $S' = $T' from $base))
            else `((show $S' = $T' from Eq.trans (show $S' = $L' by netty_ac) $base))
          pure (pf, How.twin, true, true)
        else if sty == .boolean then
          -- `S ⇒ T` is `S → T`; `S ⇐ T` is `T → S`.
          let fwd := v.op == .imp
          let pf ← if S == L then
              if fwd then `((show $S' → $T' from $inst)) else `((show $T' → $S' from $inst))
            else if fwd then
              `((show $S' → $T' from fun h => $inst (Eq.mp (show $S' = $L' by netty_ac) h)))
            else
              `((show $T' → $S' from fun h => Eq.mpr (show $S' = $L' by netty_ac) ($inst h)))
          pure (pf, How.twin, false, fwd)
        else throwError "Netty: a number step in a direction is not replayed yet"
    | none, none => throwError "Netty: no certificate"
  let leafFn ← lams (binders ++ guardBinders) leafProof
  -- The leaf applied at the hole, to the place's identifiers as the context
  -- names them and to the guards the context has in scope for them.
  let leafAt : Scope → CommandElabM Term := fun sc' => do
    let as ← args.mapM fun v => term sc' .boolean (.var v)
    let gs := natArgs.map fun v => guardHyp (ident (sc'.name v)).getId.toString
    `($leafFn $(as.toArray)* $(gs.toArray)*)
  let A' ← term sc ty a
  let B' ← term sc ty b
  let CS' ← term sc ty (fill S ctx)
  let CT' ← term sc ty (fill T ctx)
  if isEq && !natArgs.isEmpty then
    -- An equality under guards: both directions by monotonicity, each using
    -- the guards the context supplies.
    -- At the hole, either direction of the equality, as the position asks.
    let leafEq : Scope → Bool → CommandElabM Term := fun sc' w => do
      if w then `(Eq.mp $(← leafAt sc')) else `(Eq.mpr $(← leafAt sc'))
    let mp ← mono leafEq sc true ctx
    let mpr ← mono leafEq sc false ctx
    let core ← `(propext (Iff.intro $mp $mpr))
    let e ← `(Eq.trans (show $A' = $CS' by netty_ac)
      (Eq.trans (show $CS' = $CT' from $core) (show $CT' = $B' by netty_ac)))
    let pf ← if ty == .boolean then `(Iff.of_eq $e) else pure e
    return (pf, how)
  if isEq then
    let H := mkIdent `H
    let resTy ← leanTy sty
    let τ ← binders.foldrM (fun (_, t) acc => `($t → $acc)) resTy
    let C' ← term { sc with hole := some (H, args) } ty ctx
    let funexts ← binders.foldrM (fun (x, t) acc => `(funext fun ($x : $t) => $acc))
      (← `($leafFn $(binders.toArray.map (·.1))*))
    let core ← `(congrArg (fun ($H : $τ) => $C') $funexts)
    let e ← `(Eq.trans (show $A' = $CS' by netty_ac)
      (Eq.trans (show $CS' = $CT' from $core) (show $CT' = $B' by netty_ac)))
    let pf ← if ty == .boolean then `(Iff.of_eq $e) else pure e
    return (pf, how)
  else
    let want := c.op == .imp
    let leafDir : Scope → Bool → CommandElabM Term := fun sc' w => do
      if w != fwd then throwError "Netty: the law goes the other way here"
      leafAt sc'
    let core ← mono leafDir sc want ctx
    if want then
      let pf ← `((show Netty.Calc.Imp $A' $B' from fun h =>
        Eq.mp (show $CT' = $B' by netty_ac)
          ((show $CS' → $CT' from $core) (Eq.mp (show $A' = $CS' by netty_ac) h))))
      return (pf, how)
    else
      let pf ← `((show Netty.Calc.Rimp $A' $B' from fun h =>
        Eq.mpr (show $A' = $CS' by netty_ac)
          ((show $CT' → $CS' from $core) (Eq.mpr (show $CT' = $B' by netty_ac) h))))
      return (pf, how)

/-- Whether Lean accepts `pf` as a proof of `rel` under the theorem's binders:
elaborated on its own, synchronously, with whatever it reports taken back out of
the message log. `none` when it does; otherwise the first error. -/
def accepts (bs : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (rel pf : Term) :
    CommandElabM (Option String) := do
  let saved := (← get).messages
  let cmd ← `(command|
    open Classical in set_option Elab.async false in example $bs* : $rel := $pf)
  elabCommand cmd
  let errs := (← get).messages.toList.filter (·.severity == .error)
  let before := saved.toList.filter (·.severity == .error) |>.length
  modify fun st => { st with messages := saved }
  if errs.length > before then
    if (← IO.getEnv "NETTY_DEBUG").isSome then
      _root_.Lean.logInfo m!"certificate proof failed:\n{cmd}\n{← (errs.drop before).head!.data.toString}"
    return some (((← (errs.drop before).head!.data.toString).splitOn "\n").headD "")
  else return none

/-- The proof of one step, from `a` to `b` with the connective `o`: from the
certificates when the kernel checked the step by laws or rules, and by
automation otherwise. -/
def stepProof (bs : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (env : Tys) (p : Prog)
    (ty : Ty) (unfold : Array Ident) (a b : Expr)
    (o : BinOp) (sc : StepCheck) : CommandElabM (Term × How) := do
  let scope : Scope := { env := env, prog := p }
  let A' ← term scope ty a
  let B' ← term scope ty b
  let rel ← link ty o A' B'
  let auto (why : String) : CommandElabM (Term × How) := do
    let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      unfold.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    let pf ← if unfold.isEmpty then `((show $rel from by netty_step))
      else `((show $rel from by (try simp only [$lemmas,*] at *) <;> netty_step))
    return (pf, How.auto why)
  let certs := match sc with
    | .law _ cs => cs
    | .lawIf _ _ cs => cs
    | .lean _ => []
  match sc with
  | .lean h => auto s!"‘{h}’ names no law"
  | _ =>
    if certs.isEmpty then auto "no certificate" else
    try
      -- The lines the applications pass through: the written line first, the
      -- written line last, and what the kernel wrote between.
      let mids := (certs.dropLast).map (·.dst)
      let froms := a :: mids
      let tos := mids ++ [b]
      let mut links : List Term := []
      let mut hows : List How := []
      for ((x, y), cert) in (froms.zip tos).zip certs do
        let (pf, h) ← certLink env p ty x y cert
        links := links ++ [pf]
        hows := hows ++ [h]
      let chain ← match links with
        | l :: ls => ls.foldlM (fun acc x => `(Trans.trans $acc $x)) l
        | [] => throwError "no links"
      -- The applications may add up to more than the written connective claims
      -- (an equality where `⇒` is written); then the claim is weakened.
      let pf ← `((show $rel from by
        first
          | exact $chain
          | exact ($chain).mp
          | exact ($chain).mpr
          | exact Int.le_of_eq $chain
          | exact Int.le_of_eq ($chain).symm
          | exact Int.le_of_lt $chain))
      let how := if hows.all (· == How.twin) then How.twin
        else if hows.any (· == How.rule) then How.rule else How.twin
      match ← accepts bs rel pf with
      | none => return (pf, how)
      | some err => auto s!"the certificate's proof failed: {err}"
    catch e => auto s!"{← e.toMessageData.toString}"

/-- The Lean command a checked calculation translates to, and how each step
was proved. -/
def theoremCmd (c : Checked) : CommandElabM (Syntax × List How) := do
  let t := c.thm
  let p := t.cx.prog
  let exprs := t.claim :: t.lines.map (·.expr)
  let env := theoremTys (stateTys p) exprs
  let sc : Scope := { env := env, prog := p }
  -- The theorem is about its free identifiers, and — when any line is written in
  -- programming notation — about the whole state before and after.
  let names := Proof.theoremParams p t.claim (t.lines.map (·.expr))
  let lines ← t.lines.mapM fun l => term sc c.ty l.expr
  let claim ← term sc .boolean t.claim
  -- The named specifications are unfolded before each step is proved.
  let unfold : Array Ident := (p.specs.map fun (n, _) => ident n).toArray
  let _ := lines
  let mut binders : Array Syntax := #[]
  for n in names do
    let ty ← leanTy ((env.lookup n).getD .boolean)
    binders := binders.push (← `(bracketedBinder| ($(ident n) : $ty)))
    -- A natural state variable, or its prime, is at least zero.
    let isNat := p.state.any fun (v, d) => (v == n || prime v == n) && d == .var "nat"
    if isNat then
      let h := mkIdent (Name.mkSimple ("h_" ++ (ident n).getId.toString))
      binders := binders.push (← `(bracketedBinder| ($h : 0 ≤ $(ident n))))
  let bs : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := binders.map (⟨·⟩)
  let pairs := t.lines.zip (t.lines.drop 1)
  let proofs ← (pairs.zip c.steps).mapM fun ((la, lb), st) =>
    stepProof bs env p c.ty unfold la.expr lb.expr (lb.conn.getD .eq) st
  let links := proofs.map (·.1)
  let chain ← match links with
    | l :: ls => ls.foldlM (fun acc x => `(Trans.trans $acc $x)) l
    | [] => throwError "Netty: a calculation needs two lines"
  let bottom := (t.lines.getLast?.map (·.expr)).getD .top
  let first := (t.lines.head?.map (·.expr)).getD .top
  let whole := (Netty.Expr.bin c.rel first bottom).normAssoc == t.claim.normAssoc
  let body ← if whole then
      (if c.ty == .boolean && c.rel == .eq then `(propext $chain) else pure chain)
    else match c.rel, bottom with
    | .eq, .top => if c.ty == .boolean then `(($chain).mpr trivial) else pure chain
    | .rimp, .top => `(($chain) trivial)
    | .eq, .bot => if c.ty == .boolean then `(fun h => ($chain).mp h) else pure chain
    | .imp, .bot => `(fun h => ($chain) h)
    | _, _ => pure chain
  let declName := mkIdent (Name.mkSimple (Proof.twinName t.name))
  let cmd ← `(open Classical in theorem $declName:ident $bs* : $claim := $body)
  return (cmd, proofs.map (·.2))

/-- `netty_proofs "file"` checks every calculation of a calculation file with the
Netty kernel, then elaborates each as a Lean theorem named after it (spaces
becoming `_`), in the current namespace. The path is relative to the Lean file
the command appears in. -/
syntax (name := nettyProofs) "netty_proofs " str : command

open _root_.Lean Elab Command in
@[command_elab nettyProofs] def elabNettyProofs : CommandElab := fun stx => do
  let p := stx[1].isStrLit?.getD ""
  let dir := (System.FilePath.mk (← getFileName)).parent.getD (System.FilePath.mk ".")
  let path := dir / p
  let text ← IO.FS.readFile path
  let _ := text
  let f ← match ← (Proof.load path).toBaseIO with
    | .ok f => pure f
    | .error e => throwError s!"{e}"
  match Proof.checkParsed f with
  | .error e => throwError s!"{path}: {e}"
  | .ok cs =>
      -- The specifications this file names become Lean definitions, in the
      -- order they were named; those of the files it extends are the Lean
      -- definitions of those files' own modules, which the importing module
      -- must have open.
      let mut prog : Prog := { state := f.cx.prog.state }
      let own := f.ownSpecs
      for (n, body) in f.cx.prog.specs do
        if own.contains n then
          withRef stx (elabCommand (← specCmd prog n body))
        prog := { prog with specs := prog.specs ++ [(n, body)] }
      for c in cs do
        let (cmd, hows) ← theoremCmd c
        -- `NETTY_TRACE=1` prints each Lean theorem before it is elaborated.
        if (← IO.getEnv "NETTY_TRACE").isSome then logInfo m!"{cmd}"
        let before := (← get).messages.toList.filter (·.severity == .error) |>.length
        withRef stx (elabCommand cmd)
        let after := (← get).messages.toList.filter (·.severity == .error) |>.length
        if after > before then
          logError m!"Lean could not prove a step of {c.thm.name} (line {c.thm.lineNo}); \
            the statement it was proving:\n{cmd}"
        else
          let tw := (hows.filter (· == How.twin)).length
          let ru := (hows.filter (· == How.rule)).length
          let au := hows.filterMap fun h => match h with | .auto w => some w | _ => none
          logInfo m!"{c.summary}\nin Lean: {tw} from the laws' twins, {ru} by rule tactics, \
            {au.length} by automation{if au.isEmpty then "" else
              " (" ++ String.intercalate "; " au.eraseDups ++ ")"}"

end Netty.ToLean
