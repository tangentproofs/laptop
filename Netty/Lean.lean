import Lean
import Netty.Proof

/-!
# Netty proofs as Lean theorems

`netty_proofs "file.proof"` reads a calculation file (`Netty.Proof`), checks each
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
margins are Lean's own relations. Each link of the `calc` is proved by
`netty_step`, which tries Lean's decision procedures (`grind`, then `simp` and
`grind`, then `omega`). So *Lean re-proves every step on its own*: the law a
hint names is what the Netty kernel checked, and the Lean proof does not trust
it. A step whose hint names no law (`Proof.StepCheck.lean`) is checked by Lean
alone, and the command says which ones those are.

Finally the chain is turned into the claim, by the rule `Doc.outcome` uses: a
chain `A = … = ⊤` or `A ⇐ … ⇐ ⊤` proves `A`, a chain `A = … = ⊥` or
`A ⇒ … ⇒ ⊥` proves `¬A`, and any other chain proves `A op Z`.
-/

namespace Netty.Calc

/-- `a ⇒ b`, as a margin relation of a `calc` chain. -/
def Imp (a b : Prop) : Prop := a → b

/-- `a ⇐ b`, as a margin relation of a `calc` chain. -/
def Rimp (a b : Prop) : Prop := b → a

instance : Trans Imp Imp Imp := ⟨fun h g x => g (h x)⟩
instance : Trans Iff Imp Imp := ⟨fun h g x => g (h.mp x)⟩
instance : Trans Imp Iff Imp := ⟨fun h g x => g.mp (h x)⟩
instance : Trans Rimp Rimp Rimp := ⟨fun h g x => h (g x)⟩
instance : Trans Iff Rimp Rimp := ⟨fun h g x => h.mpr (g x)⟩
instance : Trans Rimp Iff Rimp := ⟨fun h g x => h (g.mpr x)⟩

instance : @Trans Int Int Int (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨Int.le_trans⟩
instance : @Trans Int Int Int (· ≤ ·) (· < ·) (· < ·) := ⟨Int.lt_of_le_of_lt⟩
instance : @Trans Int Int Int (· < ·) (· ≤ ·) (· < ·) := ⟨Int.lt_of_lt_of_le⟩
instance : @Trans Int Int Int (· < ·) (· < ·) (· < ·) := ⟨Int.lt_trans⟩
instance : @Trans Int Int Int (· ≥ ·) (· ≥ ·) (· ≥ ·) := ⟨fun h g => Int.le_trans g h⟩
instance : @Trans Int Int Int (· ≥ ·) (· > ·) (· > ·) := ⟨fun h g => Int.lt_of_lt_of_le g h⟩
instance : @Trans Int Int Int (· > ·) (· ≥ ·) (· > ·) := ⟨fun h g => Int.lt_of_le_of_lt g h⟩
instance : @Trans Int Int Int (· > ·) (· > ·) (· > ·) := ⟨fun h g => Int.lt_trans g h⟩

/-- Prove one link of a translated calculation. -/
macro "netty_step" : tactic =>
  `(tactic| (try simp only [Netty.Calc.Imp, Netty.Calc.Rimp]
             first
               | grind
               | (simp <;> grind)
               | omega))

end Netty.Calc

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
def theoremTys (es : List Expr) : Tys := Id.run do
  let mut env : Tys := []
  for _ in [0:6] do
    env := es.foldl (fun env e => infer [] (some .boolean) env e) env
  return env

/-- A Lean identifier for an aPToP identifier. -/
def ident (n : String) : Ident := mkIdent (Name.mkSimple n)

/-- Translate an expression of type `ty` into a Lean term. -/
partial def term (env : Tys) (ty : Ty) : Expr → CommandElabM Term
  | .var n => return ident n
  | .num n => `(($(quote n) : Int))
  | .top => `(True)
  | .bot => `(False)
  | .neg a => do `(¬ $(← term env .boolean a))
  | .bin o l r => do
      let lt := match o.operandTy with
        | some t => t
        | none => (tyIn env l).getD ((tyIn env r).getD .boolean)
      if o == .mem then
        let x ← term env .number l
        return ← match r with
          | .var "nat" => `(0 ≤ $x)
          | .var "int" => `(True)
          | d => throwError s!"Netty: no translation of the domain {d.render}"
      let a ← term env lt l
      let b ← term env lt r
      match o, lt with
      | .and, _ => `($a ∧ $b)
      | .or, _ => `($a ∨ $b)
      | .imp, _ => `($a → $b)
      | .rimp, _ => `($b → $a)
      | .eq, .boolean => `(($a ↔ $b))
      | .eq, .number => `($a = $b)
      | .ne, .boolean => `(¬($a ↔ $b))
      | .ne, .number => `($a ≠ $b)
      | .lt, _ => `($a < $b)
      | .gt, _ => `($a > $b)
      | .le, _ => `($a ≤ $b)
      | .ge, _ => `($a ≥ $b)
      | .add, _ => `($a + $b)
      | .sub, _ => `($a - $b)
      | .mul, _ => `($a * $b)
      | .mem, _ => throwError "unreachable"
  | .cond c x y => do
      let c' ← term env .boolean c
      let t := (tyIn env x).getD ((tyIn env y).getD ty)
      let x' ← term env t x
      let y' ← term env t y
      match t with
      | .boolean => `((($c' → $x') ∧ (¬$c' → $y')))
      | .number => `((if $c' then $x' else $y'))
  | .quant k ids d b => do
      let dt ← match domainTy d with
        | some t => pure t
        | none => throwError s!"Netty: no translation of the domain {d.render}"
      let env' := ids.map (·, dt) ++ env
      let body ← term env' .boolean b
      let leanTy ← match dt with
        | .boolean => `(Prop)
        | .number => `(Int)
      ids.foldrM (fun n acc => do
        let x := ident n
        let guard ← match d with
          | .var "nat" => `(0 ≤ $x)
          | _ => `(True)
        match k with
        | .all => `(∀ $x:ident : $leanTy, $guard → $acc)
        | .ex => `(∃ $x:ident : $leanTy, $guard ∧ $acc)) body
  | .mvar n => throwError s!"Netty: a law variable ‘{n}’ is left in the proof"

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

/-- The Lean command a checked calculation translates to. -/
def theoremCmd (c : Checked) : CommandElabM Syntax := do
  let t := c.thm
  let env := theoremTys (t.claim :: t.lines.map (·.expr))
  let names := t.claim.vars ++ (t.lines.flatMap fun l => l.expr.vars)
  let names := names.eraseDups
  let lines ← t.lines.mapM fun l => term env c.ty l.expr
  let claim ← term env .boolean t.claim
  -- The links of the chain, each proved by `netty_step` and joined by `Trans`,
  -- which is what a `calc` block elaborates to.
  let pairs := lines.zip (lines.drop 1)
  let conns := (t.lines.drop 1).map fun l => l.conn.getD .eq
  let links ← (pairs.zip conns).mapM fun ((a, b), o) => do
    let rel ← link c.ty o a b
    `((show $rel from by netty_step))
  let chain ← match links with
    | l :: ls => ls.foldlM (fun acc x => `(Trans.trans $acc $x)) l
    | [] => throwError "Netty: a calculation needs two lines"
  let bottom := (t.lines.getLast?.map (·.expr)).getD .top
  let top := (t.lines.head?.map (·.expr)).getD .top
  let whole := (Netty.Expr.bin c.rel top bottom).normAssoc == t.claim.normAssoc
  let body ← if whole then pure chain else match c.rel, bottom with
    | .eq, .top => if c.ty == .boolean then `(($chain).mpr trivial) else pure chain
    | .rimp, .top => `(($chain) trivial)
    | .eq, .bot => if c.ty == .boolean then `(fun h => ($chain).mp h) else pure chain
    | .imp, .bot => `(fun h => ($chain) h)
    | _, _ => pure chain
  let binders ← names.mapM fun n => do
    let ty ← match env.lookup n |>.getD .boolean with
      | .boolean => `(Prop)
      | .number => `(Int)
    `(bracketedBinder| ($(ident n) : $ty))
  let bs := binders.toArray
  let declName := mkIdent (Name.mkSimple (t.name.map fun ch => if ch == ' ' then '_' else ch))
  `(open Classical in theorem $declName:ident $bs* : $claim := $body)

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
  match Proof.checkFile text with
  | .error e => throwError s!"{path}: {e}"
  | .ok cs =>
      for c in cs do
        let cmd ← theoremCmd c
        withRef stx (elabCommand cmd)
        logInfo m!"{c.summary}"

end Netty.ToLean
