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
`grind`, then `omega`, then the same under the binders both lines share). So *Lean re-proves every step on its own*: the law a
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
  `(tactic| ((try simp only [Netty.Calc.Imp, Netty.Calc.Rimp]) <;>
             first
               | grind
               | (simp <;> grind)
               | omega
               -- The intermediate state of a sequential composition, pinned by
               -- assignments: the one-point rule, which `grind` does not do.
               | (simp only [and_assoc, exists_and_left, exists_and_right, exists_eq_left,
                    exists_eq_right, exists_const] <;> first | grind | (simp <;> grind) | omega)
               -- A step inside the body of quantifiers: go under the binders
               -- both lines share, then prove the bodies equal.
               | ((repeat' (first | apply exists_congr | apply forall_congr' | intro))
                    <;> first | grind | (simp <;> grind) | omega)))

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

/-- The Lean type of a domain's elements. -/
def leanTy : Ty → CommandElabM Term
  | .boolean => `(Prop)
  | .number => `(Int)

/-- The guard a domain puts on a variable of it: `0 ≤ x` for `nat`. -/
def guard (d : Expr) (x : Term) : CommandElabM (Option Term) :=
  match d with
  | .var "nat" => do return some (← `(0 ≤ $x))
  | _ => return none

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
  | .bin .seq a b => seqTerm sc a b
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
  | .mvar n => throwError s!"Netty: a law variable ‘{n}’ is left in the proof"

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
  -- The domain guards go last, after the equations an assignment writes, so
  -- that the one-point simplification finds the equations first.
  let guards ← mids.filterMapM fun (_, d, m) => guard d (ident m)
  let body ← guards.foldlM (fun acc g => `($acc ∧ $g)) (← `($a' ∧ $b'))
  mids.foldrM (fun (v, _, m) acc => do
    let lty ← leanTy ((sc.env.lookup v).getD .number)
    `(∃ $(ident m):ident : $lty, $acc)) body

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

/-- The Lean command a checked calculation translates to. -/
def theoremCmd (c : Checked) : CommandElabM Syntax := do
  let t := c.thm
  let p := t.cx.prog
  let exprs := t.claim :: t.lines.map (·.expr)
  let env := theoremTys (stateTys p) exprs
  let sc : Scope := { env := env, prog := p }
  -- The theorem is about its free identifiers, and — when any line is written in
  -- programming notation — about the whole state before and after.
  let plain := exprs.all p.isPlain
  -- A domain is a name of a bunch, not an identifier of the theorem.
  let free := (exprs.flatMap Expr.vars).filter fun n =>
    n != "ok" && !p.specs.any (·.1 == n) && !["int", "nat", "bin", "bool"].contains n
  let names := ((if plain then [] else p.params) ++ free).eraseDups
  let lines ← t.lines.mapM fun l => term sc c.ty l.expr
  let claim ← term sc .boolean t.claim
  -- The named specifications are unfolded before each step is proved.
  let unfold : Array Ident := (p.specs.map fun (n, _) => ident n).toArray
  let pairs := lines.zip (lines.drop 1)
  let conns := (t.lines.drop 1).map fun l => l.conn.getD .eq
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    unfold.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  let links ← (pairs.zip conns).mapM fun ((a, b), o) => do
    let rel ← link c.ty o a b
    if unfold.isEmpty then `((show $rel from by netty_step))
    else `((show $rel from by (try simp only [$lemmas,*] at *) <;> netty_step))
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
        let cmd ← theoremCmd c
        -- `NETTY_TRACE=1` prints each Lean theorem before it is elaborated.
        if (← IO.getEnv "NETTY_TRACE").isSome then logInfo m!"{cmd}"
        let before := (← get).messages.toList.filter (·.severity == .error) |>.length
        withRef stx (elabCommand cmd)
        let after := (← get).messages.toList.filter (·.severity == .error) |>.length
        if after > before then
          logError m!"Lean could not prove a step of {c.thm.name} (line {c.thm.lineNo}); \
            the statement it was proving:\n{cmd}"
        else logInfo m!"{c.summary}"

end Netty.ToLean
