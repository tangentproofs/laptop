import Netty.Lean

/-!
# The Lean twins of the laws

Every law of a shipped law list has a *twin*: a Lean theorem stating it, named
by `Law.twin`, so `Netty.Twin.boolean.l7` is the eighth law of
`laws/boolean.laws`. `netty_twins` generates them from the law list itself — the
statement is the law's translation (`Netty.ToLean.term`), quantified over its
law variables — and proves each one. So the law lists are checked by Lean too,
and a step the kernel takes by a law can be proved in Lean by citing its twin
(`Netty.ToLean`), which is what makes the translation of a calculation a proof
*by the laws it names* rather than by automation.

A law the translation cannot state (the quantifier laws, whose bodies are
predicates of the bound variable) has no twin, and a step by it is proved by
automation and said to be.
-/

namespace Netty.ToLean

open _root_.Lean (Syntax mkIdent quote Name Term Ident TSyntax)
open _root_.Lean.Elab.Command (CommandElabM CommandElab elabCommand)

/-- The types of a law's variables, by the same inference a theorem's get. -/
def lawTys (l : Law) : Tys := theoremTys [] [unMVar l.stmt]

/-- The statement of a law's twin: `∀ vars, law`. -/
def twinStatement (l : Law) : CommandElabM Term := do
  let env := lawTys l
  let body ← term { env := env, prog := {} } .boolean (unMVar l.stmt)
  l.vars.foldrM (fun v acc => do
    let ty ← leanTy ((env.lookup v).getD .boolean)
    `(∀ $(ident v):ident : $ty, $acc)) body

/-- Whether the translation can state a law: no quantifier. -/
def twinnable (l : Law) : Bool := !l.twin.isEmpty && noQuant l.stmt
where
  noQuant : Expr → Bool
    | .quant .. => false
    | .neg a => noQuant a
    | .bin _ l r => noQuant l && noQuant r
    | .cond c x y => noQuant c && noQuant x && noQuant y
    | _ => true

/-- `netty_twins boolean` states and proves the twin of every law of a shipped
law list. -/
syntax (name := nettyTwins) "netty_twins " ident : command

open _root_.Lean Elab Command in
@[command_elab nettyTwins] def elabNettyTwins : CommandElab := fun stx => do
  let list := stx[1].getId.toString
  let some laws := Proof.shipped list | throwError s!"no shipped law list ‘{list}’"
  for l in laws do
    if !twinnable l then continue
    let st ← twinStatement l
    let nm := mkIdent (Name.mkSimple ((l.twin.splitOn ".").getLast!))
    let doc := mkNode ``Lean.Parser.Command.docComment
      #[mkAtom "/--", mkAtom s!"{l.name}: {l.stmt.render} -/"]
    let cmd ← `(command|
      $(⟨doc⟩):docComment theorem $nm:ident : $st := by
        intros
        first
          | grind
          | omega
          | (simp only [Netty.Calc.Imp, Netty.Calc.Rimp] at *; grind))
    elabCommand cmd

end Netty.ToLean

namespace Netty.Twin.boolean
netty_twins boolean
end Netty.Twin.boolean

namespace Netty.Twin.number
netty_twins number
end Netty.Twin.number

/-! ### `law`: a law of the lists as a tactic

`law "duality"` closes a goal, or rewrites it, with the twins of the laws of that
name: a law, as Netty states it, used as a tactic in an ordinary Lean proof. It
tries each twin in turn — applied outright, as an equation rewritten left to right
or right to left, or as a simplification — and fails when none of them does. -/

namespace Netty.ToLean

/-- `law "NAME"` proves or rewrites the goal by a law of the shipped lists. -/
syntax (name := lawTac) "law " str : tactic

open _root_.Lean Elab Tactic in
@[tactic lawTac] def evalLaw : Tactic := fun stx => do
  let name := (stx[1].isStrLit?).getD ""
  let laws := (Laws.boolean ++ Laws.number).filter fun l => l.name == name && twinnable l
  if laws.isEmpty then throwError s!"there is no law ‘{name}’ with a Lean twin"
  let mut alts : Array (TSyntax `tactic) := #[]
  for l in laws do
    let id := mkIdent l.twin.toName
    alts := alts ++ #[
      ← `(tactic| (apply $id <;> assumption)),
      ← `(tactic| (rw [$id:ident]; done)),
      ← `(tactic| (rw [← $id:ident]; done)),
      ← `(tactic| (simp only [$id:ident]; done)),
      ← `(tactic| rw [$id:ident]),
      ← `(tactic| rw [← $id:ident])]
  let seqs ← alts.mapM fun a => `(Lean.Parser.Tactic.tacticSeq| $a:tactic)
  evalTactic (← `(tactic| first $[| $seqs]*))

end Netty.ToLean
