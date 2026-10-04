import LaPToP.ProgramTheory.InterpreterLang

/-!
# The statements the b4 compiler takes

The part of the interpreter's language that `CompileB4` compiles, as syntax: the
parser builds it beside each program it reads (when the program is in this
part), and `Stmt.toProg` is that program. Calls go to named statements, as the
parser's do-loops, for-loops and procedures do; `scope` is a local variable
(`new x := e in P end`), as parameters and simultaneous assignments use.
-/

namespace LaPToP.ProgramTheory.CompileB4

open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Lang

/-- The statements the compiler takes: the integer fragment of the language. -/
inductive Stmt where
  /-- `ok`. -/
  | ok
  /-- `x:= e`. -/
  | assign (x : ℕ) (e : Exp)
  /-- `P. Q`. -/
  | seq (p q : Stmt)
  /-- `if c then P else Q fi`. -/
  | cond (c : Exp) (p q : Stmt)
  /-- `while c do P od`. -/
  | loop (c : Exp) (p : Stmt)
  /-- `t:= t+1`. -/
  | tick
  /-- `c! e`, on channel number `c`. -/
  | send (c : ℕ) (e : Exp)
  /-- `c?. x:= c`: input on channel number `c`, kept in `x`. -/
  | recv (c : ℕ) (x : ℕ)
  /-- A call of named statement `k`. -/
  | call (k : ℕ)
  /-- `new x := e in P end`: `x` holds `e` while `P` runs, and gets its value back
  after. -/
  | scope (x : ℕ) (e : Exp) (p : Stmt)
  /-- The end of a call (in a running process: where it returns). -/
  | ret
  /-- The end of a scope (in a running process: `x` gets back `v`). -/
  | restore (x : ℕ) (v : Value)
  /-- `x:= √c`, on channel number `c`: whether the next message has arrived. -/
  | check (c : ℕ) (x : ℕ)
  /-- `A i:= e`, on an array variable `A`. -/
  | store (x : ℕ) (i e : Exp)
  /-- `P or Q`, the choice of Section 5.4.0, resolved by backtracking. -/
  | choice (p q : Stmt)
  /-- `ensure c`: go on if `c`, and otherwise back up to the last choice. -/
  | ensure (c : Exp)
  /-- `A:= [e₀; …; eₖ₋₁]`, on an array variable `A` of `k` cells. -/
  | fill (x : ℕ) (es : List Exp)
  /-- `if a/b then P else Q fi`, the probabilistic choice of Section 5.7. The
  compiler takes it once it is made deterministic over a seed (`CompileProb`). -/
  | prob (a b : Exp) (p q : Stmt)
  /-- A run-time check the compiler puts in: go on if `c`; if not, the machine
  stops with a fault. As a program it is `ok`. -/
  | guard (c : Exp)
  deriving Repr, DecidableEq

/-- A statement as a program of the language. -/
def Stmt.toProg : Stmt → P
  | .ok => .ok
  | .assign x e => Lang.assign x e
  | .seq p q => .seq p.toProg q.toProg
  | .cond c p q => ifThen c p.toProg q.toProg
  | .loop c p => Lang.loop c p.toProg
  | .tick => .tick
  -- Communication means something only in a network (`CompileNet`); alone, it has
  -- no behaviour.
  | .send _ _ | .recv _ _ | .check _ _ => .ensure fun _ => false
  -- `A i j:= e` is kept with the path as a list literal, `[i; j]`
  | .store x i e => assignIdx x (i.items?.getD [i]) e
  | .choice p q => .or p.toProg q.toProg
  | .ensure c => Lang.ensure c
  | .fill x es => Lang.assign x (Exp.ofList es)
  | .prob a b p q => probIf a b p.toProg q.toProg
  | .call k => .call k
  | .scope x e p => declare x e p.toProg
  | .ret => .ok
  | .restore x v => .assign x fun _ => v
  | .guard _ => .ok

/-- A statement with no communication: `toProg` means it (the parser's program
for a communication is the network's mark, `netSend`, `netRecv`, `netCheck`). -/
def Stmt.commFree : Stmt → Bool
  | .send _ _ | .recv _ _ | .check _ _ => false
  | .seq p q | .cond _ p q | .choice p q | .prob _ _ p q => p.commFree && q.commFree
  | .loop _ p | .scope _ _ p => p.commFree
  | _ => true

/-- The body of `x:= rand n` as a statement (`Lang.randBody`). -/
def randStmt (k x hn hi : ℕ) : Stmt :=
  .cond (.bin .ge (.var hi) (.bin .sub (.var hn) (.lit (.int 1)))) (.assign x (.var hi))
    (.prob (.lit (.int 1)) (.bin .sub (.var hn) (.var hi)) (.assign x (.var hi))
      (.seq (.assign hi (.bin .add (.var hi) (.lit (.int 1)))) (.call k)))

theorem randStmt_toProg (k x hn hi : ℕ) : (randStmt k x hn hi).toProg = randBody k x hn hi := rfl

end LaPToP.ProgramTheory.CompileB4
