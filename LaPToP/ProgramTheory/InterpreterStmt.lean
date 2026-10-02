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
  | .store x i e => assignIdx x [i] e
  | .call k => .call k
  | .scope x e p => declare x e p.toProg
  | .ret => .ok
  | .restore x v => .assign x fun _ => v

end LaPToP.ProgramTheory.CompileB4
