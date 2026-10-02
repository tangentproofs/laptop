import LaPToP.ProgramTheory.CompileNet
import LaPToP.ProgramTheory.NetworkLang

/-!
# Running the language on b4 (`interp --b4`)

The part of the language the b4 compiler takes — `ok`, `tick`, `x:= e`, `if`,
`while`, `do`/`exit` loops, `for` loops, `new x := e in P end`, simultaneous
assignment, specifications with parameters and recursion, `c! e`, `c?`, and a
`||` of processes as the whole program — read by the language's own parser,
which builds the compiler's statements (`CompileB4.Stmt`) beside each program it
reads (`parseToksShadow`), compiled, and run: a single program on one b4
machine, a network on a swarm (`B4.Swarm`). Named statements are laid out from
`0x100` and called with `cl`; local variables keep their old values on the
control stack. `≠ ≤ > ≥` are rewritten into `= <` and `¬`, which the compiler
handles. What the machine computes is, by `CompileB4.load_correct` and
`CompileNet.swarm_correct`, what the language computes, as long as no value
leaves 32 bits; `interp --selftest` also compares the two on the demonstrations.
-/

namespace LaPToP.ProgramTheory.Interpreter.Lang

open LaPToP.ProgramTheory.Interpreter.Demo (Tok Toks)
open LaPToP.ProgramTheory.CompileB4 LaPToP.ProgramTheory.CompileNet B4

/-- An expression in the operators the compiler takes, or why not. -/
def Exp.toB4 : Exp → Except String Exp
  | .lit (.int k) => .ok (.lit (.int k))
  | .lit (.bool b) => .ok (.lit (.bool b))
  | .var x => .ok (.var x)
  | .un .neg a => do .ok (.un .neg (← a.toB4))
  | .un .not a => do .ok (.un .not (← a.toB4))
  | .bin op a b => do
    let a ← a.toB4
    let b ← b.toB4
    match op with
    | .add | .sub | .mul | .div | .mod | .eq | .lt => .ok (.bin op a b)
    | .ne => .ok (.un .not (.bin .eq a b))
    | .le => .ok (.un .not (.bin .lt b a))
    | .gt => .ok (.bin .lt b a)
    | .ge => .ok (.un .not (.bin .lt a b))
    | _ => .error "the b4 compiler takes only + - × div mod = ≠ < ≤ > ≥ ¬ on integers and binaries"
  | .index (.var x) i => do .ok (.index (.var x) (← i.toB4))
  | _ => .error "the b4 compiler takes only integers, binaries, variables and items of arrays"

/-- A statement's expressions in the operators the compiler takes, or why not. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.toB4 : Stmt → Except String Stmt
  | .assign x e => do .ok (.assign x (← e.toB4))
  | .seq p q => do .ok (.seq (← p.toB4) (← q.toB4))
  | .cond c p q => do .ok (.cond (← c.toB4) (← p.toB4) (← q.toB4))
  | .loop c p => do .ok (.loop (← c.toB4) (← p.toB4))
  | .send ch e => do .ok (.send ch (← e.toB4))
  | .scope x e p => do .ok (.scope x (← e.toB4) (← p.toB4))
  | .store x i e => do .ok (.store x (← i.toB4) (← e.toB4))
  | s => .ok s

/-- A program for b4: its processes (one, if there is no `||`), the named
statements they call, its variables, and its channels. -/
structure B4Program where
  /-- The processes. -/
  procs : List Stmt
  /-- The named statements. -/
  defs : List (ℕ × Stmt)
  /-- The variables: variable `k` is written `names[k]`. -/
  names : List String
  /-- The channels: name, variable, (unused) cursor variable. -/
  chans : List (String × ℕ × ℕ)

/-- Read a program for b4, the names given on the command line first, through the
language's own parser (`parseToksShadow`), after checking it as the interpreter
does. -/
def parseB4 (names : List String) (ts : Toks) : Except String B4Program := do
  let _ ← parseToksMode true names ts
  let sh ← parseToksShadow names ts
  .ok ⟨← sh.procs.mapM Stmt.toB4, ← sh.defs.mapM fun (k, p) => do .ok (k, ← p.toB4), sh.names,
    sh.chans⟩

/-! ### Running -/

/-- The variables a statement may assign, given those each named statement may.
A scope hides its own variable. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.writes (look : ℕ → List ℕ) : Stmt → List ℕ
  | .assign x _ | .store x _ _ => [x]
  | .recv _ x | .check _ x => [x]
  | .seq p q | .cond _ p q => p.writes look ++ q.writes look
  | .loop _ p => p.writes look
  | .scope x _ p => (p.writes look).filter (· != x)
  | .call k => look k
  | _ => []

/-- The channels a statement outputs on (`true`) or inputs from, given those of
each named statement. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.comms (look : ℕ → List (Bool × ℕ)) :
    Stmt → List (Bool × ℕ)
  | .send c _ => [(true, c)]
  | .recv c _ | .check c _ => [(false, c)]
  | .seq p q | .cond _ p q => p.comms look ++ q.comms look
  | .loop _ p | .scope _ _ p => p.comms look
  | .call k => look k
  | _ => []

/-- Close a property of named statements under the calls they make: the least
solution, by iteration from nothing. -/
def closeDefs {α : Type} [BEq α] (defs : List (ℕ × Stmt)) (f : (ℕ → List α) → Stmt → List α) :
    ℕ → List (ℕ × List α) → List (ℕ × List α)
  | 0, w => w
  | n + 1, w =>
    let look := fun k => (w.lookup k).getD []
    let w' := defs.map fun (k, b) => (k, (f look b).eraseDups)
    if w' == w then w else closeDefs defs f n w'

/-- What each named statement may assign. -/
def B4Program.writesLook (bp : B4Program) : ℕ → List ℕ :=
  let w := closeDefs bp.defs Stmt.writes (bp.defs.length * (bp.names.length + 1) + 1) []
  fun k => (w.lookup k).getD []

/-- Where each named statement communicates. -/
def B4Program.commsLook (bp : B4Program) : ℕ → List (Bool × ℕ) :=
  let w := closeDefs bp.defs Stmt.comms (bp.defs.length * (2 * bp.chans.length + 1) + 1) []
  fun k => (w.lookup k).getD []

/-- Whether an expression is a binary, by its form. -/
def Exp.isBin : Exp → Bool
  | .lit (.bool _) | .un .not _ => true
  | .bin op _ _ => op == .eq || op == .lt
  | _ => false

/-- The expressions a statement assigns to `x`. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.assignsTo (x : ℕ) : Stmt → List Exp
  | .assign y e => if x = y then [e] else []
  | .seq p q | .cond _ p q => p.assignsTo x ++ q.assignsTo x
  | .loop _ p | .scope _ _ p => p.assignsTo x
  | _ => []

/-- A variable every assignment of which is a binary, so it is shown as one. -/
def B4Program.isBinVar (bp : B4Program) (x : ℕ) : Bool :=
  let es := (bp.procs ++ bp.defs.map (·.2)).flatMap (·.assignsTo x)
  !es.isEmpty && es.all Exp.isBin

/-- The variables an expression indexes. -/
def Exp.arrs : Exp → List ℕ
  | .index (.var x) i => x :: i.arrs
  | .index a i => a.arrs ++ i.arrs
  | .bin _ a b => a.arrs ++ b.arrs
  | .un _ a => a.arrs
  | _ => []

/-- The variables a statement uses as arrays. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.arrs : Stmt → List ℕ
  | .assign _ e | .send _ e => e.arrs
  | .store x i e => x :: i.arrs ++ e.arrs
  | .seq p q => p.arrs ++ q.arrs
  | .cond c p q => c.arrs ++ p.arrs ++ q.arrs
  | .loop c p => c.arrs ++ p.arrs
  | .scope _ e p => e.arrs ++ p.arrs
  | _ => []

/-- The variables a statement gives a whole new value: by assignment, input, or
a scope. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.wholes : Stmt → List ℕ
  | .assign x _ | .recv _ x | .check _ x => [x]
  | .seq p q | .cond _ p q => p.wholes ++ q.wholes
  | .loop _ p => p.wholes
  | .scope x _ p => x :: p.wholes
  | _ => []

/-- The array variables, each with as many cells as its list starts with. -/
def B4Program.arrays (bp : B4Program) (s : St) : List (ℕ × ℕ) :=
  ((bp.procs ++ bp.defs.map (·.2)).flatMap Stmt.arrs).eraseDups.map fun x => (x, (s x).toList.length)

/-- The layout: the named statements from `0x100`, each process's code after
them, the variables' cells above the longest, then the arrays'. -/
def B4Program.layout (bp : B4Program) (s : St) : Layout :=
  let L₀ := Layout.build 0 bp.names.length bp.defs (bp.arrays s)
  Layout.build (L₀.start + (bp.procs.map (slen L₀ ·)).foldl max 0 + 16) bp.names.length bp.defs
    (bp.arrays s)

/-- The network the processes make, with the command line's input on the
channels no process writes. -/
def B4Program.toSNet (bp : B4Program) (s : St) : SNet :=
  let cs := bp.procs.map (·.comms bp.commsLook)
  let outs := cs.map fun l => (l.filterMap fun (b, c) => if b then some c else none).eraseDups
  { procs := (bp.procs.zip (outs.zip cs)).map fun (p, o, l) =>
      ⟨p, o, (l.filterMap fun (b, c) => if b then none else some c).eraseDups⟩
    input := fun c => if outs.any (·.contains c) then [] else
      match bp.chans[c]? with
      | some (_, M, _) => (s M).toList.map fun v => (v, 0)
      | none => []
    defs := fun k => (bp.defs.lookup k).getD .ok }

/-- How a run on b4 ended. -/
inductive B4Status where
  /-- Every machine halted. -/
  | halted
  /-- No machine can move, and some have not halted: a deadlock. -/
  | deadlock
  /-- The fuel ran out. -/
  | running
  deriving DecidableEq, Repr

/-- A word as an integer. -/
def B4Program.value (w : UInt32) : ℤ := toInt32 w

/-- What a run on b4 shows: how it ended, the time, each variable that is not
hidden or a channel's, and each channel's script. -/
structure B4Outcome where
  /-- How it ended. -/
  status : B4Status
  /-- The time it ended (when the last machine did). -/
  time : ℕ
  /-- The variables. -/
  vars : List (String × ℤ)
  /-- The scripts, values with the times they were sent. -/
  scripts : List (String × List (ℤ × ℕ))
  /-- The arrays. -/
  arrays : List (String × List ℤ) := []
  deriving DecidableEq, Repr

/-- A value as b4 holds it, read back as an integer: a binary is `-1` or `0`. -/
def Value.b4Int : Value → ℤ
  | .int k => k
  | .bool b => if b then -1 else 0
  | .list _ => 0

/-- Run on b4: compile and load each process, run the swarm (a lone process is a
swarm of one), and read back the result. -/
def B4Program.run (bp : B4Program) (s : St) (fuel : ℕ) : Except String B4Outcome := do
  let L := bp.layout s
  let name := fun x => bp.names.getD x "?"
  for (x, _) in L.arrays do
    match s x with
    | .list _ => pure ()
    | _ => throw s!"{name x} is used as an array, so it must start as a list"
    if (bp.procs ++ bp.defs.map (·.2)).any (·.wholes.contains x) then
      throw s!"the b4 compiler changes the array {name x} only item by item, not as a whole"
  if !(L.base + 4 * L.n + 4 * cellsOf L.arrays + 16 ≤ MAXBYTE) then
    throw "the program and its variables do not fit in b4's 64 KB"
  let net := bp.toSNet s
  for c in [0:bp.chans.length] do
    if (net.procs.filter fun pr => pr.outs.contains c).length > 1 then
      throw s!"channel {(bp.chans[c]?.map (·.1)).getD "?"} is written by two processes"
  let w := (net.load L s).runK fuel
  let st :=
    if w.ms.all (getRST · != 1) then B4Status.halted
    else if w.sweep.2 || w.settle.isSome then .running else .deadlock
  let owner := fun x => bp.procs.findIdx? (·.writes bp.writesLook |>.contains x)
  let value := fun x => match owner x with
    | some i => ((w.ms[i]?).map fun m => B4Program.value (getVal m.mem (L.addr x))).getD 0
    | none => (s x).toInt
  let cells := fun x => match L.arrayAt x, owner x with
    | some (a₀, cap), some i => ((w.ms[i]?).map fun m =>
        (List.range cap).map fun j => B4Program.value (getVal m.mem (a₀ + 4 * j))).getD []
    | _, _ => (s x).toList.map Value.b4Int
  let isArr := fun k => L.arrays.any (·.1 == k)
  .ok ⟨st, (w.ms.map fun m => (getClk m).toNat).foldl max 0,
    (bp.names.zipIdx.filter fun (n, k) => !n.startsWith "#" && !bp.chans.any (·.2.1 == k) &&
      !isArr k).map fun (n, k) => (n, value k),
    bp.chans.zipIdx.map fun ((n, _, _), c) =>
      (n, (w.chans c).map fun (v, t) => (B4Program.value v, t.toNat)),
    (bp.names.zipIdx.filter fun (n, k) => !n.startsWith "#" && isArr k).map
      fun (n, k) => (n, cells k)⟩

/-- Parse and run on b4. -/
def b4Outcome (names : List String) (ts : Toks) (s : St) (fuel : ℕ) : Except String B4Outcome := do
  (← parseB4 names ts).run s fuel

/-- Whether the arrays a run on b4 shows are the lists `look` gives. -/
def B4Outcome.arraysAre (b : B4Outcome) (look : String → Option Value) : Bool :=
  b.arrays.all fun (n, l) => (look n).any fun v => l == v.toList.map Value.b4Int

/-- Whether a run on b4 shows what the network machine computed. -/
def B4Outcome.agrees (b : B4Outcome) (o : NetOutcome) : Bool :=
  (match o.status, b.status with
    | .done, .halted => b.time == o.time.toNat && o.time != ⊤
    | .deadlock, .deadlock => true
    | _, _ => false) &&
  b.vars == (o.vars.filter fun (n, _) => !b.arrays.any (·.1 == n)).map
    (fun (n, v) => (n, v.b4Int)) &&
  b.arraysAre (fun n => o.vars.lookup n) &&
  b.scripts == o.scripts.map (fun (n, l) => (n, l.map fun (v, t) => (v.b4Int, t.toNat)))

/-- Whether a run of a single program on b4 shows what the interpreter computed. -/
def B4Outcome.agreesWith (b : B4Outcome) (names : List String) (s : St) : Bool :=
  b.status == .halted &&
    b.vars == (names.zipIdx.filter fun (n, _) => !n.startsWith "#" && !b.arrays.any (·.1 == n)).map
      (fun (n, k) => (n, (s k).b4Int)) &&
    b.arraysAre fun n => (names.idxOf? n).map s

namespace Demo

#eval b4Outcome ["n"] sumToToks (fun x => if x = 0 then .int 10 else .int 0) 10000
#eval b4Outcome [] sendRecvToks init 1000
#eval b4Outcome [] bufferToks init 1000
#eval b4Outcome [] pipelineToks init 1000
#eval b4Outcome [] deadlockToks init 1000
#eval b4Outcome ["n", "x"] exitLoopToks (fun x => if x = 0 then .int 5 else .int 0) 10000
#eval b4Outcome [] deepExitToks init 100000
#eval b4Outcome ["n"] forLoopToks (fun x => if x = 0 then .int 10 else .int 0) 100000
#eval b4Outcome ["x", "y"] gcdToks (fun x => if x = 0 then .int 12 else if x = 1 then .int 18 else .int 0) 100000
#eval b4Outcome ["x", "y"] swapToks (fun x => if x = 0 then .int 1 else if x = 1 then .int 2 else .int 0) 1000

end Demo

end LaPToP.ProgramTheory.Interpreter.Lang
