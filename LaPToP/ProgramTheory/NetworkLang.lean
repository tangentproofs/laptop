import LaPToP.ProgramTheory.Network
import LaPToP.ProgramTheory.InterpreterLangSyntax

/-!
# Networks in the concrete syntax

A program with channels and a `||` (or any program, given `interp --net`) is a
network of communicating processes (`Network`): the processes of the top-level
`||` run concurrently, each with its own copy of the variables, and communicate
only through channels — `c! e` outputs on `c`, `c?` inputs from it, and `c` is
the last message input. Each channel has one writer and may have many readers
(broadcast); a channel no process writes carries the input the command line
gives it, all sent at time `0`.

The parser marks output and input (`netSend`, `netRecv`); `toNet` reads the
marks back as the network's `send` and `recv`, and every stretch of program
between them becomes a chunk run in one step. The network is then run by
`Network.runNet`, whose result, when every process finishes, is the book's
semantics (`Network.runNet_correct`), whatever the order the processes run in.

A local variable around input or output (as a `for` loop's index is) stays a
scope of the process (`NProc.scope`). `√c` is the book's timed check, `T r + 1 ≤ t`:
the parser puts a check (`NProc.check`) before the statement that reads it, which
keeps the answer in a hidden variable; the check waits until the answer is
settled, whatever the speed of the other processes. Not yet expressible in a
network: a choice, or a `||` around input or output.
-/

namespace LaPToP.ProgramTheory.Interpreter.Lang

open Network
open LaPToP.ProgramTheory.Interpreter.Demo (Tok Toks)

/-- The channel whose output mark is on variable `x`. -/
def sendChan (chans : List (String × ℕ × ℕ)) (x : ℕ) : Option ℕ := chans.findIdx? (·.2.2 == x)

/-- The channel whose input mark is on variable `x`. -/
def recvChan (chans : List (String × ℕ × ℕ)) (x : ℕ) : Option ℕ := chans.findIdx? (·.2.1 == x)

/-- The communication a program does, directly or through the specifications it
calls (`look`): each channel it outputs on (`true`) or inputs from (`false`). -/
def comms (chans : List (String × ℕ × ℕ)) (rdy : List ℕ) (look : ℕ → List (Bool × ℕ)) :
    P → List (Bool × ℕ)
  | .newLocal x _ p =>
    (match sendChan chans x, recvChan chans x, rdy.idxOf? x, p with
      | some c, _, _, .ok => [(true, c)]
      | _, some c, _, .ok => [(false, c)]
      | _, _, some c, .ok => [(false, c)]
      | _, _, _, _ => []) ++ comms chans rdy look p
  | .seq p q => comms chans rdy look p ++ comms chans rdy look q
  | .cond _ p q => comms chans rdy look p ++ comms chans rdy look q
  | .or p q => comms chans rdy look p ++ comms chans rdy look q
  | .par _ p q => comms chans rdy look p ++ comms chans rdy look q
  | .prob _ p q => comms chans rdy look p ++ comms chans rdy look q
  | .whileDo _ p => comms chans rdy look p
  | .call k => look k
  | _ => []

/-- The communication each specification does, through the calls it makes: the
least solution, by iteration from nothing. -/
def commsOfDefs (chans : List (String × ℕ × ℕ)) (rdy : List ℕ) (defs : List (ℕ × P)) :
    ℕ → List (ℕ × List (Bool × ℕ)) → List (ℕ × List (Bool × ℕ))
  | 0, w => w
  | f + 1, w =>
    let look := fun k => (w.lookup k).getD []
    let w' := defs.map fun (k, b) => (k, (comms chans rdy look b).eraseDups)
    if w' == w then w else commsOfDefs chans rdy defs f w'

/-- A program as a process: the marks become output and input, the structure
around them stays, and what does not communicate is a chunk. -/
def toNP (chans : List (String × ℕ × ℕ)) (rdy : List ℕ) (look : ℕ → List (Bool × ℕ)) :
    P → Except String (NProc ℕ Value)
  | .newLocal x e p =>
    match sendChan chans x, recvChan chans x, rdy.idxOf? x, p with
    | some c, _, _, .ok => .ok (.send c e)
    | _, some c, _, .ok => .ok (.recv c x)
    | _, _, some c, .ok => .ok (.check c x .bool)
    | _, _, _, p =>
      if (comms chans rdy look p).isEmpty then .ok (.act (.newLocal x e p))
      else do .ok (.scope x e (← toNP chans rdy look p))
  | .seq p q =>
    if (comms chans rdy look (.seq p q)).isEmpty then .ok (.act (.seq p q))
    else do .ok (.seq (← toNP chans rdy look p) (← toNP chans rdy look q))
  | .cond b p q =>
    if (comms chans rdy look (.cond b p q)).isEmpty then .ok (.act (.cond b p q))
    else do .ok (.cond b (← toNP chans rdy look p) (← toNP chans rdy look q))
  | .whileDo b p =>
    if (comms chans rdy look p).isEmpty then .ok (.act (.whileDo b p))
    else do .ok (.loop b (← toNP chans rdy look p))
  | .call k => .ok (if (look k).isEmpty then .act (.call k) else .call k)
  | .or p q =>
    if (comms chans rdy look (.or p q)).isEmpty then .ok (.act (.or p q))
    else .error "a choice ('or') around input or output is not supported in a network"
  | .prob r p q =>
    if (comms chans rdy look (.prob r p q)).isEmpty then .ok (.act (.prob r p q))
    else .error "a probabilistic choice around input or output is not supported in a network"
  | .par own p q =>
    if (comms chans rdy look (.par own p q)).isEmpty then .ok (.act (.par own p q))
    else .error "a || of communicating processes must be the whole main program: \
      parenthesize each process, as in (c! 1. c! 2) || (c?. x:= c)"
  | p => .ok (.act p)

/-- The processes of the top-level `||`. -/
def procsOf : P → List P
  | .par _ p q => procsOf p ++ procsOf q
  | p => [p]

/-- A parsed program as a network. -/
structure NetProgram where
  /-- The network. -/
  net : Net ℕ Value
  /-- The channels: name, variable, cursor variable. -/
  chans : List (String × ℕ × ℕ)
  /-- The variables each process may assign. -/
  owners : List (List ℕ)

/-- The network a parsed program is, from the prestate `s`, which gives the
input on the channels no process writes. -/
def toNet (prog : Program) (chans : List (String × ℕ × ℕ)) (s : St) :
    Except String NetProgram := do
  -- the variable that keeps each channel's `√c`
  let rdy := chans.map fun (c, _, _) => prog.names.idxOf ("#" ++ c ++ ".ready")
  let w := commsOfDefs chans rdy prog.defs (prog.defs.length * (2 * chans.length + 1) + 1) []
  let look := fun k => (w.lookup k).getD []
  let defs ← prog.defs.mapM fun (k, b) => do .ok (k, ← toNP chans rdy look b)
  let ps := procsOf prog.main
  let bodies ← ps.mapM (toNP chans rdy look)
  let cs := ps.map (comms chans rdy look)
  let outs := cs.map fun l => (l.filterMap fun (b, c) => if b then some c else none).eraseDups
  let ins := cs.map fun l => (l.filterMap fun (b, c) => if b then none else some c).eraseDups
  let name := fun (c : ℕ) => (chans[c]?.map (·.1)).getD "?"
  let script := fun (c : ℕ) => match chans[c]? with
    | some (_, M, _) => (s M).toList
    | none => []
  if let some c := (List.range chans.length).find? fun c =>
      (outs.filter (·.contains c)).length > 1 then
    throw s!"channel {name c} is written by two processes"
  if let some c := (List.range chans.length).find? fun c =>
      outs.any (·.contains c) && !(script c).isEmpty then
    throw s!"channel {name c} is written by a process, so it cannot also be given input"
  let pw := procWrites prog.defs (prog.defs.length * (prog.names.length + 1) + 1) []
  let lookW := fun k => (pw.lookup k).getD []
  .ok {
    net := ⟨fun k => (defs.lookup k).getD (.act (.ensure fun _ => false)),
      (bodies.zip (outs.zip ins)).map fun ((b, o, i) : NProc ℕ Value × List ℕ × List ℕ) =>
        (⟨b, o, i⟩ : Proc ℕ Value),
      fun c => if outs.any (·.contains c) then [] else (script c).map fun v => (v, 0)⟩
    chans := chans
    owners := ps.map (assigned lookW) }

/-- How a run of a network ended. -/
inductive NetStatus where
  /-- Every process finished. -/
  | done
  /-- No process can move, and some have not finished: they wait for input that
  never comes, so (`Network.deadlock_top`) the book's time is `∞`. -/
  | deadlock
  /-- The rounds ran out with processes still moving. -/
  | running
  deriving DecidableEq, Repr

/-- Run a network for at most `rounds` rounds, each chunk with fuel `fuel`. -/
def NetProgram.run (np : NetProgram) (prog : Program) (fuel rounds : ℕ) (s : St) :
    MCfg ℕ Value × NetStatus :=
  letI := prog.env
  let c := runNet np.net fuel rounds (np.net.init s 0)
  (c, if c.done then .done else if (sweep np.net fuel c).2 then .running else .deadlock)

/-- A variable after the run: the value the process that may assign it has, or
the initial one. -/
def NetProgram.value (np : NetProgram) (c : MCfg ℕ Value) (s : St) (x : ℕ) : Value :=
  match np.owners.findIdx? (·.contains x) with
  | some i => (c.ps[i]?.map fun pc => pc.st.mem x).getD (s x)
  | none => s x

/-- The time a run ends: when the last process does. -/
def finishTime (c : MCfg ℕ Value) : ℕ∞ := c.ps.foldl (fun t pc => max t pc.st.t) 0

/-- What a run of a network shows. -/
structure NetOutcome where
  /-- How it ended. -/
  status : NetStatus
  /-- The time it ended. -/
  time : ℕ∞
  /-- Each variable that is not a channel's or hidden. -/
  vars : List (String × Value)
  /-- Each channel's script: the messages, with the times they were sent. -/
  scripts : List (String × List (Value × ℕ∞))
  deriving DecidableEq

/-- What a run shows. -/
def NetProgram.outcome (np : NetProgram) (prog : Program) (fuel rounds : ℕ) (s : St) :
    NetOutcome :=
  let (c, st) := np.run prog fuel rounds s
  ⟨st, finishTime c,
    (prog.names.zipIdx.filter fun (w, k) =>
        !w.startsWith "#" && !np.chans.any (·.2.1 == k)).map fun (w, k) => (w, np.value c s k),
    np.chans.zipIdx.map fun ((w, _, _), c') => (w, c.L c')⟩

/-- Parse tokens as a network and run it from `s`. -/
def netOutcome (net : Bool) (names : List String) (ts : Toks) (s : St) (fuel rounds : ℕ) :
    Except String NetOutcome := do
  let prog ← parseToksMode net names ts
  let np ← toNet prog (chansOf names ts) s
  .ok (np.outcome prog fuel rounds s)

namespace Demo

/-- `c! 2 || (c?. x:= c)`. -/
def sendRecvSrc : String := "c! 2 || (c?. x:= c)"

/-- Its tokens. -/
def sendRecvToks : Toks :=
  [.word "c", .sym "!", .num 2, .sym "||", .sym "(", .word "c", .sym "?", .sym ".",
   .word "x", .sym ":=", .word "c", .sym ")"]

/-- The message arrives one unit of time after it is sent (§9.1.2). -/
theorem sendRecv_net :
    netOutcome false [] sendRecvToks init 100 100 =
      .ok ⟨.done, 1, [("x", .int 2)], [("c", [(.int 2, 0)])]⟩ := by
  decide +kernel

/-- The buffer: `(c! 3. tick. c! 4) || (c?. y:= c. c?. x:= c)`. -/
def bufferSrc : String := "(c! 3. tick. c! 4) || (c?. y:= c. c?. x:= c)"

/-- Its tokens. -/
def bufferToks : Toks :=
  [.sym "(", .word "c", .sym "!", .num 3, .sym ".", .word "tick", .sym ".", .word "c", .sym "!",
   .num 4, .sym ")", .sym "||", .sym "(", .word "c", .sym "?", .sym ".", .word "y", .sym ":=", .word "c", .sym ".",
   .word "c", .sym "?", .sym ".", .word "x", .sym ":=", .word "c", .sym ")"]

/-- The reader has the second message at time `2`: it was sent at `1`. -/
theorem buffer_net :
    netOutcome false [] bufferToks init 100 100 =
      .ok ⟨.done, 2, [("y", .int 3), ("x", .int 4)], [("c", [(.int 3, 0), (.int 4, 1)])]⟩ := by
  decide +kernel

/-- The deadlock of §9.1.8: `(c?. d! 2) || (d?. c! 1)`. -/
def deadlockSrc : String := "(c?. d! 2) || (d?. c! 1)"

/-- Its tokens. -/
def deadlockToks : Toks :=
  [.sym "(", .word "c", .sym "?", .sym ".", .word "d", .sym "!", .num 2, .sym ")", .sym "||",
   .sym "(", .word "d", .sym "?", .sym ".", .word "c", .sym "!", .num 1, .sym ")"]

/-- Each waits for the other: deadlock, and nothing is ever sent. -/
theorem deadlock_net :
    netOutcome false [] deadlockToks init 100 100 = .ok ⟨.deadlock, 0, [], [("c", []), ("d", [])]⟩ := by
  decide +kernel

/-- The doubler, `S ⇐ c?. d! 2×c. S`, a process that never finishes, run as a
network on input from the command line. -/
def doublerSrc : String := "S ⇐ c?. d! 2×c. S"

/-- Its tokens. -/
def doublerToks : Toks :=
  [.word "S", .sym "<==", .word "c", .sym "?", .sym ".", .word "d", .sym "!", .num 2, .sym "*",
   .word "c", .sym ".", .word "S"]

/-- On input `[1; 2; 5]` it outputs `[2; 4; 10]`, each one unit after its input,
and then waits for more. -/
theorem doubler_net :
    (netOutcome true ["c"] doublerToks
      (Function.update init 0 (.list [.int 1, .int 2, .int 5])) 100 100).map
        (fun o => (o.status, o.time, o.scripts.lookup "d")) =
      .ok (.deadlock, 1, some [(.int 2, 1), (.int 4, 1), (.int 10, 1)]) := by
  decide +kernel

/-- A pipeline of three:
`(c! 1. c! 2) || (c?. d! c+10. c?. d! c+10) || (d?. x:= d. d?. y:= d)`. -/
def pipelineSrc : String := "(c! 1. c! 2) || (c?. d! c+10. c?. d! c+10) || (d?. x:= d. d?. y:= d)"

/-- Its tokens. -/
def pipelineToks : Toks :=
  [.sym "(", .word "c", .sym "!", .num 1, .sym ".", .word "c", .sym "!", .num 2, .sym ")",
   .sym "||",
   .sym "(", .word "c", .sym "?", .sym ".", .word "d", .sym "!", .word "c", .sym "+", .num 10,
   .sym ".", .word "c", .sym "?", .sym ".", .word "d", .sym "!", .word "c", .sym "+", .num 10,
   .sym ")", .sym "||",
   .sym "(", .word "d", .sym "?", .sym ".", .word "x", .sym ":=", .word "d", .sym ".",
   .word "d", .sym "?", .sym ".", .word "y", .sym ":=", .word "d", .sym ")"]

/-- Each stage adds one unit of transit time. -/
theorem pipeline_net :
    netOutcome false [] pipelineToks init 100 100 =
      .ok ⟨.done, 2, [("x", .int 11), ("y", .int 12)],
        [("c", [(.int 1, 0), (.int 2, 0)]), ("d", [(.int 11, 1), (.int 12, 1)])]⟩ := by
  decide +kernel

/-- Polling with `√c` (§9.1.4): the reader, from time `4`, takes the messages
that have arrived — sent at `1` and `2`, both before `4` — and stops at the first
`√c` that is false. -/
def pollSrc : String :=
  "(tick. c! 5. tick. c! 6) || (tick. tick. tick. tick. n:= 0. while √c do c?. n:= n + c od)"

/-- Its tokens. -/
def pollToks : Toks :=
  [.sym "(", .word "tick", .sym ".", .word "c", .sym "!", .num 5, .sym ".", .word "tick",
   .sym ".", .word "c", .sym "!", .num 6, .sym ")", .sym "||",
   .sym "(", .word "tick", .sym ".", .word "tick", .sym ".", .word "tick", .sym ".",
   .word "tick", .sym ".", .word "n", .sym ":=", .num 0, .sym ".", .word "while", .sym "√",
   .word "c", .word "do", .word "c", .sym "?", .sym ".", .word "n", .sym ":=", .word "n",
   .sym "+", .word "c", .word "od", .sym ")"]

/-- `n = 11` at time `4`: whether a message has arrived is settled by the times,
whatever the speed of the processes. -/
theorem poll_net :
    netOutcome false [] pollToks init 100 100 =
      .ok ⟨.done, 4, [("n", .int 11)], [("c", [(.int 5, 1), (.int 6, 2)])]⟩ := by
  decide +kernel

/-- The networks the self-test checks the tokenizer on. -/
def netSelfTests : List (String × String × Toks) :=
  [("sendRecv", sendRecvSrc, sendRecvToks), ("buffer", bufferSrc, bufferToks),
   ("deadlock", deadlockSrc, deadlockToks), ("doubler", doublerSrc, doublerToks),
   ("pipeline", pipelineSrc, pipelineToks), ("poll", pollSrc, pollToks)]

end Demo

end LaPToP.ProgramTheory.Interpreter.Lang
