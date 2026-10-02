import LaPToP.ProgramTheory.CompileNet
import LaPToP.ProgramTheory.NetworkLang

/-!
# Running the language on b4 (`interp --b4`)

The part of the concrete syntax the b4 compiler takes — `ok`, `tick`, `x:= e`,
`if`, `while`, parentheses, `c! e`, `c?`, and a `||` of processes as the whole
program — read into the compiler's statements (`CompileB4.Stmt`), compiled, and
run: a single program on one b4 machine, a network on a swarm (`B4.Swarm`).
The tokens, the variable table and the expressions are the interpreter's own
(`InterpreterLangSyntax`); `≠ ≤ > ≥` are rewritten into `= <` and `¬`, which the
compiler handles. What the machine computes is, by `CompileB4.load_correct` and
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
    | .add | .sub | .mul | .eq | .lt => .ok (.bin op a b)
    | .ne => .ok (.un .not (.bin .eq a b))
    | .le => .ok (.un .not (.bin .lt b a))
    | .gt => .ok (.bin .lt b a)
    | .ge => .ok (.un .not (.bin .lt a b))
    | _ => .error "the b4 compiler takes only + - × = ≠ < ≤ > ≥ ¬ on integers and binaries"
  | _ => .error "the b4 compiler takes only integers, binaries and variables, not lists"

private def expectTok (t : Tok) (st : PS) : Except String PS :=
  match st.toks with
  | u :: rest => if u == t then .ok (st.at rest) else .error s!"expected '{t.render}', found '{u.render}'"
  | [] => .error s!"expected '{t.render}', found the end of the program"

/-- The tokens that end a block. -/
def b4Ends : Toks → Bool
  | [] => true
  | .word "else" :: _ | .word "fi" :: _ | .word "od" :: _ | .sym ")" :: _ | .sym "||" :: _ => true
  | _ => false

mutual

/-- `program := statement ('.' statement)* '.'?`. -/
def b4Prog (fuel : ℕ) (st : PS) : Except String (Stmt × PS) :=
  match fuel with
  | 0 => .error "program too long"
  | f + 1 => do
    let (p, st) ← b4Stmt f st
    match st.toks with
    | .sym "." :: ts =>
      if b4Ends ts then .ok (p, st.at ts)
      else do
        let (q, st) ← b4Prog f (st.at ts)
        .ok (.seq p q, st)
    | _ => .ok (p, st)
termination_by structural fuel

/-- A statement. -/
def b4Stmt (fuel : ℕ) (st : PS) : Except String (Stmt × PS) :=
  match fuel with
  | 0 => .error "program too long"
  | f + 1 =>
    match st.toks with
    | .word "ok" :: ts => .ok (.ok, st.at ts)
    | .word "tick" :: ts => .ok (.tick, st.at ts)
    | .word "if" :: ts => do
      let (c, st) ← parseExp f (st.at ts)
      let c ← c.toB4
      let st ← expectTok (.word "then") st
      let (p, st) ← b4Prog f st
      match st.toks with
      | .word "else" :: ts => do
        let (q, st) ← b4Prog f (st.at ts)
        let st ← expectTok (.word "fi") st
        .ok (.cond c p q, st)
      | _ => do
        let st ← expectTok (.word "fi") st
        .ok (.cond c p .ok, st)
    | .word "while" :: ts => do
      let (c, st) ← parseExp f (st.at ts)
      let c ← c.toB4
      let st ← expectTok (.word "do") st
      let (p, st) ← b4Prog f st
      let st ← expectTok (.word "od") st
      .ok (.loop c p, st)
    | .sym "(" :: ts => do
      let (p, st) ← b4Prog f (st.at ts)
      let st ← expectTok (.sym ")") st
      .ok (p, st)
    | .word c :: .sym "!" :: ts =>
      match st.chans.findIdx? (·.1 == c) with
      | some k => do
        let (e, st) ← parseExp f (st.at ts)
        .ok (.send k (← e.toB4), st)
      | none => .error s!"'{c}' is not a channel"
    | .word c :: .sym "?" :: ts =>
      match st.chans.findIdx? (·.1 == c), st.chans.find? (·.1 == c) with
      | some k, some (_, M, _) => .ok (.recv k M, st.at ts)
      | _, _ => .error s!"'{c}' is not a channel"
    | .word w :: _ => do
      let (x, st) ← parseName st
      match st.toks with
      | .sym ":=" :: ts => do
        let (e, st) ← parseExp f (st.at ts)
        .ok (.assign x (← e.toB4), st)
      | _ => .error s!"'{w}': the b4 compiler takes only plain assignments x:= e"
    | t :: _ => .error s!"'{t.render}' is not something the b4 compiler takes yet: it compiles \
        ok, tick, x:= e, if, while, c! e, c? and a || of processes"
    | [] => .error "expected a statement, found the end of the program"
termination_by structural fuel

end

/-- `processes := program ('||' program)*`. -/
def b4Procs (fuel : ℕ) (st : PS) : Except String (List Stmt × PS) :=
  match fuel with
  | 0 => .error "too many processes"
  | f + 1 => do
    let (p, st) ← b4Prog fuel st
    match st.toks with
    | .sym "||" :: ts => do
      let (ps, st) ← b4Procs f (st.at ts)
      .ok (p :: ps, st)
    | _ => .ok ([p], st)

/-- A program for b4: its processes (one, if there is no `||`), its variables,
and its channels. -/
structure B4Program where
  /-- The processes. -/
  procs : List Stmt
  /-- The variables: variable `k` is written `names[k]`. -/
  names : List String
  /-- The channels: name, variable, (unused) cursor variable. -/
  chans : List (String × ℕ × ℕ)

/-- Read a program for b4, the names given on the command line first. -/
def parseB4 (names : List String) (ts : Toks) : Except String B4Program := do
  if ts.any (· == .sym "<==") then
    throw "the b4 compiler does not take refinements (named specifications) yet"
  let (names, chans) := internChans (scanChans ts []) names
  let (procs, st) ← b4Procs (8 * ts.length + 32) ⟨ts, names, [], [], [], chans, true⟩
  match st.toks with
  | [] => .ok ⟨procs, st.names, chans⟩
  | t :: _ => throw s!"unexpected '{t.render}': a || must be the whole program, each process \
      in parentheses"

/-! ### Running -/

/-- The variables a statement assigns, and the channels it writes and reads. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.writes : Stmt → List ℕ
  | .assign x _ => [x]
  | .recv _ x => [x]
  | .seq p q | .cond _ p q => p.writes ++ q.writes
  | .loop _ p => p.writes
  | _ => []

/-- The channels a statement outputs on (`true`) or inputs from. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.comms : Stmt → List (Bool × ℕ)
  | .send c _ => [(true, c)]
  | .recv c _ => [(false, c)]
  | .seq p q | .cond _ p q => p.comms ++ q.comms
  | .loop _ p => p.comms
  | _ => []

/-- Whether an expression is a binary, by its form. -/
def Exp.isBin : Exp → Bool
  | .lit (.bool _) | .un .not _ => true
  | .bin op _ _ => op == .eq || op == .lt
  | _ => false

/-- The expressions a statement assigns to `x`. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.assignsTo (x : ℕ) : Stmt → List Exp
  | .assign y e => if x = y then [e] else []
  | .seq p q | .cond _ p q => p.assignsTo x ++ q.assignsTo x
  | .loop _ p => p.assignsTo x
  | _ => []

/-- A variable every assignment of which is a binary, so it is shown as one. -/
def B4Program.isBinVar (bp : B4Program) (x : ℕ) : Bool :=
  let es := bp.procs.flatMap (·.assignsTo x)
  !es.isEmpty && es.all Exp.isBin

/-- The layout: the cells above the longest process's code. -/
def B4Program.layout (bp : B4Program) : Layout :=
  ⟨0x100 + (bp.procs.map (slen ⟨0, 0⟩ ·)).foldl max 0 + 16, bp.names.length⟩

/-- The network the processes make, with the command line's input on the
channels no process writes. -/
def B4Program.toSNet (bp : B4Program) (s : St) : SNet :=
  let outs := bp.procs.map fun p => (p.comms.filterMap fun (b, c) => if b then some c else none)
  ⟨bp.procs.zip outs |>.map fun (p, o) =>
      ⟨p, o, p.comms.filterMap fun (b, c) => if b then none else some c⟩,
    fun c => if outs.any (·.contains c) then [] else
      match bp.chans[c]? with
      | some (_, M, _) => (s M).toList.map fun v => (v, 0)
      | none => []⟩

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
  deriving DecidableEq, Repr

/-- Run on b4: compile and load each process, run the swarm (a lone process is a
swarm of one), and read back the result. -/
def B4Program.run (bp : B4Program) (s : St) (fuel : ℕ) : Except String B4Outcome := do
  let L := bp.layout
  if !(L.base + 4 * L.n + 16 ≤ MAXBYTE) then
    throw "the program and its variables do not fit in b4's 64 KB"
  let net := bp.toSNet s
  for c in [0:bp.chans.length] do
    if (net.procs.filter fun pr => pr.outs.contains c).length > 1 then
      throw s!"channel {(bp.chans[c]?.map (·.1)).getD "?"} is written by two processes"
  let w := (net.load L s).run fuel
  let st :=
    if w.ms.all (getRST · != 1) then B4Status.halted
    else if w.sweep.2 then .running else .deadlock
  let owner := fun x => bp.procs.findIdx? (·.writes.contains x)
  let value := fun x => match owner x with
    | some i => ((w.ms[i]?).map fun m => B4Program.value (getVal m.mem (L.addr x))).getD 0
    | none => (s x).toInt
  .ok ⟨st, (w.ms.map fun m => (getClk m).toNat).foldl max 0,
    (bp.names.zipIdx.filter fun (n, k) => !n.startsWith "#" && !bp.chans.any (·.2.1 == k)).map
      fun (n, k) => (n, value k),
    bp.chans.zipIdx.map fun ((n, _, _), c) =>
      (n, (w.chans c).map fun (v, t) => (B4Program.value v, t.toNat))⟩

/-- Parse and run on b4. -/
def b4Outcome (names : List String) (ts : Toks) (s : St) (fuel : ℕ) : Except String B4Outcome := do
  (← parseB4 names ts).run s fuel

/-- A value as b4 holds it, read back as an integer: a binary is `-1` or `0`. -/
def Value.b4Int : Value → ℤ
  | .int k => k
  | .bool b => if b then -1 else 0
  | .list _ => 0

/-- Whether a run on b4 shows what the network machine computed. -/
def B4Outcome.agrees (b : B4Outcome) (o : NetOutcome) : Bool :=
  (match o.status, b.status with
    | .done, .halted => b.time == o.time.toNat && o.time != ⊤
    | .deadlock, .deadlock => true
    | _, _ => false) &&
  b.vars == o.vars.map (fun (n, v) => (n, v.b4Int)) &&
  b.scripts == o.scripts.map (fun (n, l) => (n, l.map fun (v, t) => (v.b4Int, t.toNat)))

/-- Whether a run of a single program on b4 shows what the interpreter computed. -/
def B4Outcome.agreesWith (b : B4Outcome) (names : List String) (s : St) : Bool :=
  b.status == .halted &&
    b.vars == (names.zipIdx.filter fun (n, _) => !n.startsWith "#").map fun (n, k) => (n, (s k).b4Int)

namespace Demo

#eval b4Outcome ["n"] sumToToks (fun x => if x = 0 then .int 10 else .int 0) 10000
#eval b4Outcome [] sendRecvToks init 1000
#eval b4Outcome [] bufferToks init 1000
#eval b4Outcome [] pipelineToks init 1000
#eval b4Outcome [] deadlockToks init 1000

end Demo

end LaPToP.ProgramTheory.Interpreter.Lang
