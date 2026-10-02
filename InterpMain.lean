import LaPToP.ProgramTheory.B4Lang
import LaPToP.ProgramTheory.Alloc

/-!
# `interp`: running programs of the aPToP interpreter from a shell

A thin command-line wrapper over `LaPToP.ProgramTheory.Interpreter`. It parses a
program in the concrete syntax of `Interpreter.Lang`, runs it with `run` (one
poststate, the deterministic fragment) or searches with `runAll` (every
poststate, so a choice can backtrack), with `runT`/`runAllT` in place of those on
a state with a clock, and prints the final state. No semantics lives here: the
parser, the interpreter and their theorems are in the library, and this file is
argument handling and printing.

The Verso blueprint generator is `LaPToPMain`; this is a separate executable and
does not touch it.
-/

open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Lang
open LaPToP.ProgramTheory.Interpreter.Timed (TState runT runAllT renderTime)
open LaPToP.ProgramTheory.Interpreter.Demo (Toks)

/-- What the command line asked for. -/
structure Options where
  /-- The file to read the program from; standard input when absent. -/
  file : Option String := none
  /-- A built-in demonstration program to run instead of reading one. -/
  demo : Option String := none
  /-- Initial values, as a name and the text of an expression, in the order given. -/
  sets : List (String × String) := []
  /-- The execution fuel. -/
  fuel : Nat := 1000
  /-- Search for every poststate instead of running once. -/
  all : Bool := false
  /-- Run on a state with a clock, and print the time. -/
  timed : Bool := false
  /-- Compute the distribution of the final states. -/
  dist : Bool := false
  /-- Run as a network of communicating processes. -/
  net : Bool := false
  /-- Compile to b4 and run there. -/
  b4 : Bool := false
  /-- Check the tokenizer against the token lists the parser theorems use. -/
  selftest : Bool := false
  /-- Print the grammar. -/
  grammar : Bool := false
  /-- Print the usage message. -/
  help : Bool := false

/-- How to call it. -/
def usage : String :=
"interp — run a program in the programming notation of aPToP

usage: interp [options] [file]

  file               read the program from this file (default: standard input)
  --demo=NAME        run a demonstration program: sumTo, backtrack, arrays,
                     listSum, exitLoop, deepExit, forLoop, gcd, swap, sort, even,
                     channel, parSwap, seqPar, parTime, probEx1, probEx2, rand,
                     and the networks sendRecv, buffer, deadlock, doubler,
                     pipeline, poll
  --NAME=EXP         the initial value of variable NAME, an expression such as
                     --n=10 or --L=[3;1;2] (every other variable starts at 0)
  --fuel=K           execution fuel (default 1000)
  --all              search for every poststate (runAll) rather than run once
  --timed            run on a state with a clock and print the final time;
                     `tick` advances it and a false `assert` waits until \u221e;
                     with --all, search on the clock (runAllT)
  --dist             compute the distribution of the final states (Section 5.7):
                     each with its probability, and the probability of none
  --b4               compile to the b4 virtual machine and run there (a network
                     on a swarm of b4 machines): ok, tick, x:= e, if, while,
                     do/exit and for loops, new, simultaneous assignment,
                     specifications with parameters and recursion, c! e, c?,
                     a || of processes, and arrays (A i, A i:= e, each array
                     as long as the list it starts with), on 32-bit integers
  --net              run as a network of communicating processes (Chapter 9),
                     as is done anyway when the program has channels and a ||:
                     each process has its own variables, communicates only on
                     channels, and a message takes one unit of time
  --selftest         check the tokenizer against the proved token lists
  --grammar          print the grammar of the concrete syntax
  --help             print this message

exit status: 0 success, 1 bad usage or parse error, 2 no poststate,
3 self-test failure."

/-- The grammar of the concrete syntax. -/
def grammarText : String :=
"file      := (name params? '⇐' program | program)*
params    := '(' name (',' name)* ')'
program   := par ('.' par)* '.'?
par       := choice ('||' choice)*
choice    := statement ('or' statement)*
statement := 'ok' | 'tick'
           | name atom* ':=' exp
           | name (',' name)* ':=' exp (',' exp)*   -- simultaneous
           | name ('(' exp (',' exp)* ')')?         -- a call
           | name '!' exp | name '?'                -- output, input
           | 'if' exp ('/' exp)? 'then' program ('else' program)? 'fi'
           | name ':=' 'rand' atom
           | 'while' exp 'do' program 'od'
           | 'do' body 'od'
           | 'for' name ':=' exp ';..' exp 'do' program 'od'
           | 'new' name ':=' exp 'in' program 'end'
           | 'ensure' exp | 'assert' exp
           | '(' program ')'
body      := item ('.' item)* '.'?
item      := 'exit' integer? ('when' exp)?
           | 'if' exp 'then' body ('else' body)? 'fi'
           | 'do' body 'od'
           | choice
exp       := disj ('⇒' exp)?
disj      := conj ('∨' conj)*
conj      := neg (('∧' | 'and') neg)*
neg       := 'not' neg | cmp
cmp       := sum (('=' | '≠' | '<' | '≤' | '>' | '≥') sum)?
sum       := prod (('+' | '-') prod)*
prod      := unary (('×' | '*' | 'div' | 'mod') unary)*
unary     := ('-' | '¬' | '#') unary | pow
pow       := app ('^' unary)?
app       := atom atom*
atom      := integer | '⊤' | '⊥' | name | '(' exp ')'
           | '[' ']' | '[' exp (';' exp)* ']'
           | 'if' exp 'then' exp 'else' exp 'fi'
           | '√' name

A file is a list of refinements P ⇐ ... and a main program; with no main
program the first specification is run. A specification's name on the right of
a refinement is a call, and may be recursive. 'do ... od' is the exit-loop:
'exit n when b' leaves n loops. 'for i:= m;..n do P od' runs i from m to n-1.
A specification with parameters, P(x, y) ⇐ ..., is called as P(e, f); the
arguments are computed first and bound as locals, which the body may not assign.
P || Q is concurrent composition: it binds tighter than '.' and looser than
'or'; each process owns the variables it may assign, may not assign the
other's, and sees the other's only at their initial values. On the clock it
finishes when both have.
'if a/b then P else Q fi' is probabilistic (Section 5.7): P with probability a/b.
'x:= rand n' gives x each of 0,..n with probability 1/n. --dist prints the
distribution of the final states.
A name written c! e or c? is a channel: c! e outputs, c? inputs (waiting for a
message), c is the last message input and √c says one is waiting. The channel's
script is the list variable c: --keyboard=[3;4] supplies input, and a channel
written to prints as the list of its messages.
A program with channels and a || (or any program, with --net) is a network
(Chapter 9): the processes of the main ||, each parenthesized, run concurrently,
each with its own variables, and communicate only on channels, each written by
one process; a message arrives one unit of time after it is sent. A run prints
the final variables, the time, and each channel's messages with the times they
were sent; when every unfinished process waits for input that never comes, it
is a deadlock, and the time is ∞.

Values are integers, binaries (⊤, ⊥) and lists ([3; 1; 2]); a variable never
assigned is 0. '.' is sequential composition and binds loosest, so
  s:= 0 or s:= 1. ensure s = 1
is the choice followed by the ensure, as in Section 5.4.0. Juxtaposition is
indexing: A i is item i of list A, counting from 0, and A i:= e is the book's
A:= i→e | A. '+' adds integers and catenates lists; #L is the length of L.
ASCII spellings: <== => \\/ /\\ != <= >= * true false; ⧧ is accepted for ≠.
¬ binds tightest, as in the book; the word 'not' binds looser than a
comparison. A comment runs from -- to the end of the line."

/-- The text of an option after its `--name=` prefix. -/
private def optValue (a : String) (n : Nat) : String := String.ofList (a.toList.drop n)

private def parseIntArg (name s : String) : Except String Int :=
  match s.toInt? with
  | some k => .ok k
  | none => .error s!"the value of {name} must be an integer, not '{s}'"

/-- Read the command line. -/
def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | a :: rest, o =>
    if a == "--help" || a == "-h" then parseArgs rest { o with help := true }
    else if a == "--all" then parseArgs rest { o with all := true }
    else if a == "--timed" then parseArgs rest { o with timed := true }
    else if a == "--dist" then parseArgs rest { o with dist := true }
    else if a == "--net" then parseArgs rest { o with net := true }
    else if a == "--b4" then parseArgs rest { o with b4 := true }
    else if a == "--selftest" then parseArgs rest { o with selftest := true }
    else if a == "--grammar" then parseArgs rest { o with grammar := true }
    else if a.startsWith "--demo=" then parseArgs rest { o with demo := some (optValue a 7) }
    else if a.startsWith "--fuel=" then
      match parseIntArg "--fuel" (optValue a 7) with
      | .ok k => if k < 0 then .error "the fuel must not be negative"
                 else parseArgs rest { o with fuel := k.toNat }
      | .error e => .error e
    else if a.startsWith "--" && a.contains '=' then
      let body := optValue a 2
      let name := String.ofList (body.toList.takeWhile (· != '='))
      let val := String.ofList ((body.toList.dropWhile (· != '=')).drop 1)
      parseArgs rest { o with sets := o.sets ++ [(name, val)] }
    else if a.startsWith "-" then .error s!"unknown option '{a}'"
    else
      match o.file with
      | none => parseArgs rest { o with file := some a }
      | some _ => .error "give at most one program file"

/-- The demonstration programs that can be named on the command line: their
sources, which the self-test checks tokenize to the token lists the theorems of
`Lang.Demo` are stated of. -/
def demoSrc : String → Option String
  | "sumTo" => some Lang.Demo.sumToSrc
  | "backtrack" => some Lang.Demo.backtrackSrc
  | "arrays" => some Lang.Demo.arraysSrc
  | "sort" => some Lang.Demo.sortSrc
  | "listSum" => some Lang.Demo.listSumSrc
  | "exitLoop" => some Lang.Demo.exitLoopSrc
  | "deepExit" => some Lang.Demo.deepExitSrc
  | "forLoop" => some Lang.Demo.forLoopSrc
  | "gcd" => some Lang.Demo.gcdSrc
  | "swap" => some Lang.Demo.swapSrc
  | "even" => some Lang.Demo.evenSrc
  | "channel" => some Lang.Demo.channelSrc
  | "parSwap" => some Lang.Demo.parSwapSrc
  | "seqPar" => some Lang.Demo.seqParSrc
  | "parTime" => some Lang.Demo.parTimeSrc
  | "probEx1" => some Lang.Demo.probEx1Src
  | "probEx2" => some Lang.Demo.probEx2Src
  | "rand" => some Lang.Demo.randSrc
  | "sendRecv" => some Lang.Demo.sendRecvSrc
  | "buffer" => some Lang.Demo.bufferSrc
  | "deadlock" => some Lang.Demo.deadlockSrc
  | "doubler" => some Lang.Demo.doublerSrc
  | "pipeline" => some Lang.Demo.pipelineSrc
  | "poll" => some Lang.Demo.pollSrc
  | _ => none

/-- Read the program text. -/
def readSource (o : Options) : IO (Except String String) := do
  match o.file with
  | some f =>
    try
      return .ok (← IO.FS.readFile f)
    catch e =>
      return .error s!"cannot read '{f}': {e}"
  | none => return .ok (← (← IO.getStdin).readToEnd)

/-- Check that the tokenizer takes each demonstration source to the token list
the parser theorems are stated of. Those theorems (`parseToks_sumTo` and its
fellows) prove that the parser turns those tokens into the Lean programs, so
passing here means the binary runs exactly what the library proves about. -/
def runSelfTest : IO UInt32 := do
  let mut bad : Nat := 0
  for (name, src, toks) in Lang.Demo.selfTests ++ Lang.Demo.netSelfTests do
    match tokenize (src.length + 1) src.toList with
    | .ok ts =>
      if ts == toks then
        IO.println s!"ok    {name}: tokenizes to the token list of the parser theorem"
      else
        IO.eprintln s!"FAIL  {name}: tokens differ from the proved list"
        bad := bad + 1
    | .error e =>
      IO.eprintln s!"FAIL  {name}: {e}"
      bad := bad + 1
  -- The b4 compiler against the interpreters, on the demonstrations it takes.
  let given : List (ℕ × ℤ) → St := fun l x => .int (((l.lookup x).getD 0))
  let b4Tests : List (String × List String × Toks × St) :=
    [("sumTo", ["n"], Lang.Demo.sumToToks, given [(0, 10)]),
     ("exitLoop", ["n", "x"], Lang.Demo.exitLoopToks, given [(0, 5)]),
     ("deepExit", [], Lang.Demo.deepExitToks, given []),
     ("forLoop", ["n"], Lang.Demo.forLoopToks, given [(0, 10)]),
     ("gcd", ["x", "y"], Lang.Demo.gcdToks, given [(0, 12), (1, 18)]),
     ("swap", ["x", "y"], Lang.Demo.swapToks, given [(0, 1), (1, 2)]),
     ("sort", ["n", "A"], Lang.Demo.sortToks, Function.update (given [(0, 6)]) 1
       (.list ([5, 3, 9, 1, 4, 2].map .int)))]
  -- The allocator: read from its source, it is the statement proved (Alloc.alloc_sEval).
  let allocToks := (tokenize (LaPToP.ProgramTheory.Alloc.allocSrc.length + 1) LaPToP.ProgramTheory.Alloc.allocSrc.toList).toOption.getD []
  match parseB4 ["n", "M"] allocToks with
  | .ok bp =>
    if reprStr bp.procs == reprStr [LaPToP.ProgramTheory.Alloc.allocStmt] then
      IO.println "ok    alloc: the source reads as the allocator proved in Alloc"
    else IO.eprintln "FAIL  alloc: the source does not read as the proved allocator"; bad := bad + 1
  | .error e => IO.eprintln s!"FAIL  alloc: {e}"; bad := bad + 1
  let heap : List ℤ → St := fun ms => Function.update (given [(0, 5)]) 1 (.list (ms.map .int))
  let b4Tests := b4Tests ++
    [("alloc (split)", ["n", "M"], allocToks, heap ([-1, 17] ++ List.replicate 18 0)),
     ("alloc (merge)", ["n", "M"], allocToks,
       Function.update (heap [6, 3, 0, 0, 0, 0, 11, 2, 0, 0, 0, -1, 6, 1, 0, 0, 0, 0, 0, 0]) 0 (.int 7)),
     ("alloc (none)", ["n", "M"], allocToks,
       Function.update (heap [6, 3, 1, 0, 0, 0, -1, 11, 1, 0, 0, 0, 0, 0, 0, 0, 0]) 0 (.int 2))]
  for (name, names, toks, start) in b4Tests do
    match parseToksWith names toks, b4Outcome names toks start 100000 with
    | .ok prog, .ok b =>
      let arr : Array Value := Array.ofFn (n := prog.names.length) fun i => start i.1
      match prog.runFast 100000 arr with
      | some r =>
        if b.agreesWith prog.names (toFun r) then
          IO.println s!"ok    {name}: b4 computes what the interpreter does"
        else IO.eprintln s!"FAIL  {name}: b4 and the interpreter differ"; bad := bad + 1
      | none => IO.eprintln s!"FAIL  {name}: the interpreter found no poststate"; bad := bad + 1
    | .error e, _ | _, .error e => IO.eprintln s!"FAIL  {name}: {e}"; bad := bad + 1
  for (name, _, toks) in Lang.Demo.netSelfTests do
    let start : St := if name == "doubler" then Function.update init 0 (.list [.int 1, .int 2, .int 5]) else init
    if name == "doubler" then continue
    match netOutcome false [] toks start 1000 1000, b4Outcome [] toks start 10000 with
    | .ok o, .ok b =>
      if b.agrees o then IO.println s!"ok    {name}: the b4 swarm computes what the network machine does"
      else IO.eprintln s!"FAIL  {name}: the b4 swarm and the network machine differ"; bad := bad + 1
    | _, _ => IO.eprintln s!"FAIL  {name}: does not run on both"; bad := bad + 1
  if bad == 0 then
    IO.println "all self-tests passed"
    return 0
  else
    return 3

/-- The initial state: the names given on the command line are the first in the
table, so they print first, and each is set to the value of its expression. -/
def initialState (names : List String) (sets : List (String × String)) :
    Except String (List String × St) := do
  let mut names := names
  let mut s := init
  for (w, src) in sets do
    let (x, ns) := intern w names
    let (e, ns) ← (parseExpression ns src).mapError fun m => s!"the value of {w}: {m}"
    names := ns
    s := Function.update s x (e.eval s)
  return (names, s)

/-- Collect equal states of a distribution, comparing them on the variables
the program has. -/
def collect (n : ℕ) (d : List (St × ℚ)) : List (St × ℚ) :=
  d.foldl (fun acc (s, w) =>
    let key := (List.range n).map s
    match acc.findIdx? fun (t, _) => (List.range n).map t == key with
    | some i => acc.modify i fun (t, v) => (t, v + w)
    | none => acc ++ [(s, w)]) []

/-- Run a program and print what it reaches. -/
def runProgram (o : Options) (names : List String) (st : St) (prog : Program) : IO UInt32 := do
  let shown (s : St) : String := renderState names s
  if o.dist then
    if o.timed || o.all then
      IO.eprintln "interp: --dist cannot be combined with --timed or --all"
      return 1
    let d := collect names.length (prog.runDist o.fuel st)
    for (s, w) in d do
      IO.println s!"{w}: {shown s}"
    let lost := 1 - mass d
    if lost != 0 then
      IO.println s!"{lost}: no final state (no termination within the fuel, or a failed ensure)"
    return (if d.isEmpty then 2 else 0)
  if o.timed && o.all then
    let results := prog.runAllT o.fuel ⟨st, 0⟩
    if results.isEmpty then
      IO.eprintln "interp: no poststate — the program has none, or the fuel ran out"
      return 2
    for r in results do
      IO.println s!"{shown r.mem}, t = {renderTime r.t}"
    return 0
  -- The deterministic runs use the array interpreters, which compute what `run`
  -- and `runT` compute (`Program.runFast_eq`, `Program.runTFast_eq`).
  let arr : Array Value := Array.ofFn (n := names.length) fun i => st i.1
  if o.timed then
    match prog.runTFast o.fuel (arr, 0) with
    | some (r, t) =>
      IO.println s!"{shown (toFun r)}, t = {renderTime t}"
      return 0
    | none =>
      IO.eprintln
        "interp: no poststate — the program has none (a failed `ensure`), the fuel \
         ran out, or the branch the deterministic interpreter chose failed (try --all)"
      return 2
  if o.all then
    let results := prog.runAll o.fuel st
    if results.isEmpty then
      IO.eprintln "interp: no poststate — the program has none, or the fuel ran out"
      return 2
    for r in results do
      IO.println (shown r)
    return 0
  else
    match prog.runFast o.fuel arr with
    | some r =>
      IO.println (shown (toFun r))
      return 0
    | none =>
      IO.eprintln
        "interp: no poststate — the program has none, the fuel ran out, or the \
         branch the deterministic interpreter chose failed (try --all)"
      return 2

/-- Run a network and print what it does. -/
def runNetwork (o : Options) (setNames : List String) (ts : Toks) : IO UInt32 := do
  let parsed := do
    let prog ← parseToksMode true setNames ts
    let (names, st) ← initialState prog.names o.sets
    let np ← toNet prog (chansOf setNames ts) st
    return (prog, names, st, np)
  match parsed with
  | .error e =>
    IO.eprintln s!"interp: {e}"
    return 1
  | .ok (prog, _, st, np) =>
    let (c, status) := np.run prog o.fuel o.fuel st
    let out := np.outcome prog o.fuel o.fuel st
    let vars := ", ".intercalate (out.vars.map fun (w, v) => s!"{w} = {v.render}")
    let time := match status with
      | .deadlock => "∞"
      | _ => renderTime (finishTime c)
    IO.println (if vars.isEmpty then s!"t = {time}" else s!"{vars}, t = {time}")
    for (w, sc) in out.scripts do
      let vs := "; ".intercalate (sc.map fun (v, _) => v.render)
      let ts := "; ".intercalate (sc.map fun (_, t) => renderTime t)
      IO.println s!"{w} = [{vs}] sent at [{ts}]"
    match status with
    | .done => return 0
    | .deadlock =>
      let waiting := (c.ps.zipIdx.filter fun (pc, _) => !pc.k.isEmpty).map fun (pc, i) =>
        match pc.k with
        | .recv ch _ :: _ =>
          s!"process {i + 1} waits for input on {(np.chans[ch]?.map (·.1)).getD "?"}"
        | _ => s!"process {i + 1} cannot go on"
      IO.println s!"deadlock: {", ".intercalate waiting}; that input never comes"
      return 0
    | .running =>
      IO.eprintln s!"interp: the processes were still running after {o.fuel} rounds \
        (--fuel); shown is what they had done"
      return 2

/-- Compile to b4, run, and print what the machines hold. -/
def runB4 (o : Options) (setNames : List String) (ts : Toks) : IO UInt32 := do
  let parsed := do
    let bp ← parseB4 setNames ts
    let (names, st) ← initialState bp.names o.sets
    let bp := { bp with names := names }
    let out ← bp.run st o.fuel
    return (bp, st, out)
  match parsed with
  | .error e =>
    IO.eprintln s!"interp --b4: {e}"
    return 1
  | .ok (bp, st, out) =>
    -- The theorems hold while no value leaves 32 bits: check against the
    -- language's own interpreters, and say so if the machine went outside.
    let agrees : Bool :=
      if out.status == .running then true
      else if bp.procs.length == 1 && bp.chans.isEmpty then
        match parseToksMode false setNames ts with
        | .ok prog =>
          let arr : Array Value := Array.ofFn (n := prog.names.length) fun i => st i.1
          match prog.runFast o.fuel arr with
          | some r => out.agreesWith prog.names (toFun r)
          | none => true
        | .error _ => true
      else
        match netOutcome true setNames ts st o.fuel o.fuel with
        | .ok n => n.status == .running || out.status == .running || out.agrees n
        | .error _ => true
    if !agrees then
      IO.eprintln "interp --b4: warning: some value left 32 bits or some index left its array, \
        so the machine's result is not the language's (the compiler is proved correct only \
        within 32 bits and within the arrays)"
    let shown := fun (w : String) (v : ℤ) =>
      match bp.names.idxOf? w with
      | some x => if bp.isBinVar x then (if v == 0 then "⊥" else "⊤") else toString v
      | none => toString v
    let vars := ", ".intercalate (bp.names.filterMap fun w =>
      match out.vars.lookup w, out.arrays.lookup w with
      | some v, _ => some s!"{w} = {shown w v}"
      | none, some l => some s!"{w} = [{"; ".intercalate (l.map toString)}]"
      | none, none => none)
    let time := if out.status == .deadlock then "∞" else toString out.time
    IO.println (if vars.isEmpty then s!"t = {time}" else s!"{vars}, t = {time}")
    for (w, sc) in out.scripts do
      let vs := "; ".intercalate (sc.map fun (v, _) => toString v)
      let tts := "; ".intercalate (sc.map fun (_, t) => toString t)
      IO.println s!"{w} = [{vs}] sent at [{tts}]"
    match out.status with
    | .halted => return 0
    | .deadlock =>
      IO.println "deadlock: the machines that have not halted wait for input that never comes"
      return 0
    | .running =>
      IO.eprintln s!"interp --b4: the machines were still running after {o.fuel} rounds (--fuel)"
      return 2

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln s!"interp: {e}"
    IO.eprintln usage
    return 1
  | .ok o =>
    if o.help then
      IO.println usage
      return 0
    if o.grammar then
      IO.println grammarText
      return 0
    if o.selftest then
      return (← runSelfTest)
    let src ← match o.demo with
      | some name =>
        match demoSrc name with
        | some src => pure (Except.ok src)
        | none => pure (.error s!"unknown demonstration '{name}' (try sumTo, backtrack, arrays, listSum, exitLoop, deepExit, forLoop, gcd, swap, even, channel, parSwap, seqPar, parTime, probEx1, probEx2, rand, sendRecv, buffer, deadlock, doubler or pipeline)")
      | none => readSource o
    for (w, _) in o.sets do
      if !validName w then
        IO.eprintln s!"interp: '{w}' cannot be a variable name"
        return 1
    let setNames := (o.sets.map (·.1)).foldl (fun ns w => (intern w ns).2) []
    if o.b4 then
      match src with
      | .ok text =>
        match tokenize (text.length + 1) text.toList with
        | .ok ts => return (← runB4 o setNames ts)
        | .error e => IO.eprintln s!"interp: {e}"; return 1
      | .error e => IO.eprintln s!"interp: {e}"; return 1
    if !o.timed && !o.all && !o.dist then
      match src with
      | .ok text =>
        match tokenize (text.length + 1) text.toList with
        | .ok ts =>
          if o.net || isNet (chansOf setNames ts) ts then
            return (← runNetwork o setNames ts)
        | .error _ => pure ()
      | .error _ => pure ()
    let parsed := do
      let src ← src
      let prog ← parseProgramWith setNames src
      let (names, st) ← initialState prog.names o.sets
      return (prog, names, st)
    match parsed with
    | .error e =>
      IO.eprintln s!"interp: {e}"
      return 1
    | .ok (prog, names, st) => runProgram o names st prog
