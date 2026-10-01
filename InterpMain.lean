import LaPToP.ProgramTheory.InterpreterLangSyntax

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
                     listSum, exitLoop, deepExit, forLoop, gcd, swap, even,
                     channel
  --NAME=EXP         the initial value of variable NAME, an expression such as
                     --n=10 or --L=[3;1;2] (every other variable starts at 0)
  --fuel=K           execution fuel (default 1000)
  --all              search for every poststate (runAll) rather than run once
  --timed            run on a state with a clock and print the final time;
                     `tick` advances it and a false `assert` waits until \u221e;
                     with --all, search on the clock (runAllT)
  --selftest         check the tokenizer against the proved token lists
  --grammar          print the grammar of the concrete syntax
  --help             print this message

exit status: 0 success, 1 bad usage or parse error, 2 no poststate,
3 self-test failure."

/-- The grammar of the concrete syntax. -/
def grammarText : String :=
"file      := (name params? '⇐' program | program)*
params    := '(' name (',' name)* ')'
program   := choice ('.' choice)* '.'?
choice    := statement ('or' statement)*
statement := 'ok' | 'tick'
           | name atom* ':=' exp
           | name (',' name)* ':=' exp (',' exp)*   -- simultaneous
           | name ('(' exp (',' exp)* ')')?         -- a call
           | name '!' exp | name '?'                -- output, input
           | 'if' exp 'then' program ('else' program)? 'fi'
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
A name written c! e or c? is a channel: c! e outputs, c? inputs (waiting for a
message), c is the last message input and √c says one is waiting. The channel's
script is the list variable c: --keyboard=[3;4] supplies input, and a channel
written to prints as the list of its messages.

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
  | "listSum" => some Lang.Demo.listSumSrc
  | "exitLoop" => some Lang.Demo.exitLoopSrc
  | "deepExit" => some Lang.Demo.deepExitSrc
  | "forLoop" => some Lang.Demo.forLoopSrc
  | "gcd" => some Lang.Demo.gcdSrc
  | "swap" => some Lang.Demo.swapSrc
  | "even" => some Lang.Demo.evenSrc
  | "channel" => some Lang.Demo.channelSrc
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
  for (name, src, toks) in Lang.Demo.selfTests do
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

/-- Run a program and print what it reaches. -/
def runProgram (o : Options) (names : List String) (st : St) (prog : Program) : IO UInt32 := do
  let shown (s : St) : String := renderState names s
  if o.timed && o.all then
    let results := prog.runAllT o.fuel ⟨st, 0⟩
    if results.isEmpty then
      IO.eprintln "interp: no poststate — the program has none, or the fuel ran out"
      return 2
    for r in results do
      IO.println s!"{shown r.mem}, t = {renderTime r.t}"
    return 0
  if o.timed then
    match prog.runT o.fuel ⟨st, 0⟩ with
    | some r =>
      IO.println s!"{shown r.mem}, t = {renderTime r.t}"
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
    match prog.run o.fuel st with
    | some r =>
      IO.println (shown r)
      return 0
    | none =>
      IO.eprintln
        "interp: no poststate — the program has none, the fuel ran out, or the \
         branch the deterministic interpreter chose failed (try --all)"
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
        | none => pure (.error s!"unknown demonstration '{name}' (try sumTo, backtrack, arrays, listSum, exitLoop, deepExit, forLoop, gcd, swap, even or channel)")
      | none => readSource o
    for (w, _) in o.sets do
      if !validName w then
        IO.eprintln s!"interp: '{w}' cannot be a variable name"
        return 1
    let setNames := (o.sets.map (·.1)).foldl (fun ns w => (intern w ns).2) []
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
