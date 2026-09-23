import LaPToP.ProgramTheory.InterpreterSyntax
import LaPToP.ProgramTheory.InterpreterTime

/-!
# `interp`: running the aPToP demonstration programs from a shell

A thin command-line wrapper over `LaPToP.ProgramTheory.Interpreter`. It parses a
program in the concrete syntax of `Interpreter.Demo`, runs it with `run` (one
poststate, the deterministic fragment) or searches with `runAll` (every
poststate, so a choice can backtrack), and prints the final state. No semantics
lives here: the parser, the interpreter and their theorems are in the library,
and this file is argument handling and printing.

The Verso blueprint generator is `LaPToPMain`; this is a separate executable and
does not touch it.
-/

open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Demo
open LaPToP.ProgramTheory.Interpreter.Timed (TState runT renderTime)

/-- What the command line asked for. -/
structure Options where
  /-- The file to read the program from; standard input when absent. -/
  file : Option String := none
  /-- A built-in demonstration program to run instead of reading one. -/
  demo : Option String := none
  /-- The initial value of `n`. -/
  n : Int := 0
  /-- The initial value of `i`. -/
  i : Int := 0
  /-- The initial value of `s`. -/
  s : Int := 0
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
"interp — run a program of the aPToP interpreter demonstrations

usage: interp [options] [file]

  file               read the program from this file (default: standard input)
  --demo=NAME        run a program written in Lean instead: sumTo, count,
                     backtrack, withLocal
  --n=K --i=K --s=K  initial values of the state variables (default 0)
  --fuel=K           execution fuel (default 1000)
  --all              search for every poststate (runAll) rather than run once
  --timed            run on a state with a clock and print the final time;
                     `tick` advances it and a false `assert` waits until \u221e
  --selftest         check the tokenizer against the proved token lists
  --grammar          print the grammar of the concrete syntax
  --help             print this message

exit status: 0 success, 1 bad usage or parse error, 2 no poststate,
3 self-test failure."

/-- The grammar of the concrete syntax. -/
def grammarText : String :=
"program   := choice ('.' choice)* '.'?
choice    := statement ('or' statement)*
statement := 'ok'
           | 'tick'
           | var ':=' exp
           | 'if' cond 'then' program 'else' program 'fi'
           | 'while' cond 'do' program 'od'
           | 'new' var ':=' exp 'in' program 'end'
           | 'ensure' cond
           | 'assert' cond
           | '(' program ')'
cond      := rel ('and' rel)*
rel       := 'not' rel | exp ('=' | '<=' | '!=') exp
exp       := term (('+' | '-') term)*
term      := factor ('*' factor)*
factor    := integer | var | '-' factor | '(' exp ')'
var       := 'n' | 'i' | 's'

'.' is sequential composition and binds loosest, so
  s:= 0 or s:= 1. ensure s = 1
is the choice followed by the ensure, as in Section 5.4.0. A condition is not
parenthesized; an expression may be. The state is the three integer variables
n, i, s of the demonstrations."

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
    else if a.startsWith "--n=" then
      match parseIntArg "--n" (optValue a 4) with
      | .ok k => parseArgs rest { o with n := k }
      | .error e => .error e
    else if a.startsWith "--i=" then
      match parseIntArg "--i" (optValue a 4) with
      | .ok k => parseArgs rest { o with i := k }
      | .error e => .error e
    else if a.startsWith "--s=" then
      match parseIntArg "--s" (optValue a 4) with
      | .ok k => parseArgs rest { o with s := k }
      | .error e => .error e
    else if a.startsWith "--fuel=" then
      match parseIntArg "--fuel" (optValue a 7) with
      | .ok k => if k < 0 then .error "the fuel must not be negative"
                 else parseArgs rest { o with fuel := k.toNat }
      | .error e => .error e
    else if a.startsWith "-" then .error s!"unknown option '{a}'"
    else
      match o.file with
      | none => parseArgs rest { o with file := some a }
      | some _ => .error "give at most one program file"

/-- The demonstration programs that can be named on the command line: the very
terms `Interpreter.Demo` proves things about. -/
def demoProg : String → Option (String × P)
  | "sumTo" => some (sumToSrc, sumTo)
  | "count" => some (countSrc, count)
  | "backtrack" => some (backtrackSrc, backtrack)
  | "withLocal" => some (withLocalSrc, withLocal)
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
  for (name, src, toks) in selfTests do
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

/-- Run a program and print what it reaches. -/
def runProgram (o : Options) (p : P) : IO UInt32 := do
  let st := state o.n o.i o.s
  if o.timed then
    match runT o.fuel p ⟨st, 0⟩ with
    | some r =>
      IO.println s!"{renderState r.mem}, t = {renderTime r.t}"
      return 0
    | none =>
      IO.eprintln
        "interp: no poststate — the program has none (a failed `ensure`), the fuel \
         ran out, or the branch the deterministic interpreter chose failed"
      return 2
  if o.all then
    let results := runAll o.fuel p st
    if results.isEmpty then
      IO.eprintln "interp: no poststate — the program has none, or the fuel ran out"
      return 2
    for r in results do
      IO.println (renderState r)
    return 0
  else
    match run o.fuel p st with
    | some r =>
      IO.println (renderState r)
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
    if o.timed && o.all then
      IO.eprintln "interp: --timed and --all cannot be combined (there is no searching \
        timed interpreter yet)"
      return 1
    match o.demo with
    | some name =>
      match demoProg name with
      | some (_, p) => runProgram o p
      | none =>
        IO.eprintln s!"interp: unknown demonstration '{name}' \
          (try sumTo, count, backtrack or withLocal)"
        return 1
    | none =>
      match ← readSource o with
      | .error e =>
        IO.eprintln s!"interp: {e}"
        return 1
      | .ok src =>
        match parseProgram src with
        | .error e =>
          IO.eprintln s!"interp: {e}"
          return 1
        | .ok p => runProgram o p
