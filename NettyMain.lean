import Netty

/-!
# `netty`: driving a Netty proof session from a shell

A thin command line over `Netty.Doc` and `Netty.Session`. It loads law files,
runs a script of commands, prints the three panes when the script asks, and
saves or loads a proof file. No part of a proof lives here: the document model,
the suggestions and the check on what a proof proves are all in the library.

The Verso blueprint generator is `LaPToPMain` and the aPToP interpreter is
`InterpMain`; this is a third executable and touches neither.
-/

open Netty

/-- What the command line asked for. -/
structure Options where
  /-- The script to run; standard input when absent. -/
  script : Option String := none
  /-- A built-in demonstration to run instead of a script. -/
  demo : Option String := none
  /-- Law files to add, in order. -/
  laws : List String := []
  /-- Leave out the built-in boolean law list. -/
  bare : Bool := false
  /-- A proof file to start from. -/
  load : Option String := none
  /-- A proof file to write when the script ends. -/
  save : Option String := none
  /-- Print the laws in force and stop. -/
  listLaws : Bool := false
  /-- Print the built-in law list as a law file and stop. -/
  emitLaws : Bool := false
  /-- Run the kernel's checks on itself and stop. -/
  selftest : Bool := false
  /-- Print the usage message. -/
  help : Bool := false

/-- How to call it. -/
def usage : String :=
"netty — the kernel of a Netty calculational proof session

usage: netty [options] [script]

  script              run this file of commands (default: standard input)
  --demo=NAME         run a built-in demonstration instead: portation,
                      discharge, gap
  --laws=FILE         add a law file; may be repeated
  --bare              start with no laws but those given by --laws
  --load=FILE         start from a saved proof file
  --save=FILE         write the session to a proof file when the script ends
  --list-laws         print the laws in force and stop
  --emit-laws         print the built-in boolean law list as a law file
  --selftest          check the shipped laws and the demonstrations, and stop
  --help              print this message

A script is one command per line; ‘#’ begins a comment.

  start [boolean|number] DIRECTION EXPRESSION   begin the proof
  apply NAME                                    take a law's suggestion
  apply NAME : CONNECTIVE EXPRESSION            …when the law offers several
  apply #N                                      take the N-th suggestion
  direct CONNECTIVE EXPRESSION                  type the next line in
  zoom N                                        zoom in to the N-th operand
  out                                           zoom out
  focus N                                       move the focus after line N
  undo                                          undo one command
  proof | suggest | context                     print a pane
  check [EXPRESSION]                            print, and insist on, what the
                                                proof proves
  laws FILE                                     add a law file
  load FILE | save FILE                         read or write a proof file

Expressions are the boolean and number fragment of aPToP. ‘¬’ binds more
weakly than ‘=’, as it does in the book, and ‘≡ ⟹ ⟸’ are the book's large
‘= ⇒ ⇐’, which a law file needs because it has no left margin. Every operator
has an ASCII spelling: ~ /\\ \\/ => <= == ==> <== =< >= != T F.
"

/-- Drop the first `n` characters. -/
private def after (n : Nat) (s : String) : String := String.ofList (s.toList.drop n)

/-- Read the command line. -/
def parseArgs (args : List String) : Except String Options :=
  args.foldlM (init := {}) fun o a =>
    if a == "--help" || a == "-h" then .ok { o with help := true }
    else if a == "--bare" then .ok { o with bare := true }
    else if a == "--list-laws" then .ok { o with listLaws := true }
    else if a == "--emit-laws" then .ok { o with emitLaws := true }
    else if a == "--selftest" then .ok { o with selftest := true }
    else if a.startsWith "--demo=" then .ok { o with demo := some (after 7 a) }
    else if a.startsWith "--laws=" then .ok { o with laws := o.laws ++ [after 7 a] }
    else if a.startsWith "--load=" then .ok { o with load := some (after 7 a) }
    else if a.startsWith "--save=" then .ok { o with save := some (after 7 a) }
    else if Netty.Parser.beginsWith a '-' then .error s!"unknown option ‘{a}’"
    else if o.script.isSome then .error "give at most one script"
    else .ok { o with script := some a }

/-- The state a script runs in. -/
structure Run where
  /-- The session. -/
  session : Session
  /-- Whether every `check` has held so far. -/
  ok : Bool := true

/-- Run one script command. -/
def runCmd (r : Run) (lineNo : Nat) (c : ScriptCmd) : IO Run := do
  let fail (msg : String) : IO Run := do
    IO.eprintln s!"line {lineNo}: {msg}"
    return { r with ok := false }
  match c with
  | .doc dc =>
      match r.session.step dc with
      | .ok s => return { r with session := s }
      | .error e => fail e
  | .undo =>
      match r.session.undo with
      | .ok s => return { r with session := s }
      | .error e => fail e
  | .proof => IO.println r.session.doc.renderProof; return r
  | .suggest => IO.println r.session.doc.renderSuggestions; return r
  | .context => IO.println r.session.doc.renderContext; return r
  | .check expected =>
      IO.println r.session.doc.renderOutcome
      match expected, r.session.doc.outcome with
      | some e, .ok o =>
          if o.proved == e then return r
          else fail s!"the proof proves {o.proved.render}, not {e.render}"
      | some _, .error e => fail e
      | none, _ => return r
  | .laws path => do
      let text ← IO.FS.readFile path
      match Parser.lawFile text with
      | .ok ls =>
          return { r with session := { r.session with
            doc := { r.session.doc with laws := r.session.doc.laws ++ ls } } }
      | .error e => fail s!"{path}: {e}"
  | .load path => do
      let text ← IO.FS.readFile path
      match loadText text with
      | .ok d => return { r with session := { doc := d } }
      | .error e => fail s!"{path}: {e}"
  | .save path => do
      IO.FS.writeFile path (saveText r.session.doc)
      return r

/-- Run a whole script. -/
def runScript (r : Run) (cs : List (Nat × ScriptCmd)) : IO Run :=
  cs.foldlM (fun acc (n, c) => runCmd acc n c) r

/-- Where the shipped boolean law file lives, relative to the repository. -/
def lawFilePath : String := "Netty/laws/boolean.laws"

/-- Run the kernel's checks on itself: that every shipped law is a tautology,
that the law list survives being written out and read back, that the law file
on disk is the one compiled in, and that every demonstration script is the
command list `Netty.Replay` checks in Lean and still proves what it claims. -/
def selftest : IO Bool := do
  let mut ok := true
  let bad := Laws.boolean.filter fun l => !l.isTautology
  if bad.isEmpty then
    IO.println s!"laws: {Laws.boolean.length} boolean laws, all tautologies"
  else
    ok := false
    IO.eprintln s!"laws: not a tautology: {String.intercalate "; " (bad.map Law.render)}"
  match Parser.lawFile (renderLawFile Laws.boolean) with
  | .ok ls =>
      if ls == Laws.boolean then IO.println "laws: written out and read back unchanged"
      else
        ok := false
        IO.eprintln "laws: writing the law list out and reading it back changed it"
  | .error e =>
      ok := false
      IO.eprintln s!"laws: the written-out law list does not parse: {e}"
  -- Lean does not treat the law file as a build dependency, so a stale `.olean`
  -- would quietly ship yesterday's laws. Catch that here.
  if ← System.FilePath.pathExists lawFilePath then
    match Parser.lawFile (← IO.FS.readFile lawFilePath) with
    | .ok ls =>
        if ls == Laws.boolean then
          IO.println s!"laws: {lawFilePath} is the list compiled in"
        else
          ok := false
          IO.eprintln s!"laws: {lawFilePath} and the list compiled in differ; \
            rebuild Netty.Laws"
    | .error e =>
        ok := false
        IO.eprintln s!"laws: {lawFilePath}: {e}"
  else
    IO.println s!"laws: {lawFilePath} not found here; skipping the staleness check"
  for (name, text, expected) in Replay.demos do
    match Parser.script text with
    | .error e =>
        ok := false
        IO.eprintln s!"demo {name}: {e}"
    | .ok cs =>
        let commands := cs.filterMap fun (_, c) =>
          match c with | .doc dc => some dc | _ => none
        if commands != expected then
          ok := false
          IO.eprintln s!"demo {name}: the script and the command list Netty.Replay \
            checks are not the same"
        let quiet := cs.filter fun (_, c) =>
          match c with | .proof | .suggest | .context => false | _ => true
        let r ← runScript { session := { doc := { laws := Laws.boolean } } } quiet
        if r.ok then IO.println s!"demo {name}: script agrees with Netty.Replay, and proved"
        else ok := false
  return ok

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; IO.eprint usage; return 2
  | .ok o =>
    if o.help then IO.print usage; return 0
    if o.emitLaws then IO.print (renderLawFile Laws.boolean); return 0
    if o.selftest then return (if (← selftest) then 0 else 1)
    -- The laws in force: the built-in boolean list unless `--bare`, then each
    -- law file named on the command line.
    let mut laws := if o.bare then [] else Laws.boolean
    for path in o.laws do
      let text ← IO.FS.readFile path
      match Parser.lawFile text with
      | .ok ls => laws := laws ++ ls
      | .error e => IO.eprintln s!"{path}: {e}"; return 2
    if o.listLaws then
      IO.print (renderLawFile laws)
      return 0
    let mut doc : Doc := { laws := laws }
    match o.load with
    | some path =>
        match loadText (← IO.FS.readFile path) with
        | .ok d => doc := { d with laws := laws }
        | .error e => IO.eprintln s!"{path}: {e}"; return 2
    | none => pure ()
    let text ←
      match o.demo, o.script with
      | some name, _ =>
          match Demo.all.lookup name with
          | some t => pure t
          | none =>
              IO.eprintln s!"there is no demonstration named ‘{name}’; there are \
                {String.intercalate ", " (Demo.all.map (·.1))}"
              return 2
      | none, some path => IO.FS.readFile path
      | none, none => IO.getStdin >>= fun h => h.readToEnd
    match Parser.script text with
    | .error e => IO.eprintln e; return 2
    | .ok cs =>
        let r ← runScript { session := { doc := doc } } cs
        match o.save with
        | some path => IO.FS.writeFile path (saveText r.session.doc)
        | none => pure ()
        return (if r.ok then 0 else 1)
