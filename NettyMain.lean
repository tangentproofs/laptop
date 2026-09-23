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
  /-- Answer JSON requests on standard input instead of running a script. -/
  serve : Bool := false
  /-- Print the usage message. -/
  help : Bool := false

/-- How to call it. -/
def usage : String :=
"netty — the kernel of a Netty calculational proof session

usage: netty [options] [script]

  script              run this file of commands (default: standard input)
  --demo=NAME         run a built-in demonstration instead: portation,
                      discharge, gap, minimize, fold, merge
  --laws=FILE         add a law file; may be repeated
  --bare              start with no laws but those given by --laws
  --load=FILE         start from a saved proof file
  --save=FILE         write the session to a proof file when the script ends
  --list-laws         print the laws in force and stop
  --emit-laws         print the built-in boolean law list as a law file
  --selftest          check the shipped laws and the demonstrations, and stop
  --serve             answer one JSON request per line of standard input with
                      one line of JSON, for a user interface to talk to
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
    else if a == "--serve" then .ok { o with serve := true }
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

/-- Lines to offer the whole law list, to check that every suggestion it makes
is a sound step. Most are associations longer than the two operands most laws
are written with, which is what matching modulo associativity reads apart; all
of them have main operands that a law can be applied to as *parts*, in positive,
negative and neutral positions, which is what the margin connective of a part
rewrite has to get right. -/
def soundnessLines : List String :=
  ["x ∧ y ∧ z", "x ∨ y ∨ z", "x ∧ y ∧ z ∧ w", "x ∧ (y ∨ z)", "¬(x ∧ y ∧ z)",
   "x ⇒ y ∧ z", "(x ∧ y ∧ z) ∨ w", "x ∧ (y ∨ y)", "(x ⇒ y) = (y ⇐ x)"]

/-- Check the matching that the suggestions rest on. Every suggestion the
whole law list offers for those lines, under each of the three directions,
must be a *sound* step: the line joined to the suggestion by the connective it
would put in the margin has to hold under every assignment. That is the check on
matching modulo associativity, which reads a line apart in more ways than one,
and on applying a law to a part of a line, which turns the law's own connective
into the margin's according to the part's position — both could offer more than
they may. Two readings are witnessed by name: from `x ∧ y ∧ z`, specialization
must offer `x`, a first segment shorter than the left spine, as well as `x ∧ y`;
and from `x ∧ (y ∨ y)`, which idempotence cannot match as a whole, it must offer
`x ∧ y`, the fold of the second main operand. -/
def matchTest : IO Bool := do
  let mut ok := true
  let mut checked := 0
  let mut skipped := 0
  for text in soundnessLines do
    match Parser.expr text with
    | .error e =>
        ok := false
        IO.eprintln s!"matching: ‘{text}’: {e}"
    | .ok line =>
      for dir in [Dir.down, Dir.same, Dir.up] do
        match Doc.steps { laws := Laws.boolean } [.start .boolean dir line] with
        | .error e =>
            ok := false
            IO.eprintln s!"matching: ‘{text}’: {e}"
        | .ok d =>
          for s in d.suggestions do
            let step : Law := { stmt := Expr.bin s.op line s.result }
            if (step.stmt.mvars ++ step.stmt.vars).length > 8 then
              skipped := skipped + 1
            else if step.isTautology then
              checked := checked + 1
            else
              ok := false
              IO.eprintln s!"matching: ‘{s.law}’ offers an unsound step: {step.stmt.render}"
  if ok then
    IO.println s!"matching: {checked} suggested steps are sound\
      {if skipped == 0 then "" else s!" ({skipped} had too many names to check)"}"
  -- The reading that matching modulo associativity adds.
  match Parser.expr "x ∧ y ∧ z" with
  | .error e =>
      ok := false
      IO.eprintln s!"matching: {e}"
  | .ok line =>
    match Doc.steps { laws := Laws.boolean } [.start .boolean .down line] with
    | .error e =>
        ok := false
        IO.eprintln s!"matching: {e}"
    | .ok d =>
      let offered := (d.suggestions.filter (·.law == "specialization")).map (·.result.render)
      if offered == ["x", "x ∧ y"] then
        IO.println "matching: specialization reads x ∧ y ∧ z both ways"
      else
        ok := false
        IO.eprintln s!"matching: specialization offers {String.intercalate ", " offered}, \
          not x and x ∧ y"
  -- The reading that applying a law to a part of a line adds: idempotence
  -- cannot match `x ∧ (y ∨ y)`, whose main operator is `∧`, but it folds the
  -- second main operand where it stands.
  match Parser.expr "x ∧ (y ∨ y)" with
  | .error e =>
      ok := false
      IO.eprintln s!"matching: {e}"
  | .ok line =>
    match Doc.steps { laws := Laws.boolean } [.start .boolean .same line] with
    | .error e =>
        ok := false
        IO.eprintln s!"matching: {e}"
    | .ok d =>
      let folds := d.suggestions.filter fun s =>
        s.law == "idempotent" && s.result.render == "x ∧ y"
      if folds.length == 1 then
        IO.println "matching: idempotence folds y ∨ y inside x ∧ (y ∨ y)"
      else
        ok := false
        IO.eprintln s!"matching: idempotence offers {folds.length} ways to fold \
          y ∨ y inside x ∧ (y ∨ y), not one"
  return ok

/-- Check that the focus can land anywhere, through the request service a user
interface talks to — which is the path the web client's clickable line numbers
take. Zoom in, take a step, and the outer line must be reported `focusable`;
asking for it must succeed and leave the session at the outermost level, with
the subproof's own lines still there but no longer focusable. -/
def focusTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean } }
  let run (s : Session) (arg : String) : Session × Api.Response :=
    Api.respond s { op := "cmd", arg := arg }
  let mut s := fresh
  for arg in ["start ⇐ (a ⇒ b) ⇒ (a ⇒ a ∧ b)", "zoom 1", "apply discharge : = a ⇒ b"] do
    let (s', r) := run s arg
    s := s'
    if !r.ok then
      ok := false
      IO.eprintln s!"focus: ‘{arg}’: {r.error}"
  let before := Api.stateView s
  match before.lines.find? (fun l => l.index == 0) with
  | some l =>
      if l.focusable && before.depth == 1 then
        IO.println "focus: an outer line is focusable while the proof is zoomed in"
      else
        ok := false
        IO.eprintln s!"focus: at depth {before.depth}, line 0 is \
          {if l.focusable then "focusable" else "not focusable"}"
  | none =>
      ok := false
      IO.eprintln "focus: the answer has no line 0"
  let (s', r) := run s "focus 0"
  if !r.ok then
    ok := false
    IO.eprintln s!"focus: ‘focus 0’ at an outer level: {r.error}"
  else
    let after := r.state
    let focusables := (after.lines.filter (·.focusable)).map (·.index)
    -- The document has four lines now; the display draws two, because the
    -- subproof the click closed is a single law application and folds into the
    -- line above it. Both drawn lines are still focusable, under their own
    -- indices in the document.
    if after.focus == 0 && after.depth == 0 && after.lines.length == 2
        && focusables == [0, 3] then
      IO.println "focus: clicking it closed the subproof and left the focus there"
    else
      ok := false
      IO.eprintln s!"focus: after ‘focus 0’ the focus is {after.focus} at depth \
        {after.depth}, with {after.lines.length} lines drawn and \
        {focusables.length} focusable"
    -- A line of the subproof that has just been closed cannot be focused again.
    let (_, back) := run s' "focus 1"
    if back.ok then
      ok := false
      IO.eprintln "focus: a line of a closed subproof was focused"
    else
      IO.println "focus: a line of the closed subproof is refused"
  return ok

/-- Check that the display collapses reach a user interface, through the same
request service the web client talks to. The `fold` demonstration's four lines
are drawn as two, with `idempotent` moved up onto the line the subproof was
zoomed in from — which is line for line what `minimize`, the same step taken in
one application, draws. The `merge` demonstration's seven lines are drawn as
five, one level deep rather than two: the middle level held nothing but the
subproof, so it is not drawn at all. In both, a drawn line keeps its own index
in the document, which is what a click on it still means. -/
def collapseTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean } }
  let drawn := fun (name : String) => do
    let (_, r) := Api.respond fresh { op := "demo", arg := name }
    if !r.ok then
      IO.eprintln s!"collapse: demo {name}: {r.error}"
      return (none : Option (List (Nat × Nat × String)))
    return some (r.state.lines.map fun l => (l.index, l.depth, l.note))
  match ← drawn "fold", ← drawn "minimize" with
  | some f, some m =>
      if f == [(0, 0, "idempotent"), (3, 0, "")] then
        IO.println "collapse: a one-step subproof folds into its parent line"
      else
        ok := false
        IO.eprintln s!"collapse: fold draws {repr f}"
      if f.map (fun (_, d, n) => (d, n)) == m.map (fun (_, d, n) => (d, n)) then
        IO.println "collapse: the long way round is drawn as the short way round"
      else
        ok := false
        IO.eprintln s!"collapse: fold draws {repr f}, minimize draws {repr m}"
  | _, _ => ok := false
  match ← drawn "merge" with
  | some g =>
      if g == [(0, 0, ""), (2, 1, "idempotent"), (3, 1, "double negation"),
               (4, 1, ""), (6, 0, "")] then
        IO.println "collapse: two zoom-ins matched by two zoom-outs draw as one"
      else
        ok := false
        IO.eprintln s!"collapse: merge draws {repr g}"
  | none => ok := false
  return ok

/-- Check the request service a user interface talks to: every demonstration
replays through it, a session survives being saved and loaded back through it,
and a request the service does not know is refused rather than passed over. -/
def apiTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean } }
  for (name, _) in Demo.all do
    let (s, r) := Api.respond fresh { op := "demo", arg := name }
    if !r.ok then
      ok := false
      IO.eprintln s!"api: demo {name}: {r.error}"
    else if r.state.proofPane != s.doc.renderProof then
      ok := false
      IO.eprintln s!"api: demo {name}: the answer's proof pane is not the document's"
    else
      let (_, saved) := Api.respond s { op := "save" }
      let (s', loaded) := Api.respond fresh { op := "load", arg := saved.save }
      if !loaded.ok then
        ok := false
        IO.eprintln s!"api: demo {name}: loading what save wrote: {loaded.error}"
      else if s'.doc != s.doc then
        ok := false
        IO.eprintln s!"api: demo {name}: saving and loading through the service \
          changed the document"
      else
        IO.println s!"api: demo {name} replays, and saves and loads unchanged"
  let (_, answer) := Api.respondText fresh "{\"id\": 7, \"op\": \"fly\"}"
  match Lean.Json.parse answer >>= fun j => do
      return ((← j.getObjValAs? Nat "id"), (← j.getObjValAs? Bool "ok")) with
  | .ok (7, false) => IO.println "api: an unknown request is refused, with its id"
  | .ok _ =>
      ok := false
      IO.eprintln "api: an unknown request was not refused"
  | .error e =>
      ok := false
      IO.eprintln s!"api: the answer to an unknown request does not parse: {e}"
  return ok

/-- Run the kernel's checks on itself: that every shipped law is a tautology,
that the law list survives being written out and read back, that the law file
on disk is the one compiled in, that every demonstration script is the command
list `Netty.Replay` checks in Lean and still proves what it claims, that every
suggestion the law list offers is a sound step, that the focus can land on an
outer line through the request service, and that the display collapses reach it
too. -/
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
  if !(← matchTest) then ok := false
  if !(← focusTest) then ok := false
  if !(← collapseTest) then ok := false
  if !(← apiTest) then ok := false
  return ok

/-- Answer JSON requests until standard input ends: one request per line in,
one answer per line out. The requests are `Netty.Api`'s, and every change to
the document still goes through `Netty.Doc.step`; this loop is the reading, the
writing and the flushing, and nothing else. -/
def serve (doc : Doc) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut session : Session := { doc := doc }
  repeat
    let line ← stdin.getLine
    -- `getLine` returns the empty string only at end of input.
    if line.isEmpty then break
    if (Parser.trim line).isEmpty then continue
    let (session', answer) := Api.respondText session line
    session := session'
    stdout.putStrLn answer
    stdout.flush

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
    if o.serve then
      serve doc
      return 0
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
