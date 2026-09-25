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
                      discharge, gap, minimize, segment, segfold, fold,
                      merge
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
  apply … with x := E, y := F                   …supplying the law variables the
                                                match left unconstrained
  direct CONNECTIVE EXPRESSION                  type the next line in
  zoom N                                        zoom in to the N-th operand
  zoom S:L                                      …or to the L operands from the
                                                S-th, a contiguous segment of an
                                                association
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

/-- Where the number law list lives, for the same staleness check. -/
def numberLawFilePath : String := "Netty/laws/number.laws"

/-- Where the quantifier law list lives, for the same staleness check. -/
def quantifierLawFilePath : String := "Netty/laws/quantifier.laws"

/-- Lines to offer the whole law list, to check that every suggestion it makes
is a sound step. Most are associations longer than the two operands most laws
are written with, which is what matching modulo associativity reads apart and
modulo symmetry rearranges; all of them have main operands that a law can be
applied to as *parts*, in positive, negative and neutral positions, and the
longer associations among them have contiguous *segments* as well, which is what
the margin connective of a part rewrite has to get right in both cases. Two write
a unit where a law need not mention one, which is what matching modulo the
identity element strikes out, and the last repeats an operand in the middle of an
association, which is the shape only a segment site reaches. -/
def soundnessLines : List String :=
  ["x ∧ y ∧ z", "x ∨ y ∨ z", "x ∧ y ∧ z ∧ w", "x ∧ (y ∨ z)", "¬(x ∧ y ∧ z)",
   "x ⇒ y ∧ z", "(x ∧ y ∧ z) ∨ w", "x ∧ (y ∨ y)", "(x ⇒ y) = (y ⇐ x)",
   "x ∧ ⊤ ∧ y", "x ∨ ⊥ ∨ y", "x ∧ y ∧ y ∧ z"]

/-- Check the matching that the suggestions rest on. Every suggestion the
whole law list offers for those lines, under each of the three directions,
must be a *sound* step: the line joined to the suggestion by the connective it
would put in the margin has to hold under every assignment. That is the check on
matching modulo associativity, symmetry and the identity element, which reads a
line apart, rearranges it and strikes its units out, and on applying a law to a
part of a line, which turns the law's own connective into the margin's according
to the part's position — all of them could offer more than they may. Four
readings are witnessed by name: from `x ∧ y ∧ z`, specialization must offer
every sub-conjunction — the three single conjuncts before the three pairs, which
is `Doc.rank` putting the shorter line first; from `x ∧ (y ∨ y)`, which idempotence cannot match as
a whole, it must offer `x ∧ y`, the fold of the second main operand; from
`x ∧ y ∧ y ∧ z`, which idempotence matches neither whole nor at any single
operand, it must offer `x ∧ y ∧ z`, the fold of the contiguous *segment*
`y ∧ y`; and a law written with a unit — `a ∧ ⊤`, here as a law list of its own
— must read a line that never writes one. -/
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
            -- A conditional reading is a sound step *given its premise* — that is
            -- what the gap it leaves records — so what has to be a tautology is
            -- the premise implying the step. For a reading that needs nothing
            -- that is the step itself, as it always was.
            let claim := Expr.bin s.op line s.result
            let step : Law := { stmt :=
              match s.premise with | some q => Expr.bin .imp q claim | none => claim }
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
      if offered == ["x", "z", "y", "x ∧ y", "y ∧ z", "x ∧ z"] then
        IO.println "matching: specialization reads every sub-conjunction of x ∧ y ∧ z"
      else
        ok := false
        IO.eprintln s!"matching: specialization offers {String.intercalate ", " offered}, \
          not every sub-conjunction of x ∧ y ∧ z"
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
  -- The reading a contiguous *segment* of an association adds: the middle two
  -- conjuncts of `x ∧ y ∧ y ∧ z` are a site of their own, and idempotence folds
  -- them where they stand. Neither the whole line nor any single main operand —
  -- the bare identifiers `x`, `y`, `y`, `z` — matches, so no other site can make
  -- this step.
  match Parser.expr "x ∧ y ∧ y ∧ z" with
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
        s.law == "idempotent" && s.result.render == "x ∧ y ∧ z"
      let whole := Expr.matchAll (Expr.bin .and (Expr.mvar "a") (Expr.mvar "a")) line []
      let parts := line.operands.filter fun o =>
        !(Expr.matchAll (Expr.bin .and (Expr.mvar "a") (Expr.mvar "a")) o []).isEmpty
      if folds.length == 1 && whole.isEmpty && parts.isEmpty then
        IO.println "matching: idempotence folds the segment y ∧ y inside x ∧ y ∧ y ∧ z, \
          which neither the whole line nor a single operand can reach"
      else
        ok := false
        IO.eprintln s!"matching: idempotence offers {folds.length} ways to fold the \
          segment y ∧ y inside x ∧ y ∧ y ∧ z, with {whole.length} whole-line and \
          {parts.length} single-operand matches"
  -- The reading matching modulo the identity element adds: a law written with a
  -- unit reads a line that never writes one. `a ∧ ⊤ ⇒ ¬¬a` is not a law of the
  -- shipped list, so it stands here as a law list of its own; against the line
  -- `y` it must offer `¬¬y`, and a law written without the unit must not.
  match Parser.lawFile "unit: a ∧ ⊤ ⟹ ¬¬a\nno unit: a ∧ b ⟹ ¬¬a\n", Parser.expr "y" with
  | .ok ls, .ok line =>
      match Doc.steps { laws := ls } [.start .boolean .down line] with
      | .error e =>
          ok := false
          IO.eprintln s!"matching: {e}"
      | .ok d =>
        let offered := d.suggestions.map fun s => (s.law, s.result.render)
        if offered == [("unit", "¬¬y")] then
          IO.println "matching: a law written a ∧ ⊤ reads the line y, and a ∧ b does not"
        else
          ok := false
          IO.eprintln s!"matching: against y the unit laws offer \
            {String.intercalate ", " (offered.map fun (l, r) => s!"{l}: {r}")}, \
            not just the one written with ⊤"
  | _, _ =>
      ok := false
      IO.eprintln "matching: the unit law list does not parse"
  return ok

/-- Check that the focus can land anywhere, through the request service a user
interface talks to — which is the path the web client's clickable line numbers
take. Zoom in, take a step, and the outer line must be reported `focusable`;
asking for it must succeed and leave the session at the outermost level, with
the subproof's own lines still there. Then go back *into* that subproof by
asking for one of its lines, which takes the zoom out back; and check that the
same click is refused once a line has been written after the subproof closed,
because taking the zoom out back would take that line with it. -/
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
    -- A line of the subproof that has just been closed re-opens it: the zoom
    -- out goes away again, the level is innermost once more, and the focus is
    -- on the line that was asked for. All three lines are drawn now, because a
    -- level holding the focus is never collapsed.
    let (_, back) := run s' "focus 1"
    if !back.ok then
      ok := false
      IO.eprintln s!"focus: ‘focus 1’ back into the closed subproof: {back.error}"
    else if back.state.focus == 1 && back.state.depth == 1
        && back.state.lines.length == 3 then
      IO.println "focus: a line of the closed subproof re-opens it"
    else
      ok := false
      IO.eprintln s!"focus: after ‘focus 1’ the focus is {back.state.focus} at \
        depth {back.state.depth}, with {back.state.lines.length} lines drawn"
    -- But not once work has been written after the subproof closed: from the
    -- state where it is closed, put a line in after the line the zoom out
    -- wrote, and the same click must be refused — undoing the zoom out would
    -- undo that line.
    let (t1, _) := run s' "focus 3"
    let (t2, r2) := run t1 "direct = ⊤"
    if !r2.ok then
      ok := false
      IO.eprintln s!"focus: writing a line after the closed subproof: {r2.error}"
    else
      let (_, refused) := run t2 "focus 1"
      if refused.ok then
        ok := false
        IO.eprintln "focus: a subproof closed before later work was re-opened"
      else
        IO.println "focus: with work written after it, the subproof is refused"
      match (Api.stateView t2).lines.find? (fun l => l.index == 3) with
      | some l =>
          if l.focusable then
            IO.println "focus: the line the zoom out wrote is focusable either way"
          else
            ok := false
            IO.eprintln "focus: the line the zoom out wrote is not focusable"
      | none => pure ()
  return ok

/-- Check the order the suggestions come in, on a line long enough for the order
to matter: `x ∧ y ∧ y ∧ z` under the whole shipped law list, which offers a couple
of hundred steps from nine places.

`Doc.rank` is a heuristic, so what is checked is mostly not which step is first
but that the order really is the order the rule describes: the keys never go
backwards (applicable before unconstrained, then fewer unconstrained variables,
then the shorter line the step writes, then the more specific place), ranking the
ranked list changes nothing — which is what it means for the order to be total and
the sort stable — and asking twice gives the same list, since a user's `apply #N`
has to mean the same thing the second time they look.

The point of putting the shorter line ahead of the place is checked head on:
`x ∧ y ∧ z`, the fold that neither the whole line nor any single operand can make,
is the *third* of the 227 steps offered. Only two come before it, and both write a
line of the same length: `distributive` contracting the whole line. When the place
outranked the length this fold was the 124th, behind every way of reassociating
and commuting the whole line. -/
def rankTest : IO Bool := do
  let mut ok := true
  match Parser.expr "x ∧ y ∧ y ∧ z" with
  | .error e =>
      IO.eprintln s!"rank: {e}"
      return false
  | .ok line =>
    match Doc.steps { laws := Laws.boolean } [.start .boolean .same line] with
    | .error e =>
        IO.eprintln s!"rank: {e}"
        return false
    | .ok d =>
      let ss := d.suggestions
      let key := fun (s : Suggestion) =>
        [if s.holes.isEmpty then 0 else 1, s.holes.length, s.result.size, s.part.rank]
      -- Lexicographic ≤ on those keys, and whether a list of them ever goes back.
      let rec le : List Nat → List Nat → Bool
        | [], _ => true
        | _, [] => false
        | a :: as, b :: bs => if a == b then le as bs else a < b
      let keys := ss.map key
      let backwards := (List.range keys.length).filter fun i =>
        match keys[i]?, keys[i + 1]? with
        | some a, some b => !le a b
        | _, _ => false
      if backwards.isEmpty then
        IO.println s!"rank: the {ss.length} suggestions for x ∧ y ∧ y ∧ z are in \
          ranking order"
      else
        ok := false
        IO.eprintln s!"rank: the order goes backwards after suggestion \
          {String.intercalate ", " (backwards.map toString)}"
      if Doc.rank ss == ss && d.suggestions == ss then
        IO.println "rank: ranking the ranked list changes nothing, and asking twice \
          gives the same list"
      else
        ok := false
        IO.eprintln "rank: ranking the ranked list is not the ranked list"
      -- Applicable before unconstrained is the key a user sees most: the greyed
      -- rows are the tail of the list and nothing applicable hides among them.
      let blocked := ss.dropWhile (·.holes.isEmpty)
      if blocked.all (fun s => !s.holes.isEmpty) then
        IO.println s!"rank: every one of the {ss.length - blocked.length} applicable \
          steps comes before all {blocked.length} that leave a variable free"
      else
        ok := false
        IO.eprintln "rank: an applicable suggestion comes after an unconstrained one"
      -- The fold of the middle two conjuncts is the third step offered, and every
      -- step before it writes a line no longer than it does. It is also the first
      -- step offered on a *run* of operands, its run being shorter than the two
      -- that overlap it.
      let fold := ss.findIdx? fun s =>
        s.result.render == "x ∧ y ∧ z" && s.part.render == "1:2"
      let ahead := (ss.take 2).all fun s => s.result.size ≤ 5
      let firstRun := (ss.filter fun s => s.part.rank ≥ 2).head?
      if fold == some 2 && ahead
          && (firstRun.map fun s => s.part.render) == some "1:2" then
        IO.println "rank: the fold of the run y ∧ y is the third step offered, \
          behind two whole-line steps that write a line just as short"
      else
        ok := false
        let sizes := String.intercalate ", " ((ss.take 2).map fun s => toString s.result.size)
        IO.eprintln s!"rank: the fold of the run y ∧ y is at {repr fold}, the two \
          steps ahead of it write lines of size {sizes}, and the first step on a \
          run is at {repr (firstRun.map fun s => s.part.render)}"
  return ok

/-- Check the click path a window takes to zoom in, through the same request
service the web client talks to.

The answer gives each line the parts a click may zoom in to
(`Api.LineView.zooms`), each with the name the *script language* calls it by, so
a window sends `zoom` and that name and never composes one itself. This checks
that the parts offered for `x ∧ y ∧ y ∧ z` are the kernel's own — every main
operand, then every contiguous run of them, which is `Doc.parts` — that clicking
each of them is accepted and opens a level whose first line is the part the
button was labelled with, that clicking the run `1:2` gains the operands outside
it as context, and that a line which is not the one before the focus offers
nothing to a click at all. -/
def zoomTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean } }
  let (s, r) := Api.respond fresh { op := "cmd", arg := "start = x ∧ y ∧ y ∧ z" }
  if !r.ok then
    IO.eprintln s!"zoom: starting the line: {r.error}"
    return false
  match r.state.lines with
  | [l] =>
      let offered := l.zooms.map fun z => (z.name, z.text)
      if l.zoomable && offered ==
          [("0", "x"), ("1", "y"), ("2", "y"), ("3", "z"),
           ("0:2", "x ∧ y"), ("0:3", "x ∧ y ∧ y"), ("1:2", "y ∧ y"),
           ("1:3", "y ∧ y ∧ z"), ("2:2", "y ∧ z")] then
        IO.println "zoom: a window is offered every main operand and every run of them"
      else
        ok := false
        IO.eprintln s!"zoom: x ∧ y ∧ y ∧ z offers \
          {String.intercalate ", " (offered.map fun (n, t) => s!"{n} ({t})")}"
      -- Every part the window offers must be one the kernel accepts, and must
      -- open the level its button was labelled with.
      for z in l.zooms do
        let (_, a) := Api.respond s { op := "cmd", arg := s!"zoom {z.name}" }
        if !a.ok then
          ok := false
          IO.eprintln s!"zoom: clicking ‘{z.text}’ (zoom {z.name}): {a.error}"
        else
          match a.state.lines.getLast? with
          | some last =>
              if !(a.state.depth == 1 && last.expr == z.text) then
                ok := false
                IO.eprintln s!"zoom: clicking ‘{z.text}’ (zoom {z.name}) opened \
                  ‘{last.expr}’ at depth {a.state.depth}"
          | none =>
              ok := false
              IO.eprintln s!"zoom: clicking ‘{z.text}’ (zoom {z.name}) left no lines"
      IO.println s!"zoom: each of the {l.zooms.length} parts opens the level its button names"
      -- The run `y ∧ y` is the one no single operand can reach. Clicking it
      -- gains `x` and `z` — the operands outside the run — and leaves the outer
      -- line with nothing to click, since it is no longer the line before the
      -- focus.
      match l.zooms.find? (·.name == "1:2") with
      | none =>
          ok := false
          IO.eprintln "zoom: the run 1:2 is not offered"
      | some z =>
          let (_, a) := Api.respond s { op := "cmd", arg := s!"zoom {z.name}" }
          let outer := (a.state.lines.find? (·.index == 0)).map (fun l => l.zooms.length)
          if a.ok && a.state.context == ["x", "z"] && outer == some 0 then
            IO.println "zoom: clicking a run gains the operands outside it, and the \
              outer line stops offering a click"
          else
            ok := false
            IO.eprintln s!"zoom: after clicking the run, the context is \
              {String.intercalate ", " a.state.context} and the outer line offers \
              {repr outer}"
  | ls =>
      ok := false
      IO.eprintln s!"zoom: the started proof draws {ls.length} lines, not one"
  return ok

/-- Check that the display collapses reach a user interface, through the same
request service the web client talks to. The `fold` demonstration's four lines
are drawn as two, with `idempotent` moved up onto the line the subproof was
zoomed in from — which is line for line what `minimize`, the same step taken in
one application, draws; and `segfold`, which zooms into a contiguous *segment* of
an association and splices the subproof back, draws what `segment` draws for the
same reason. The `merge` demonstration's seven lines are drawn as
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
  -- The same, for a zoom into a contiguous *segment* of an association: the
  -- subproof `segfold` opens on `y ∧ y` folds into the line it was zoomed in
  -- from, and what is left is what `segment` — the same step as one rewrite of
  -- that segment — draws. This is the segment zoom driven end to end through the
  -- request service, splice and all.
  match ← drawn "segfold", ← drawn "segment" with
  | some z, some r =>
      if z.map (fun (_, d, n) => (d, n)) == r.map (fun (_, d, n) => (d, n)) then
        IO.println "collapse: zooming into a segment draws as rewriting it in place"
      else
        ok := false
        IO.eprintln s!"collapse: segfold draws {repr z}, segment draws {repr r}"
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

/-- Check that every suggestion says *where* it would rewrite, through the
request service the window talks to.

`Suggestion.part` has carried the site since the ranking, and `SuggestionView`
now hands it on as a `PartView` — the very shape the zoom targets come in — so a
window can draw the place a step would rewrite as the same part of the same line
a click would zoom into. On `x ∧ y ∧ y ∧ z` the fold that only a run can make
must be credited to the run `1:2` and read `y ∧ y`, a law that pads the whole
line must be credited to the whole line, and *every* site must be either the
whole line or one of the parts the same answer offers as a zoom target: a
highlight can then always be drawn, and it cannot name a part the line does not
have.
-/
def siteTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean } }
  let (_, r) := Api.respond fresh { op := "cmd", arg := "start = x ∧ y ∧ y ∧ z" }
  if !r.ok then
    IO.eprintln s!"site: starting the line: {r.error}"
    return false
  let st := r.state
  match st.lines with
  | [l] =>
      -- The fold of the run `y ∧ y`, which neither the whole line nor any single
      -- operand can make: its site is the run, named as the zoom button is.
      match st.suggestions.find? fun g =>
          g.law == "idempotent" && g.result == "x ∧ y ∧ z" with
      | some g =>
          if (g.site.name, g.site.text, g.site.start, g.site.len) == ("1:2", "y ∧ y", 1, 2) then
            IO.println "site: the fold of a run is credited to that run"
          else
            ok := false
            IO.eprintln s!"site: the fold of y ∧ y is credited to \
              ‘{g.site.name}’ (‘{g.site.text}’, {g.site.start}+{g.site.len})"
      | none =>
          ok := false
          IO.eprintln "site: the fold of the run y ∧ y is not offered at all"
      -- A law that reads the whole line is credited to the whole line, which is
      -- no run of operands at all and says so with `len = 0`.
      match st.suggestions.find? fun g =>
          g.law == "double negation" && g.result == "¬¬(x ∧ y ∧ y ∧ z)" with
      | some g =>
          if g.site.len == 0 && g.site.text == "x ∧ y ∧ y ∧ z" then
            IO.println "site: a step on the whole line is credited to the whole line"
          else
            ok := false
            IO.eprintln s!"site: padding the whole line is credited to \
              ‘{g.site.name}’ (‘{g.site.text}’, {g.site.start}+{g.site.len})"
      | none =>
          ok := false
          IO.eprintln "site: the padding of the whole line is not offered at all"
      -- And every site is a part of *this* line: the whole line, or one of the
      -- parts the same answer offers as a zoom target, under that part's name.
      let names := l.zooms.map (·.name)
      let stray := st.suggestions.filter fun g =>
        g.site.len != 0 && !(names.contains g.site.name)
      if stray.isEmpty then
        IO.println s!"site: all {st.suggestions.length} sites are parts the same \
          line offers to a click"
      else
        ok := false
        IO.eprintln s!"site: {stray.length} suggestions name a part the line does \
          not offer, the first ‘{(stray.head!).site.name}’"
      -- The site is the part it names, letter for letter: what a window would
      -- highlight is what a click on that part would open.
      let wrong := st.suggestions.filter fun g =>
        g.site.len != 0 && !(l.zooms.any fun z => z.name == g.site.name && z.text == g.site.text)
      if wrong.isEmpty then
        IO.println "site: and each reads as the part of the line it names"
      else
        ok := false
        IO.eprintln s!"site: {wrong.length} sites read differently from the part \
          they name"
  | ls =>
      ok := false
      IO.eprintln s!"site: the started proof draws {ls.length} lines, not one"
  return ok

/-- Check the conditional reading of a law at the number level, through the
request service the window talks to.

A law such as `x ≤ x + y ⇐ 0 ≤ y` has `⇐` for its main operator, so on its own it
is a step a *boolean* line can take. Its conditional reading puts the consequent's
`≤` in a number margin and leaves `0 ≤ y` over as a premise. Two things must
follow. Inside `0 ≤ m ⇒ n ≤ n + m`, where zooming in has put `0 ≤ m` in the
context, the reading that needs `0 ≤ m` must carry no premise and the one that
needs `0 ≤ n` must carry its own, in the same pane, off the same line. And on a
number proof with nothing in force to settle it, taking the step must write the
line, leave the document's warning sign, say on the line what would close it, and
claim nothing. -/
def conditionalTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean ++ Laws.number } }
  let run := fun (s : Session) (arg : String) => Api.respond s { op := "cmd", arg := arg }
  -- Two zooms in: to the consequent, where `0 ≤ m` becomes context, and then to
  -- `n + m`, which is a number level.
  let mut s := fresh
  for arg in ["start ⇐ 0 ≤ m ⇒ n ≤ n + m", "zoom 1", "zoom 1"] do
    let (s', r) := run s arg
    s := s'
    if !r.ok then
      ok := false
      IO.eprintln s!"conditional: ‘{arg}’: {r.error}"
  let inner := Api.stateView s
  let ups := inner.suggestions.filter fun g => g.law == "upper bound" && g.holes.isEmpty
  match ups.filter (fun g => g.premise == ""), ups.filter (fun g => g.premise != "") with
  | [clean], [gappy] =>
      if clean.result == "n" && gappy.result == "m" && gappy.premise == "0 ≤ n" then
        IO.println "conditional: one law, one line, one reading discharged and one gapped"
      else
        ok := false
        IO.eprintln s!"conditional: the two readings are ‘{clean.result}’ and \
          ‘{gappy.result}’ needing ‘{gappy.premise}’"
  | cs, gs =>
      ok := false
      IO.eprintln s!"conditional: {cs.length} readings need nothing and {gs.length} \
        need something, not one of each"
  let (s2, r2) := run s "apply upper bound : ≥ n"
  if !r2.ok then
    ok := false
    IO.eprintln s!"conditional: taking the discharged step: {r2.error}"
  else if r2.state.lines.all (fun l => !l.gap) then
    IO.println "conditional: taking the discharged one leaves no gap"
  else
    ok := false
    IO.eprintln "conditional: the discharged step left a gap"
  let _ := s2
  -- The same law, on the same line, with nothing in force to settle its premise.
  let mut t := fresh
  for arg in ["start number ≥ n + m", "apply upper bound : ≥ n"] do
    let (t', r) := run t arg
    t := t'
    if !r.ok then
      ok := false
      IO.eprintln s!"conditional: ‘{arg}’: {r.error}"
  let after := Api.stateView t
  match after.lines.find? (fun l => l.index == 0) with
  | some l =>
      if l.gap && l.premise == "0 ≤ m" && l.note == "!" && !after.proved then
        IO.println "conditional: with nothing to settle it, the step leaves the \
          premise as a gap and claims nothing"
      else
        ok := false
        IO.eprintln s!"conditional: line 0 has gap {l.gap}, premise ‘{l.premise}’, \
          note ‘{l.note}’, and the proof is {if after.proved then "proved" else "unproved"}"
  | none =>
      ok := false
      IO.eprintln "conditional: the answer has no line 0"
  -- The line the step wrote is the one the law licenses, and it carries its name.
  match after.lines.find? (fun l => l.index == 1) with
  | some l =>
      if l.expr == "n" && l.why == "upper bound" then
        IO.println "conditional: and the step is recorded, not refused"
      else
        ok := false
        IO.eprintln s!"conditional: line 1 is ‘{l.expr}’ by ‘{l.why}’"
  | none =>
      ok := false
      IO.eprintln "conditional: the answer has no line 1"
  -- The same machinery at the *boolean* level, where what a conditional reading
  -- needs comes from the context: two zoom-ins put `a ⇒ (b ⇒ c)` and `a` in
  -- force, and a context law is ground, so its conditional reading has nothing
  -- left unconstrained. It rewrites the operand `b` of `b ⇒ c` to `c`, and what
  -- licenses it is the other fact in force.
  let mut u := fresh
  for arg in ["start ⇐ a ⇒ ((a ⇒ (b ⇒ c)) ⇒ (b ⇒ c))", "zoom 1", "zoom 1"] do
    let (u', r) := run u arg
    u := u'
    if !r.ok then
      ok := false
      IO.eprintln s!"conditional: ‘{arg}’: {r.error}"
  let deep := Api.stateView u
  match (deep.suggestions.filter fun g =>
      g.law == "context" && g.holes.isEmpty && g.result == "c ⇒ c") with
  | [g] =>
      if g.premise == "" then
        IO.println "conditional: a context law rewrites a boolean line, its premise \
          settled by another fact in force"
      else
        ok := false
        IO.eprintln s!"conditional: the context's reading still needs ‘{g.premise}’"
  | gs =>
      ok := false
      IO.eprintln s!"conditional: {gs.length} context readings write ‘c ⇒ c’, not one"
  let (_, r3) := run u "apply context : ⇐ c ⇒ c"
  if !r3.ok then
    ok := false
    IO.eprintln s!"conditional: taking the boolean conditional step: {r3.error}"
  else if r3.state.lines.all (fun l => !l.gap) then
    IO.println "conditional: taking it leaves no gap either"
  else
    ok := false
    IO.eprintln "conditional: the discharged boolean step left a gap"
  -- Drop the outer `a ⇒ …` and nothing settles the premise: the same reading is
  -- offered with it, and taking it leaves the warning sign.
  let mut v := fresh
  for arg in ["start ⇐ (a ⇒ (b ⇒ c)) ⇒ (b ⇒ c)", "zoom 1", "apply context : ⇐ c ⇒ c"] do
    let (v', r) := run v arg
    v := v'
    if !r.ok then
      ok := false
      IO.eprintln s!"conditional: ‘{arg}’: {r.error}"
  let vv := Api.stateView v
  match vv.lines.find? (fun l => l.index == 1) with
  | some l =>
      if l.gap && l.premise == "a" && !vv.proved then
        IO.println "conditional: without that fact the boolean reading leaves the \
          premise as a gap and claims nothing"
      else
        ok := false
        IO.eprintln s!"conditional: line 1 has gap {l.gap}, premise ‘{l.premise}’, and \
          the proof is {if vv.proved then "proved" else "unproved"}"
  | none =>
      ok := false
      IO.eprintln "conditional: the boolean answer has no line 1"
  return ok

/-- Check the document's small dialog box through the request service the window
talks to: a suggestion that leaves a law variable free is offered, refused while
the variable is missing, and taken once it is supplied.

Inside `(x ⇒ y) ⇒ (x ∧ z ⇒ y ∧ z)`, where zooming in has put `x ⇒ y` in the
context, monotonicity offers to rewrite the operand `x ∧ z` and is greyed: nothing
on the line says what `b` is. `apply #N` must be refused, `apply #N with b := y`
must go through, and because the premise is then `x ⇒ y` — which the context
settles — it must leave no gap. On a bare line, where nothing settles it, the same
binding must still leave the warning sign and claim nothing. -/
def dialogTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean } }
  let run := fun (s : Session) (arg : String) => Api.respond s { op := "cmd", arg := arg }
  let mut s := fresh
  for arg in ["start ⇐ (x ⇒ y) ⇒ (x ∧ z ⇒ y ∧ z)", "zoom 1"] do
    let (s', r) := run s arg
    s := s'
    if !r.ok then
      ok := false
      IO.eprintln s!"dialog: ‘{arg}’: {r.error}"
  let st := Api.stateView s
  match st.suggestions.filter fun g =>
      g.law == "monotonic" && g.result == "b ∧ z ⇒ y ∧ z" with
  | [g] =>
      if g.holes == ["b"] && g.premise == "x ⇒ b" then
        IO.println "dialog: a monotonicity reading is offered, waiting for b"
      else
        ok := false
        IO.eprintln s!"dialog: that reading leaves {g.holes.length} free and needs \
          ‘{g.premise}’"
      -- Refused while `b` is missing …
      let (_, bare) := run s s!"apply #{g.index}"
      if bare.ok then
        ok := false
        IO.eprintln "dialog: a suggestion with a free variable was applied"
      else
        IO.println "dialog: and refused until it is given"
      -- … and a binding for a variable it has not got is refused too.
      let (_, stray) := run s s!"apply #{g.index} with q := y"
      if stray.ok then
        ok := false
        IO.eprintln "dialog: a binding for a variable the suggestion has not was taken"
      else
        IO.println "dialog: a binding it has no variable for is refused"
      -- With the binding it is a step, and the context settles what it needs.
      let (_, bound) := run s s!"apply #{g.index} with b := y"
      if !bound.ok then
        ok := false
        IO.eprintln s!"dialog: ‘apply #{g.index} with b := y’: {bound.error}"
      else
        let after := bound.state
        let wrote := after.lines.any fun l => l.expr == "y ∧ z ⇒ y ∧ z"
        if wrote && after.lines.all (fun l => !l.gap) then
          IO.println "dialog: supplying b takes the step, and the context settles \
            the premise it needs"
        else
          ok := false
          IO.eprintln s!"dialog: after the binding the line was \
            {if wrote then "written" else "not written"} and there \
            {if after.lines.all (fun l => !l.gap) then "is no gap" else "is a gap"}"
  | gs =>
      ok := false
      IO.eprintln s!"dialog: {gs.length} monotonicity readings write ‘b ∧ z ⇒ y ∧ z’, not one"
  -- The same law and binding on a bare line: nothing settles the premise, so the
  -- step still leaves the warning sign and the proof still claims nothing.
  let (u, r0) := run fresh "start ⇒ x ∧ z"
  if !r0.ok then
    ok := false
    IO.eprintln s!"dialog: ‘start ⇒ x ∧ z’: {r0.error}"
  match (Api.stateView u).suggestions.filter fun g =>
      g.law == "monotonic" && g.result == "b ∧ z" with
  | [g] =>
      let (_, bound) := run u s!"apply #{g.index} with b := y"
      if !bound.ok then
        ok := false
        IO.eprintln s!"dialog: on a bare line: {bound.error}"
      else
        let after := bound.state
        match after.lines.find? (fun l => l.index == 0) with
        | some l =>
            if l.gap && l.premise == "x ⇒ y" && !after.proved then
              IO.println "dialog: with nothing to settle it the step still leaves the \
                premise as a gap"
            else
              ok := false
              IO.eprintln s!"dialog: line 0 has gap {l.gap} and premise ‘{l.premise}’"
        | none =>
            ok := false
            IO.eprintln "dialog: the answer has no line 0"
  | gs =>
      ok := false
      IO.eprintln s!"dialog: {gs.length} monotonicity readings write ‘b ∧ z’ on a bare line"
  return ok

/-- Check the document's `if … then … else … fi` through the request service the
window talks to: that it travels as text, that the window is offered its three
pieces as three places to click, and that a law of the list rewrites one.

The form brackets itself, so `start = if T then x else y fi` is one line of the
script language and needs no new request. Its three main operands are the
condition and the two branches, so the answer must offer three parts and three
zoom targets, and `case base` must take the line to `x`. -/
def ifTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean } }
  let run := fun (s : Session) (arg : String) => Api.respond s { op := "cmd", arg := arg }
  -- Read and written as one. This is checked here rather than in Lean because the
  -- parser is a `partial def`, which the kernel cannot reduce; script parsing has
  -- always been checked at run time for the same reason.
  match Parser.expr "if b then x else y fi", Parser.expr "if b then x else y fi ∧ z" with
  | .ok one, .ok two =>
      let want := Expr.cond (Expr.var "b") (Expr.var "x") (Expr.var "y")
      if one == want && one.render == "if b then x else y fi"
          && two == Expr.bin .and want (Expr.var "z") then
        IO.println "if: it parses, renders as it was written, and ‘fi’ closes it"
      else
        ok := false
        IO.eprintln s!"if: parsed ‘{one.render}’ and ‘{two.render}’"
  | a, b =>
      ok := false
      IO.eprintln s!"if: it does not parse: \
        {match a with | .error e => e | .ok _ => ""}\
        {match b with | .error e => e | .ok _ => ""}"
  let (s, r) := run fresh "start = if T then x else y fi"
  if !r.ok then
    ok := false
    IO.eprintln s!"if: ‘start = if T then x else y fi’: {r.error}"
  match r.state.lines with
  | [l] =>
      if l.expr == "if ⊤ then x else y fi" && l.kind == "cond"
          && l.parts == ["⊤", "x", "y"] && l.zooms.length == 3 then
        IO.println "if: it reads back as it was written, in three clickable pieces"
      else
        ok := false
        IO.eprintln s!"if: the line is ‘{l.expr}’, kind ‘{l.kind}’, with \
          {l.parts.length} parts and {l.zooms.length} zoom targets"
  | ls =>
      ok := false
      IO.eprintln s!"if: the started proof draws {ls.length} lines, not one"
  let (_, based) := run s "apply case base : = x"
  if !based.ok then
    ok := false
    IO.eprintln s!"if: ‘apply case base : = x’: {based.error}"
  else if based.state.proved then
    IO.println "if: and a law of the list rewrites it away"
  else
    ok := false
    IO.eprintln s!"if: after ‘case base’ the proof is not finished: {based.state.outcome}"
  -- Zooming in to a branch gains the condition, which is what makes a proof
  -- inside one possible.
  let mut u := fresh
  for arg in ["start ⇐ if b then b else T fi", "zoom 1"] do
    let (u', r') := run u arg
    u := u'
    if !r'.ok then
      ok := false
      IO.eprintln s!"if: ‘{arg}’: {r'.error}"
  if (Api.stateView u).context == ["b"] then
    IO.println "if: zooming in to a branch gains the condition"
  else
    ok := false
    IO.eprintln s!"if: inside the branch the context is \
      {String.intercalate ", " (Api.stateView u).context}"
  for arg in ["apply context : = ⊤", "out", "apply case idempotent : = ⊤"] do
    let (u', r') := run u arg
    u := u'
    if !r'.ok then
      ok := false
      IO.eprintln s!"if: ‘{arg}’: {r'.error}"
  if (Api.stateView u).proved then
    IO.println "if: and the proof inside it finishes"
  else
    ok := false
    IO.eprintln s!"if: the proof inside the branch did not finish: {(Api.stateView u).outcome}"
  return ok

/-- Check the document's quantified expressions through the request service the
window talks to.

The grammar puts a quantifier at the weakest level, so its body runs to the end of
the expression: that is what the parse checks are about, and it is why they live
here rather than in Lean, the parser being a `partial def` the kernel cannot
reduce. Then: that the form travels as text, that the window is offered its domain
and its body as two places to click, that a shipped law rewrites one with the
line's own binder name in the answer, and that zooming in to a body gains `v: d`
— which is what makes a proof inside a body possible. -/
def quantTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean ++ Laws.quantifier } }
  let run := fun (s : Session) (arg : String) => Api.respond s { op := "cmd", arg := arg }
  -- Read and written as one, and the body runs to the end: `∀i: nat· i ≥ 0 ∧ p` is
  -- one quantification of a conjunction, and the conjunction of a quantification
  -- with `p` has to bracket it.
  let body := Expr.bin .and (Expr.bin .ge (Expr.var "i") (Expr.num 0)) (Expr.var "p")
  let whole := Expr.quant .all ["i"] (Expr.var "nat") body
  match Parser.expr "∀i: nat· i ≥ 0 ∧ p", Parser.expr "(∀i: nat· i ≥ 0) ∧ p" with
  | .ok greedy, .ok bracketed =>
      if greedy == whole && greedy.render == "∀i: nat· i ≥ 0 ∧ p"
          && bracketed == Expr.bin .and (Expr.quant .all ["i"] (Expr.var "nat")
              (Expr.bin .ge (Expr.var "i") (Expr.num 0))) (Expr.var "p")
          && bracketed.render == "(∀i: nat· i ≥ 0) ∧ p" then
        IO.println "quant: it parses, renders as it was written, and its body runs to the end"
      else
        ok := false
        IO.eprintln s!"quant: parsed ‘{greedy.render}’ and ‘{bracketed.render}’"
  | a, b =>
      ok := false
      IO.eprintln s!"quant: it does not parse: \
        {match a with | .error e => e | .ok _ => ""}\
        {match b with | .error e => e | .ok _ => ""}"
  -- The law line's own `∀a, b·` binder and an expression quantifier both begin a
  -- law file line with `∀`, and the `:` before the `·` is what tells them apart.
  -- Both readings, on one line each, so the two cannot start reading each other.
  match Parser.lawLine "specialization: ∀a, b· a ∧ b ⇒ a",
        Parser.lawLine "a made-up law: ∀x: nat· x ≥ 0" with
  | .ok (some binder), .ok (some quantified) =>
      if binder.vars == ["a", "b"] && binder.stmt.vars == []
          && quantified.vars == ["nat"] && quantified.stmt.vars == []
          && quantified.stmt == Expr.quant .all ["x"] (Expr.mvar "nat")
              (Expr.bin .ge (Expr.var "x") (Expr.num 0)) then
        IO.println "quant: a law line's own binder and an expression quantifier \
          still read as themselves"
      else
        ok := false
        IO.eprintln s!"quant: the law line binder read {binder.vars} and the \
          quantified law read {quantified.vars} over ‘{quantified.stmt.render}’"
  | a, b =>
      ok := false
      IO.eprintln s!"quant: a law file line was not read: \
        {match a with | .error e => e | _ => ""}{match b with | .error e => e | _ => ""}"
  -- The two things the document rules out, refused rather than read.
  match Parser.expr "∀i· i ≥ 0", Parser.expr "∀i: i· i ≥ 0" with
  | .error _, .error _ =>
      IO.println "quant: no domain is not a second form, and a domain may not \
        mention what is bound"
  | a, b =>
      ok := false
      IO.eprintln s!"quant: read \
        {match a with | .ok e => s!"‘{e.render}’ " | .error _ => ""}\
        {match b with | .ok e => s!"‘{e.render}’" | .error _ => ""}"
  let (_, r) := run fresh "start = ∀i: nat· i ≥ 0"
  if !r.ok then
    ok := false
    IO.eprintln s!"quant: ‘start = ∀i: nat· i ≥ 0’: {r.error}"
  match r.state.lines with
  | [l] =>
      if l.expr == "∀i: nat· i ≥ 0" && l.kind == "quant" && l.op == "∀i"
          && l.parts == ["nat", "i ≥ 0"] && l.zooms.length == 2 then
        IO.println "quant: it reads back as it was written, in a domain and a body"
      else
        ok := false
        IO.eprintln s!"quant: the line is ‘{l.expr}’, kind ‘{l.kind}’, opening ‘{l.op}’, \
          with {l.parts.length} parts and {l.zooms.length} zoom targets"
  | ls =>
      ok := false
      IO.eprintln s!"quant: the started proof draws {ls.length} lines, not one"
  -- A shipped law, applied to a line whose binder is not the law's.
  let (v, started) := run fresh "start = ¬(∀i: nat· i ≥ 0)"
  if !started.ok then
    ok := false
    IO.eprintln s!"quant: ‘start = ¬(∀i: nat· i ≥ 0)’: {started.error}"
  let (_, dual) := run v "apply generalized duality : = ∃i: nat· ¬(i ≥ 0)"
  if dual.ok && dual.state.proved then
    IO.println "quant: a shipped law rewrites it, in the line's own binder name"
  else
    ok := false
    IO.eprintln s!"quant: ‘generalized duality’ on ‘¬(∀i: nat· i ≥ 0)’: \
      {dual.error}{dual.state.outcome}"
  -- Zooming in to the body gains `i: nat`, and a proof inside it finishes.
  let mut u := fresh
  for arg in ["start = ∀i: nat· ¬¬(i ≥ 0)", "zoom 1"] do
    let (u', r') := run u arg
    u := u'
    if !r'.ok then
      ok := false
      IO.eprintln s!"quant: ‘{arg}’: {r'.error}"
  if (Api.stateView u).context == ["i: nat"] then
    IO.println "quant: zooming in to a body gains the membership the quantifier declares"
  else
    ok := false
    IO.eprintln s!"quant: inside the body the context is \
      {String.intercalate ", " (Api.stateView u).context}"
  for arg in ["apply double negation : = i ≥ 0", "out"] do
    let (u', r') := run u arg
    u := u'
    if !r'.ok then
      ok := false
      IO.eprintln s!"quant: ‘{arg}’: {r'.error}"
  if (Api.stateView u).proved then
    IO.println "quant: and the proof inside it finishes"
  else
    ok := false
    IO.eprintln s!"quant: the proof inside the body did not finish: {(Api.stateView u).outcome}"
  return ok

/-- Check that a gap is carried out of the subproof that holds it, through the
request service the window talks to.

A zoom out justifies the outer step by the subproof, so a subproof that still
has a gap in it leaves the outer step unjustified; the document draws the
warning sign on the line just before a gap, and after the splice that line is
the one the zoom was made from. The same session with the subproof's step taken
from a law instead of typed in must be unchanged from before: no gap outside,
and the one-step subproof folded into its parent line with the law's name lifted
onto it.

Driven through `cmd` requests rather than a demonstration script, because a
proof that keeps a gap never proves anything and `--demo=` runs only proofs that
do. -/
def gapTest : IO Bool := do
  let mut ok := true
  let fresh : Session := { doc := { laws := Laws.boolean } }
  let after := fun (last : String) => Id.run do
    let mut s := fresh
    let mut err := ""
    for arg in ["start = x ∧ (y ∨ y)", "zoom 1", last, "out"] do
      let (s', r) := Api.respond s { op := "cmd", arg := arg }
      s := s'
      if !r.ok && err.isEmpty then err := s!"‘{arg}’: {r.error}"
    return (err, Api.stateView s)
  let (err, gappy) := after "direct = y"
  if !err.isEmpty then
    ok := false
    IO.eprintln s!"gap: {err}"
  else
    let notes := gappy.lines.map fun l => (l.index, l.gap, l.note)
    if notes == [(0, true, "!"), (1, true, "!"), (2, false, ""), (3, false, "")] then
      IO.println "gap: a gappy subproof leaves a warning on the line before the splice"
    else
      ok := false
      IO.eprintln s!"gap: after the splice the lines are {repr notes}"
    if !gappy.proved then
      IO.println "gap: and the proof still claims nothing"
    else
      ok := false
      IO.eprintln "gap: a proof with a gap carried out of a subproof claims something"
  let (err', clean) := after "apply idempotent : = y"
  if !err'.isEmpty then
    ok := false
    IO.eprintln s!"gap: {err'}"
  else
    let notes := clean.lines.map fun l => (l.index, l.gap, l.note)
    if notes == [(0, false, "idempotent"), (3, false, "")] && clean.proved then
      IO.println "gap: a justified subproof splices with no gap, and still folds"
    else
      ok := false
      IO.eprintln s!"gap: a justified subproof draws {repr notes}, \
        proved = {clean.proved}"
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
suggestion the law list offers is a sound step, that the suggestions come in the
order `Doc.rank` describes, that the focus can land on an outer line through the
request service, that a click can zoom in to every part of a line through it — the
runs of operands as well as the single ones — that a gap left inside a subproof
is carried out to the line the zoom was made from, that every suggestion says
which part of the line it would rewrite, and that the display collapses reach it
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
  if ← System.FilePath.pathExists numberLawFilePath then
    match Parser.lawFile (← IO.FS.readFile numberLawFilePath) with
    | .ok ls =>
        if ls == Laws.number then
          IO.println s!"laws: {numberLawFilePath} is the list compiled in, and \
            {Laws.number.length} number laws hold on small integers"
        else
          ok := false
          IO.eprintln s!"laws: {numberLawFilePath} and the list compiled in differ; \
            rebuild Netty.Laws"
    | .error e =>
        ok := false
        IO.eprintln s!"laws: {numberLawFilePath}: {e}"
  if ← System.FilePath.pathExists quantifierLawFilePath then
    match Parser.lawFile (← IO.FS.readFile quantifierLawFilePath) with
    | .ok ls =>
        if ls == Laws.quantifier then
          IO.println s!"laws: {quantifierLawFilePath} is the list compiled in, \
            {Laws.quantifier.length} quantifier laws, trusted as transcribed"
        else
          ok := false
          IO.eprintln s!"laws: {quantifierLawFilePath} and the list compiled in differ; \
            rebuild Netty.Laws"
    | .error e =>
        ok := false
        IO.eprintln s!"laws: {quantifierLawFilePath}: {e}"
  -- A law whose statement writes a `:` has to round-trip through the law file
  -- notation too, and a law's name is whatever precedes the first `:`.
  match Parser.lawFile (renderLawFile Laws.quantifier) with
  | .ok ls =>
      if ls == Laws.quantifier then
        IO.println "laws: the quantifier list is written out and read back unchanged"
      else
        ok := false
        IO.eprintln "laws: writing the quantifier list out and reading it back changed it"
  | .error e =>
      ok := false
      IO.eprintln s!"laws: the written-out quantifier list does not parse: {e}"
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
  if !(← rankTest) then ok := false
  if !(← focusTest) then ok := false
  if !(← zoomTest) then ok := false
  if !(← collapseTest) then ok := false
  if !(← gapTest) then ok := false
  if !(← conditionalTest) then ok := false
  if !(← dialogTest) then ok := false
  if !(← ifTest) then ok := false
  if !(← quantTest) then ok := false
  if !(← siteTest) then ok := false
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
