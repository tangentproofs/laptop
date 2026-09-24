import Netty.Render

/-!
# Scripts: driving a proof session from text

A headless Netty needs a way to say what a user would do with a mouse. A
script is one command per line; `#` begins a comment. The commands are the
document's own transitions plus a few that only print or touch files.

```
start [boolean|number] DIRECTION EXPRESSION   begin the proof
apply NAME                                   take the suggestion from a law
apply NAME : CONNECTIVE EXPRESSION           …when the law offers several
apply #N                                     take the N-th suggestion
direct CONNECTIVE EXPRESSION                 type the next line in (leaves a gap)
zoom N                                       zoom in to the N-th main operand
out                                          zoom out
focus N                                      move the focus to just after line N
undo                                         undo one command
proof                                        print the proof pane
suggest                                      print the suggestions pane
context                                      print the context pane
check [EXPRESSION]                           print what the proof proves, and
                                             fail unless it is EXPRESSION
laws FILE                                    add a law file
load FILE / save FILE                        read or write a proof file
```

`undo` is why a session is more than a document: `Session` keeps the documents
the commands have passed through, and undoing pops one off.
-/

namespace Netty

/-- A line of a script: a document command, or one of the things a command
line can do that a document cannot. -/
inductive ScriptCmd
  /-- A transition on the document. -/        | doc (c : Cmd)
  /-- Undo one command. -/                    | undo
  /-- Print the proof pane. -/                | proof
  /-- Print the suggestions pane. -/          | suggest
  /-- Print the context pane. -/              | context
  /-- Print what the proof proves, and fail
  unless it is the given formula. -/          | check (expected : Option Expr)
  /-- Add the laws in a file. -/              | laws (path : String)
  /-- Read a proof file. -/                   | load (path : String)
  /-- Write a proof file. -/                  | save (path : String)
  deriving Repr, DecidableEq, Inhabited

/-- A proof session: the document and enough history to undo. -/
structure Session where
  /-- The document as it stands. -/
  doc : Doc
  /-- Earlier states, most recent first. -/
  history : List Doc := []
  deriving Repr, DecidableEq, Inhabited

namespace Session

/-- Run a document command, remembering the state it came from. -/
def step (s : Session) (c : Cmd) : Except String Session := do
  let d ← s.doc.step c
  return { doc := d, history := s.doc :: s.history }

/-- Undo one command. -/
def undo (s : Session) : Except String Session :=
  match s.history with
  | d :: rest => .ok { doc := d, history := rest }
  | [] => .error "there is nothing to undo"

end Session

namespace Parser

/-- Split off the first whitespace-delimited word. -/
private def firstWord (s : String) : String × String :=
  let cs := (trim s).toList
  (String.ofList (cs.takeWhile fun c => !c.isWhitespace),
   trim (String.ofList (cs.dropWhile fun c => !c.isWhitespace)))

/-- Read a margin connective from the front of a token list. -/
private def connective : List Tok → Except String (BinOp × List Tok)
  | .op o :: rest
  | .bigOp o :: rest =>
      if o.isMargin then .ok (o, rest)
      else .error s!"‘{o.symbol}’ cannot stand in the left margin of a proof"
  | t :: _ => .error s!"expected a connective but found ‘{t}’"
  | [] => .error "expected a connective"

/-- Read an optional type, then a direction, from the front of a token list. -/
private def direction : List Tok → Except String (Ty × Dir × List Tok)
  | .ident "boolean" :: rest => do
      let (o, rest) ← connective rest
      let r ← orElseError s!"‘{o.symbol}’ is not a direction" o.rel?
      return (.boolean, r.dir, rest)
  | .ident "number" :: rest => do
      let (o, rest) ← connective rest
      let r ← orElseError s!"‘{o.symbol}’ is not a direction" o.rel?
      return (.number, r.dir, rest)
  | ts => do
      let (o, rest) ← connective ts
      let r ← orElseError s!"‘{o.symbol}’ is not a direction" o.rel?
      -- `=` belongs to every type, so a proof that starts with it is boolean
      -- unless the type was given.
      return (o.connTy.getD .boolean, r.dir, rest)

/-- Parse one line of a script; comments and blank lines yield nothing. -/
def scriptLine (line : String) : Except String (Option ScriptCmd) := do
  let t := trim line
  if t.isEmpty || beginsWith t '#' then return none
  let (word, rest) := firstWord t
  match word with
  | "start" => do
      let (ty, dir, ts) ← direction (← tokenize rest)
      return some (.doc (.start ty dir (← exprOfToks ts)))
  | "apply" => do
      if beginsWith rest '#' then
        let n ← orElseError s!"‘{rest}’ is not a suggestion number"
          (String.ofList (rest.toList.drop 1)).toNat?
        return some (.doc (.apply n))
      match rest.splitOn ":" with
      | [name] =>
          if (trim name).isEmpty then throw "apply what?"
          return some (.doc (.applyNamed (trim name) none))
      | name :: expected =>
          let (o, ts) ← connective (← tokenize (String.intercalate ":" expected))
          return some (.doc (.applyNamed (trim name) (some (o, ← exprOfToks ts))))
      | [] => throw "apply what?"
  | "direct" => do
      let (o, ts) ← connective (← tokenize rest)
      return some (.doc (.direct o (← exprOfToks ts)))
  | "zoom" => do
      let n ← orElseError s!"‘{rest}’ is not an operand number" rest.toNat?
      return some (.doc (.zoomIn n))
  | "out" => return some (.doc .zoomOut)
  | "focus" => do
      let n ← orElseError s!"‘{rest}’ is not a line number" rest.toNat?
      return some (.doc (.setFocus n))
  | "undo" => return some .undo
  | "proof" => return some .proof
  | "suggest" => return some .suggest
  | "context" => return some .context
  | "check" =>
      if rest.isEmpty then return some (.check none)
      else return some (.check (some (← expr rest)))
  | "laws" => return some (.laws rest)
  | "load" => return some (.load rest)
  | "save" => return some (.save rest)
  | w => throw s!"‘{w}’ is not a command"

/-- Parse a whole script, keeping the line numbers for error messages. -/
def script (text : String) : Except String (List (Nat × ScriptCmd)) :=
  go 1 (text.splitOn "\n") []
where
  go : Nat → List String → List (Nat × ScriptCmd) → Except String (List (Nat × ScriptCmd))
    | _, [], acc => .ok acc.reverse
    | n, line :: rest, acc =>
        match scriptLine line with
        | .error e => .error s!"line {n}: {e}"
        | .ok none => go (n + 1) rest acc
        | .ok (some c) => go (n + 1) rest ((n, c) :: acc)

end Parser

namespace Demo

/-- The short proof from the first page of the Netty document, the one whose
proof pane reads

```
⇐  a ⇒ (b⇒a)  portation
=  a∧b ⇒ a    specialization
=  T
```

and which therefore proves `a ⇒ (b ⇒ a)`. -/
def portation : String :=
"# The example proof from page 0 of the Netty document.
start ⇐ a ⇒ (b ⇒ a)
suggest
apply portation
apply specialization : = ⊤
proof
check a ⇒ (b ⇒ a)
"

/-- A proof that uses the rest of the kernel: zooming in to a subexpression,
the context that zooming in supplies, and zooming back out. -/
def discharge : String :=
"# (a ⇒ b) ⇒ (a ⇒ a ∧ b), proved by zooming in to the consequent, where the
# antecedent a ⇒ b is available as context.
start ⇐ (a ⇒ b) ⇒ (a ⇒ a ∧ b)
zoom 1
context
apply discharge : = a ⇒ b
apply context : = ⊤
out
proof
apply base : = ⊤
check (a ⇒ b) ⇒ (a ⇒ a ∧ b)
"

/-- A proof pane with a gap in it, and the gap then filled: direct entry
leaves a warning sign, and moving the focus back and taking the suggestion
that writes the line already there replaces the sign with the law's name. -/
def gap : String :=
"# Direct entry leaves a gap, which taking the right suggestion then closes.
start ⇐ ¬¬a
direct = a
proof
focus 0
apply double negation : = a
proof
check ¬¬a ≡ a
"

/-- A law applied to a *part* of a line: idempotence matches the second main
operand of `x ∧ (y ∨ y)` and folds it in place, which before a law could be
applied to a part took a zoom in, an application and a zoom out. -/
def minimize : String :=
"# A law applied to a part of a line, as a result of minimization: idempotence
# matches y ∨ y, the second main operand, and folds it where it stands.
start = x ∧ (y ∨ y)
suggest
apply idempotent : = x ∧ y
proof
check x ∧ (y ∨ y) ≡ x ∧ y
"

/-- A law applied to a contiguous *segment* of an association: idempotence
matches the middle two operands of `x ∧ y ∧ y ∧ z` and folds them where they
stand. Neither the whole line nor any single main operand matches — the operands
are the bare identifiers `x`, `y`, `y`, `z` — so before a segment was a site this
step did not exist at all. -/
def segment : String :=
"# A law applied to a contiguous segment of an association: idempotence matches
# y ∧ y, the middle two of four conjuncts, and folds them where they stand,
# leaving x and z alone. The whole line does not match, and neither does any
# single main operand.
start = x ∧ y ∧ y ∧ z
suggest
apply idempotent : = x ∧ y ∧ z
proof
check x ∧ y ∧ y ∧ z ≡ x ∧ y ∧ z
"

/-- The first of the display collapses: a subproof that is a single law
application is *drawn* as its parent line with the law's name moved up onto
it. The proof pane is printed twice, once while the subproof is still open and
once after the zoom out has closed it, so the fold can be seen happening — and
what is left is line for line what `minimize` draws, which is the same step
taken the short way round. -/
def fold : String :=
"# A one-step subproof, folded into its parent line by the display. The first
# ‘proof’ shows the subproof open; the second shows it folded away, with
# ‘idempotent’ moved up to line 0 — which is what the ‘minimize’ demonstration,
# taking the same step in one application, draws.
start = x ∧ (y ∨ y)
zoom 1
apply idempotent : = y
proof
out
proof
check x ∧ (y ∨ y) ≡ x ∧ y
"

/-- The other display collapse: two zoom-ins matched by two zoom-outs are
*drawn* as one zoom step. The middle level holds nothing of its own — its only
two lines are the one the zoom in wrote and the one the zoom out wrote — so the
subproof it holds is drawn a level further out. Again the pane is printed
twice, before the outer zoom out and after it. -/
def merge : String :=
"# Two zoom-ins matched by two zoom-outs, merged by the display into one zoom
# step. The middle level — the line ‘y ∨ ¬¬z ∧ ¬¬z’ and the line the first zoom
# out writes — does nothing but hold the subproof, so after the second zoom out
# the display draws that subproof one level out and leaves the middle level's
# two lines undrawn. The inner subproof is two steps long, so it is not folded
# away as well.
start = x ∧ (y ∨ (¬¬z ∧ ¬¬z))
zoom 1
zoom 1
apply idempotent : = ¬¬z
apply double negation : = z
out
proof
out
proof
check x ∧ (y ∨ (¬¬z ∧ ¬¬z)) ≡ x ∧ (y ∨ z)
"

/-- The demonstrations, by name. -/
def all : List (String × String) :=
  [("portation", portation), ("discharge", discharge), ("gap", gap),
   ("minimize", minimize), ("segment", segment), ("fold", fold), ("merge", merge)]

end Demo
end Netty
