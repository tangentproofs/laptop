import Netty.Laws
import Netty.Doc
import Netty.Arith

/-!
# Proofs written as the book writes them

A *calculation file* holds calculations laid out as aPToP lays them out: one formula
per line, the connective that relates it to the line above in the left margin,
and, at the end of a line, the hint that justifies the step to the *next* line.

```
laws boolean

theorem portation demo: a ⇒ (b ⇒ a)
    a ⇒ (b ⇒ a)        portation
=   a ∧ b ⇒ a          specialization
=   ⊤
```

That is the proof pane of `Doc.renderProof` read the other way round: the pane
is what a session *writes*, and a calculation file is what a person writes and the
kernel *reads back*, checking each step.

## The format

* `#` begins a comment line; blank lines are ignored.
* `laws NAME …` puts shipped law lists in force: `boolean`, `number`,
  `quantifier`. It may appear more than once, and applies to the theorems that
  follow it.
* `law NAME: STATEMENT` adds one law, in law-file notation (`Parser.lawLine`), to
  the laws in force for the theorems that follow — a definition the proofs below
  it may cite by name.
* `theorem NAME: CLAIM` begins a proof of `CLAIM`. The name may contain spaces.
* Every other line is a line of the proof: an optional margin connective (none
  on the first line), the formula, and an optional hint separated from the
  formula by at least two spaces. A hint is the name of the law that takes this
  line to the next; several names separated by `,` are applied one after the
  other.

## What is checked

A step `A`, hint `L`, then `op B` is checked by asking the kernel whether one
application of `L` can take `A` to `B` with `op` in the margin. The law may be
applied anywhere in `A` — at the whole line, at a part (`Doc.sites`), or at any
depth below, which is reached by zooming in (`Cmd.zoomIn`) along the way, applying
the law, and zooming back out (`Doc.zoomOut`). So the step a calculation file asserts is
a step the document model would have taken, and it inherits that model's
direction discipline and context: a law applied under a negation goes the other
way, and a law applied inside `a ∧ ·` may use `a` (the hint `context`).

A law the match leaves variables unconstrained in — transitivity, say — is
completed from the next line: each unconstrained variable is bound by matching
what the law would write against the parts of `B`.

`B` is compared with what the kernel writes modulo the association of
associative operators, since a calculation is written with as few brackets as the
grammar allows.

A step may claim less than the kernel derives — `⇒` where the law gives `=` —
but never more.

Two hints are decisions rather than laws (`Netty.Arith`): `arithmetic` (equal
polynomials, comparisons with the same normal form, a comparison of numerals)
and `binary algebra` (equal truth tables). The kernel finds where the lines
differ and checks each place.

A hint that names no law in force and no decision is not checked here. The step is reported as
*left to Lean*: the translation (`Netty.ToLean`) proves every step, law or not, so
such a step is still checked, only not by this kernel. This is what lets a proof
file carry the book's own hints — "arithmetic", "Substitution Law" — before the
kernel has a law that does what the hint says.

Finally, what the whole calculation proves (`Doc.outcome`'s rule: a proof that
ends in `⊤` under `=` or `⇐` proves its first line) must be the theorem's claim.
-/

namespace Netty

/-- What is in force where a theorem is stated: the laws, and the state and named
specifications the programming rules work with. -/
structure Ctx where
  /-- The laws in force. -/
  laws : List Law := []
  /-- The state and the named specifications. -/
  prog : Prog := {}
  /-- The named specifications a parent file declared (`extends`), which an
  implementation must refine. -/
  inherited : List String := []
  deriving Repr, Inhabited

/-- One line of a written proof. -/
structure PLine where
  /-- The connective in the margin; `none` on the first line. -/
  conn : Option BinOp
  /-- The formula. -/
  expr : Expr
  /-- The hint at the end of the line, justifying the step to the next one; `""`
  when there is none. -/
  hint : String
  /-- The line's number in the file. -/
  lineNo : Nat
  deriving Repr, Inhabited

/-- A theorem of a calculation file and its calculation. -/
structure PTheorem where
  /-- Its name. -/
  name : String
  /-- What it claims. -/
  claim : Expr
  /-- The lines of the calculation. -/
  lines : List PLine
  /-- What is in force for it. -/
  cx : Ctx
  /-- For a refinement `S ⇐ P`, the specification `S` it refines. -/
  refines : Option String := none
  /-- The line of the file the theorem starts on. -/
  lineNo : Nat
  deriving Repr, Inhabited

/-- How one application of a law or rule was made, recorded so that the
translation can prove the step from the law's Lean twin: the line it started
from and the line it wrote, the connective at the root, the zooms that reached
the place it was applied (outermost first), the suggestion taken there — which
carries the place, the reading of the law and the substitution — and the
variables supplied by hand. -/
structure Cert where
  /-- The line the application starts from. -/
  src : Expr
  /-- The line it writes. -/
  dst : Expr
  /-- The connective it puts in the margin. -/
  op : BinOp
  /-- The zooms to the level the law was applied at, outermost first. -/
  path : List Part
  /-- The suggestion taken there. -/
  sugg : Suggestion
  /-- The unconstrained variables, supplied. -/
  bind : Subst
  /-- The line with the hole where the step rewrote, when the step was not made
  by zooming (`arithmetic`, `binary algebra`); otherwise it is computed from the
  path and the place. -/
  ctx : Option Expr := none
  deriving Repr, DecidableEq, Inhabited

/-- How a step was justified. -/
inductive StepCheck
  /-- The kernel applied the named laws and wrote the next line, as `certs` say. -/
  | law (names : List String) (certs : List Cert)
  /-- The kernel applied the named laws and wrote the next line, but a
  conditional law left premises the laws in force do not settle; those are left
  to Lean, which proves the step outright. -/
  | lawIf (names : List String) (premises : List Expr) (certs : List Cert)
  /-- The hint names no law in force; the step is left to Lean. -/
  | lean (hint : String)
  deriving Repr, Inhabited, DecidableEq

/-- A checked theorem: the theorem, its type, the relation its calculation
proves, and how each step was justified. -/
structure Checked where
  /-- The theorem. -/
  thm : PTheorem
  /-- The type of its lines. -/
  ty : Ty
  /-- What the connectives add up to. -/
  rel : BinOp
  /-- One entry per step. -/
  steps : List StepCheck
  deriving Repr, Inhabited

namespace Expr

/-- Every association of an associative operator rebuilt to the left, at every
depth, so that two formulas differing only in how an association is bracketed are
equal. -/
partial def normAssoc : Expr → Expr
  | bin o l r =>
      if o.assoc then
        let es := (flattenOp o (bin o l r)).map normAssoc
        (rebuildOp o es).getD (bin o l r)
      else bin o (normAssoc l) (normAssoc r)
  | neg a => neg (normAssoc a)
  | cond c x y => cond (normAssoc c) (normAssoc x) (normAssoc y)
  | quant k ids d b => quant k ids (normAssoc d) (normAssoc b)
  | e => e

/-- Every subexpression, the expression itself first. -/
partial def subterms (e : Expr) : List Expr :=
  e :: (match e with
    | bin o l r =>
        if o.assoc then
          -- The contiguous runs of an association are parts as well.
          let es := flattenOp o e
          let runs := (List.range es.length).flatMap fun i =>
            (List.range (es.length + 1)).filterMap fun j =>
              if j ≥ i + 2 && j - i < es.length then rebuildOp o ((es.drop i).take (j - i))
              else none
          runs ++ es.flatMap subterms
        else subterms l ++ subterms r
    | neg a => subterms a
    | cond c x y => subterms c ++ subterms x ++ subterms y
    | quant _ _ d b => subterms d ++ subterms b
    | _ => [])

end Expr

namespace Proof

/-- Where one application of a law can take a line: the connective the step puts
in the outer margin, the line it writes, and the premise it leaves when it is a
conditional law whose premise the laws in force did not settle. -/
structure Reach where
  /-- The connective. -/
  op : BinOp
  /-- The line written. -/
  expr : Expr
  /-- What is left to prove, if anything. -/
  premise : Option Expr := none
  /-- How the kernel took the step (`Cert`), for the translation to Lean. -/
  cert : Option Cert := none
  deriving Repr, DecidableEq, Inhabited

/-- Zoom out `k` times. -/
def zoomOutN : Nat → Doc → Except String Doc
  | 0, d => .ok d
  | k + 1, d => do zoomOutN k (← d.zoomOut)

/-- The step a root level of two lines records: its connective and its second
line, with the premise the first line's gap is for. -/
def rootStep (d : Doc) : Option Reach := do
  let a ← d.lines[0]?
  let j ← d.nextSibling 0
  let b ← d.lines[j]?
  let op ← b.conn
  if a.gap && a.premise.isNone then none
  return { op := op, expr := b.expr, premise := a.premise }

/-- Bindings for the unconstrained variables of a suggestion, found by matching
what it would write against the parts of the line it should lead to. -/
def holeBinds (s : Suggestion) (target : Expr) : List Subst :=
  if s.holes.isEmpty then [[]] else
  let found := (target.subterms.flatMap fun t => Expr.matchAll s.result t []).filter
    fun σ => s.holes.all fun h => (σ.lookup h).isSome
  found.map fun σ => s.holes.filterMap fun h => (σ.lookup h).map (h, ·)

/-- Every line one application of the law named `name` can write after the
focus line of `d`, which is `k` zooms deep, at any depth up to `fuel` more
zooms. `target` is the line the step should reach, used only to fill in
variables the match leaves unconstrained. -/
def reachFrom (name : String) (target src : Expr) :
    List Part → Nat → Nat → Doc → List Reach
  | path, k, fuel, d =>
      let here := (d.suggestions.filter (·.law.toLower == name.toLower)).flatMap fun s =>
        (holeBinds s target).filterMap fun b =>
          match d.applySuggestion s b with
          | .ok d' => match zoomOutN k d' with
            | .ok d'' => (rootStep d'').map fun r =>
                { r with cert := some { src := src, dst := r.expr, op := r.op,
                                        path := path.reverse, sugg := s, bind := b } }
            | .error _ => none
          | .error _ => none
      let deeper := match fuel with
        | 0 => []
        | f + 1 =>
            match d.focusLine? with
            | some fl =>
                ((Doc.parts fl.expr).filter Part.zoomable).flatMap fun p =>
                  match d.step (.zoomIn p) with
                  | .ok d' => reachFrom name target src (p :: path) (k + 1) f d'
                  | .error _ => []
            | none => []
      here ++ deeper

/-- How deep a step may reach into a line. -/
def maxDepth : Nat := 12

/-- The lines one application of law `name` takes `a` to, from a level of type
`ty` and direction `dir`. -/
def reach (cx : Ctx) (ty : Ty) (dir : Dir) (name : String) (target a : Expr) :
    List Reach :=
  let named := cx.laws.filter (·.name.toLower == name.toLower)
  match ({ laws := named, prog := cx.prog } : Doc).step (.start ty dir a) with
  | .ok d => reachFrom name target a [] 0 maxDepth d
  | .error _ => []

/-- Whether a step the kernel derived with connective `got` licenses the
connective `want` a proof wrote: equal, or `=` for any connective of the same
direction family, or a strict connective for its weak form. -/
def licenses (got want : BinOp) : Bool :=
  got == want ||
    match got.rel?, want.rel? with
    | some g, some w =>
        (g.dir == .same && (w.dir == .same || !w.strict) && want != .ne) ||
          (g.dir == w.dir && g.strict && !w.strict)
    | _, _ => false

/-- One line a sequence of law applications reaches: the relation the steps add
up to, the line, and the premises conditional laws left on the way. -/
abbrev End := Rel × Expr × List Expr × List Cert

/-- Every line a sequence of law applications takes `a` to. -/
def chain (cx : Ctx) (ty : Ty) (dir : Dir) (target : Expr) :
    List String → List End → List End
  | [], acc => acc
  | n :: ns, acc =>
      let next := acc.flatMap fun (r, e, qs, cs) =>
        (reach cx ty dir n target e).filterMap fun x => do
          let r' ← x.op.rel?
          let rc ← Rel.combine [r, r']
          some (rc, x.expr, qs ++ x.premise.toList, cs ++ x.cert.toList)
      -- Keep one of each line, so a long hint does not multiply its work; a
      -- reading that leaves no premise is kept over one that leaves some.
      let sorted := next.filter (·.2.2.1.isEmpty) ++ next.filter (!·.2.2.1.isEmpty)
      let dedup := sorted.foldl (fun acc' p =>
        if acc'.any (fun q => q.2.1 == p.2.1 && q.1 == p.1) then acc' else acc' ++ [p]) []
      chain cx ty dir target ns dedup

/-- Check one step: the laws named by `names` take `a` to `b` with `op`. The
result is the premises conditional laws left, which are empty for a step that
needs nothing, and how each application was made. -/
def checkStep (cx : Ctx) (ty : Ty) (names : List String) (a : Expr) (op : BinOp)
    (b : Expr) : Except String (List Expr × List Cert) := do
  let r ← orElseError s!"‘{op.symbol}’ cannot stand in the margin" op.rel?
  -- The level's direction is the step's own, so `=` steps and steps in the
  -- step's direction are the ones offered.
  let ends := chain cx ty r.dir b names [(⟨.same, false⟩, a, [], [])]
  let nb := b.normAssoc
  let hits := ends.filter fun (rel, e, _) => e.normAssoc == nb && licenses (rel.op ty) op
  match hits.find? (·.2.2.1.isEmpty), hits.head? with
  | some (_, _, _, cs), _ => return ([], cs)
  | none, some (_, _, qs, cs) => return (qs, cs)
  | none, none => pure ()
  let law := String.intercalate ", " names
  -- Say what the law does do: in the other directions, if it reaches `b` there.
  let others := [Dir.down, Dir.up].flatMap fun d =>
    if d == r.dir then [] else chain cx ty d b names [(⟨.same, false⟩, a, [], [])]
  match (ends ++ others).find? (fun (_, e, _) => e.normAssoc == nb) with
  | some (rel, _, _) =>
      throw s!"{law} gives {(rel.op ty).symbol} here, not {op.symbol}"
  | none =>
      if ends.isEmpty then
        throw s!"{law} does not apply to {a.render}"
      else
        let shown := (ends.take 6).map fun (rel, e, _) => s!"  {(rel.op ty).symbol} {e.render}"
        throw s!"{law} does not write {b.render}; it writes\n\
          {String.intercalate "\n" shown}{if ends.length > 6 then "\n  …" else ""}"

/-- What the calculation `lines` proves, by `Doc.outcome`'s rule. -/
def proves (ty : Ty) (lines : List PLine) : Except String (BinOp × Expr) := do
  let top ← orElseError "the proof has no lines" lines.head?
  let bottom ← orElseError "the proof has no lines" lines.getLast?
  let rel ← orElseError "the proof mixes directions"
    (Rel.combine (lines.filterMap fun l => l.conn.bind BinOp.rel?))
  let op := rel.op ty
  let proved :=
    if bottom.expr == .top && (op == .eq || op == .rimp) then top.expr
    else if bottom.expr == .bot && (op == .eq || op == .imp) then .neg top.expr
    else .bin op top.expr bottom.expr
  return (op, proved)

/-- The type of a calculation's lines: what its first line or its connectives
settle, and boolean otherwise. -/
def lineTy (lines : List PLine) : Ty :=
  match lines.findSome? (fun l => l.expr.tyOf?) with
  | some t => t
  | none => (lines.findSome? fun l => l.conn.bind BinOp.connTy).getD .boolean

/-- Whether a hint names laws in force: every comma-separated name does. -/
def hintLaws (cx : Ctx) (hint : String) : Option (List String) :=
  let names := (hint.splitOn ",").map Parser.trim
  let rules := cx.prog.rules.map Prog.ruleName
  -- Resolve each hint word to the kernel's spelling (case-insensitive), so
  -- book hints like "Substitution Law" match `substitution law`.
  let resolve (n : String) : Option String :=
    let nl := n.toLower
    if nl == "context" then some "context"
    else rules.find? (·.toLower == nl)
    <|> (cx.laws.find? (·.name.toLower == nl)).map (·.name)
  let resolved := names.mapM resolve
  match resolved with
  | some rs => if rs.isEmpty then none else some rs
  | none => none

/-- A step by a decision (`arithmetic`, `binary algebra`): the places where the
lines differ, each shown by the decision, as certificates. -/
def decide (r : Rule) (a b : Expr) : Option (List Cert) := do
  let ok : Expr → Expr → Bool := match r with
    | .arith => fun s t => (Arith.arith s t).isSome
    | _ => fun s t => Arith.taut s t
  let ds ← Arith.diffs ok a b
  if ds.isEmpty then none
  return ds.map fun (c, s, t) =>
    let src := c.replaceHole s
    let dst := c.replaceHole t
    { src := src, dst := dst, op := .eq, path := [], bind := [], ctx := some c,
      sugg := { law := Prog.ruleName r, op := .eq, result := dst, holes := [], part := .whole,
                site := s, rule := some r, replacement := t } }

/-- Check a theorem. -/
def check (t : PTheorem) : Except String Checked := do
  let ty := lineTy t.lines
  let rec go : List PLine → Except String (List StepCheck)
    | a :: b :: rest => do
        let op ← orElseError s!"line {b.lineNo}: a line after the first needs a connective"
          b.conn
        let decision := match a.hint with
          | "arithmetic" => some Rule.arith
          | "binary algebra" => some Rule.binAlg
          | _ => none
        let s ← match decision, hintLaws t.cx a.hint with
          | some r, _ =>
              match decide r a.expr b.expr with
              | some cs => pure (StepCheck.law [a.hint] cs)
              | none =>
                  if op != .eq then
                    throw s!"line {a.lineNo}: {a.hint} shows equalities; write = here"
                  else throw s!"line {a.lineNo}: {a.hint} does not show {a.expr.render} = {b.expr.render}"
          | none, names? => match names? with
            | some names =>
              match checkStep t.cx ty names a.expr op b.expr with
              | .ok ([], cs) => pure (StepCheck.law names cs)
              | .ok (qs, cs) => pure (StepCheck.lawIf names qs cs)
              | .error e => throw s!"line {a.lineNo}: {e}"
            | none =>
              if a.hint.isEmpty then throw s!"line {a.lineNo}: the step to the next line has no hint"
              else pure (StepCheck.lean a.hint)
        return s :: (← go (b :: rest))
    | [_] => pure []
    | [] => pure []
  if t.lines.length < 2 then throw s!"theorem {t.name}: a calculation needs two lines or more"
  match t.lines.head? with
  | some l => if l.conn.isSome then
      throw s!"line {l.lineNo}: the first line of a calculation has no connective"
  | none => pure ()
  let steps ← go t.lines
  let (op, proved) ← proves ty t.lines
  let first := (t.lines.head?.map (·.expr)).getD .top
  let last := (t.lines.getLast?.map (·.expr)).getD .top
  -- The claim may be what the calculation proves, or the calculation's own
  -- `first op last`.
  if proved.normAssoc != t.claim.normAssoc &&
      (Expr.bin op first last).normAssoc != t.claim.normAssoc then
    throw s!"theorem {t.name}: the calculation proves {proved.render}, not {t.claim.render}"
  return { thm := t, ty := ty, rel := op, steps := steps }

/-! ### Reading a calculation file -/

/-- The shipped law list of that name. -/
def shipped : String → Option (List Law)
  | "boolean" => some Laws.boolean
  | "number" => some Laws.number
  | "quantifier" => some Laws.quantifier
  | _ => none

/-- Split a proof line into its formula and its hint: the whole line, when it
parses, and otherwise the longest prefix ending at a run of two or more spaces
that parses, the rest being the hint. -/
def splitHint (s : String) : Except String (List Tok × String) := do
  let t := Parser.trim s
  if let .ok ts := Parser.tokenize t then
    if (Parser.exprOfToks (dropConn ts)).toOption.isSome then return (ts, "")
  let cs := t.toList
  -- The places a hint may start: after a run of two or more blanks.
  let cuts := (List.range cs.length).filter fun i =>
    i ≥ 2 && cs[i]? != some ' ' && cs[i - 1]? == some ' ' && cs[i - 2]? == some ' '
  let rec tryCuts : List Nat → Except String (List Tok × String)
    | [] => do
        let ts ← Parser.tokenize t
        let _ ← Parser.exprOfToks (dropConn ts)
        return (ts, "")
    | i :: rest =>
        let left := String.ofList (cs.take i)
        match Parser.tokenize left with
        | .ok ts =>
            if (Parser.exprOfToks (dropConn ts)).toOption.isSome then
              .ok (ts, Parser.trim (String.ofList (cs.drop i)))
            else tryCuts rest
        | .error _ => tryCuts rest
  tryCuts cuts.reverse
where
  dropConn : List Tok → List Tok
    | .op o :: rest | .bigOp o :: rest => if o.isMargin then rest else .op o :: rest
    | ts => ts

/-- Read one proof line. -/
def proofLine (n : Nat) (s : String) : Except String PLine := do
  let (ts, hint) ← splitHint s
  match ts with
  | .op o :: rest | .bigOp o :: rest =>
      if o.isMargin then
        return { conn := some o, expr := ← Parser.exprOfToks rest, hint := hint, lineNo := n }
      else return { conn := none, expr := ← Parser.exprOfToks ts, hint := hint, lineNo := n }
  | _ => return { conn := none, expr := ← Parser.exprOfToks ts, hint := hint, lineNo := n }

/-- Split off the first whitespace-delimited word. -/
private def firstWord (s : String) : String × String :=
  let cs := (Parser.trim s).toList
  (String.ofList (cs.takeWhile fun c => !c.isWhitespace),
   Parser.trim (String.ofList (cs.dropWhile fun c => !c.isWhitespace)))

/-- The identifiers a theorem is stated over, in order, as its Lean translation
binds them: the whole state before and after when any line is written in
programming notation, then the free identifiers of the claim and the lines. -/
def theoremParams (p : Prog) (claim : Expr) (lines : List Expr) : List String :=
  let exprs := claim :: lines
  let plain := exprs.all p.isPlain
  let free := (exprs.flatMap Expr.vars).filter fun n =>
    n != "ok" && !p.specs.any (·.1 == n) && !["int", "nat", "bin", "bool"].contains n
  ((if plain then [] else p.params) ++ free).eraseDups

/-- The name of a theorem's Lean twin: its name, spaces become `_`. -/
def twinName (name : String) : String := name.map fun ch => if ch == ' ' then '_' else ch

/-- A theorem as a law of the rest of its file: a ground law, whose twin is the
theorem's own translation. -/
def theoremLaw (c : PTheorem) : Law :=
  { name := c.name, stmt := c.claim, twin := twinName c.name,
    twinArgs := theoremParams c.cx.prog c.claim (c.lines.map (·.expr)) }

/-- A parsed calculation file: its theorems, what is in force at its end, and
the specifications it names itself. -/
structure PFile where
  /-- The theorems, refinements among them, in order. -/
  theorems : List PTheorem
  /-- What is in force at the end of the file, which a file extending it starts
  from. -/
  cx : Ctx
  /-- The specifications this file names (`spec`). -/
  ownSpecs : List String
  deriving Repr, Inhabited

/-- The files a calculation file extends: its `extends "PATH"` lines. -/
def extendsOf (text : String) : List String :=
  (text.splitOn "\n").filterMap fun raw =>
    let (w, rest) := firstWord raw
    if w == "extends" then some (Parser.trim (rest.replace "\"" "")) else none

/-- Read `state NAMES: DOMAIN`. -/
def stateLine (n : Nat) (rest : String) : Except String (List (String × Expr)) := do
  match rest.splitOn ":" with
  | [names, dom] =>
      let d ← (Parser.expr dom).mapError (s!"line {n}: " ++ ·)
      let ns := ((names.splitOn ",").map Parser.trim).filter (!·.isEmpty)
      if ns.isEmpty then throw s!"line {n}: ‘state’ wants variable names"
      return ns.map (·, d)
  | _ => throw s!"line {n}: write ‘state x, y: int’"

/-- Whether an expression is a program: built from `ok`, assignments, `.`,
`if … then … else … fi` with a plain condition, and named specifications —
what the right side of a refinement may be. -/
def isProgram (p : Prog) : Expr → Bool
  | .var n => n == "ok" || p.specs.any (·.1 == n)
  | .bin .assign (.var _) e => p.isPlain e
  | .bin .seq a b => isProgram p a && isProgram p b
  | .cond c a b => p.isPlain c && isProgram p a && isProgram p b
  | _ => false

/-- Parse a calculation file, starting from what is in force at the start (the
end of the files it extends). -/
def file (init : Ctx) (text : String) : Except String PFile := do
  let mut cx := init
  let mut own : List String := []
  let mut done : List PTheorem := []
  let mut cur : Option PTheorem := none
  let mut n := 0
  for raw in text.splitOn "\n" do
    n := n + 1
    let t := Parser.trim raw
    if t.isEmpty || Parser.beginsWith t '#' then continue
    let (w, rest) := firstWord t
    -- A directive ends the theorem before it, which is then a law of the rest of
    -- the file under its own name.
    let isProofLine := !["laws", "law", "theorem", "state", "spec", "refine",
      "extends"].contains w
    if !isProofLine then
      if let some c := cur then
        done := c :: done
        cx := { cx with laws := cx.laws ++ [theoremLaw c] }
        cur := none
    if w == "extends" then continue
    else if w == "laws" then
      for name in (rest.splitOn " ").filter (!·.isEmpty) do
        match shipped name with
        | some ls => cx := { cx with laws := cx.laws ++ ls }
        | none => throw s!"line {n}: there is no shipped law list called ‘{name}’"
    else if w == "law" then
      match Parser.lawLine rest with
      | .ok (some l) => cx := { cx with laws := cx.laws ++ [l] }
      | .ok none => throw s!"line {n}: an empty law"
      | .error e => throw s!"line {n}: {e}"
    else if w == "state" then
      let vs ← stateLine n rest
      for (v, _) in vs do
        if cx.prog.state.any (·.1 == v) then
          throw s!"line {n}: ‘{v}’ is already a state variable"
      cx := { cx with prog := { cx.prog with state := cx.prog.state ++ vs } }
    else if w == "spec" then
      let (name, body) := firstWord rest
      let body := Parser.trim body
      if name.isEmpty || !Parser.beginsWith body '=' then
        throw s!"line {n}: write ‘spec NAME = SPECIFICATION’"
      if cx.prog.specs.any (·.1 == name) then
        throw s!"line {n}: ‘{name}’ is already a specification"
      let e ← (Parser.expr (String.ofList (body.toList.drop 1))).mapError (s!"line {n}: " ++ ·)
      cx := { cx with prog := { cx.prog with specs := cx.prog.specs ++ [(name, e)] } }
      own := own ++ [name]
    else if w == "theorem" then
      match rest.splitOn ":" with
      | name :: claim@(_ :: _) =>
          let e ← (Parser.expr (String.intercalate ":" claim)).mapError (s!"line {n}: " ++ ·)
          cur := some { name := Parser.trim name, claim := e, lines := [], cx := cx,
                        lineNo := n }
      | _ => throw s!"line {n}: write ‘theorem NAME: CLAIM’"
    else if w == "refine" then
      let e ← (Parser.expr rest).mapError (s!"line {n}: " ++ ·)
      match e with
      | .bin .rimp (.var spec) prog =>
          if !cx.prog.specs.any (·.1 == spec) then
            throw s!"line {n}: ‘{spec}’ is not a specification; name it with ‘spec’ first"
          if !isProgram cx.prog prog then
            throw s!"line {n}: the right side of a refinement must be a program — \
              ok, assignments, ‘.’, if … fi and specifications — not {prog.render}"
          let k := (done.filter (·.refines == some spec)).length + 1
          cur := some { name := s!"{spec} refinement {k}", claim := e, lines := [],
                        cx := cx, refines := some spec, lineNo := n }
      | _ => throw s!"line {n}: write ‘refine SPEC ⇐ PROGRAM’"
    else
      match cur with
      | some c =>
          let l ← (proofLine n raw).mapError (s!"line {n}: " ++ ·)
          cur := some { c with lines := c.lines ++ [l] }
      | none => throw s!"line {n}: a proof line outside a theorem"
  if let some c := cur then
    done := c :: done
    cx := { cx with laws := cx.laws ++ [theoremLaw c] }
  return { theorems := done.reverse, cx := cx, ownSpecs := own }

/-- What an implementation still owes: a file with refinements must refine every
specification its parents named, and every specification any of its refinements
calls. Recursion is allowed — a refinement may call the specification it refines
— so what is required is that every specification reached is refined somewhere,
not that the calls bottom out. -/
def unrefined (f : PFile) : List String :=
  let refined := f.theorems.filterMap (·.refines)
  if refined.isEmpty then [] else
  let called := f.theorems.flatMap fun t =>
    if t.refines.isSome then
      match t.claim with
      | .bin .rimp _ prog => prog.vars.filter fun v => f.cx.prog.specs.any (·.1 == v)
      | _ => []
    else []
  (f.cx.inherited ++ called).eraseDups.filter (!refined.contains ·)

/-- Check every theorem of a parsed file, and that an implementation refines
everything it owes. -/
def checkParsed (f : PFile) : Except String (List Checked) := do
  let cs ← f.theorems.mapM check
  match unrefined f with
  | [] => return cs
  | us => throw s!"not refined: {String.intercalate ", " us} — an implementation \
      must refine every specification it inherits or calls"

/-- Parse and check a calculation file that extends nothing. -/
def checkFile (text : String) : Except String (List Checked) := do
  checkParsed (← file {} text)

/-- Read a calculation file and the files it extends, each path relative to the
file that names it. `depth` stops a cycle of `extends`. -/
partial def load (path : System.FilePath) (depth : Nat := 0) : IO PFile := do
  if depth > 16 then throw (IO.userError s!"{path}: ‘extends’ goes round in a circle")
  let text ← IO.FS.readFile path
  let dir := path.parent.getD "."
  let mut init : Ctx := {}
  for p in extendsOf text do
    let parent ← load (dir / p) (depth + 1)
    init := { laws := init.laws ++ parent.cx.laws,
              prog := { state := init.prog.state ++ parent.cx.prog.state,
                        specs := init.prog.specs ++ parent.cx.prog.specs },
              -- What the parent named or inherited and did not refine itself.
              inherited := init.inherited ++ ((parent.cx.inherited ++ parent.ownSpecs).filter
                fun n => !parent.theorems.any (·.refines == some n)) }
  match file init text with
  | .ok f => return f
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- A one-line summary of a checked theorem. -/
def _root_.Netty.Checked.summary (c : Checked) : String :=
  let byLaw := (c.steps.filter fun s => match s with | .lean _ => false | _ => true).length
  let premises := c.steps.flatMap fun s => match s with | .lawIf _ qs _ => qs | _ => []
  let left := c.steps.filterMap fun s => match s with | .lean h => some h | _ => none
  s!"{c.thm.name}: {c.thm.claim.render} — {c.steps.length} steps, {byLaw} checked by law" ++
    (if left.isEmpty then "" else
      s!", {left.length} left to Lean ({String.intercalate "; " left.eraseDups})") ++
    (if premises.isEmpty then "" else
      s!", premises left to Lean: {String.intercalate "; " (premises.map Expr.render)}")

end Proof
end Netty
