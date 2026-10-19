import Ampheck.Script

/-!
# The document's example, replayed and checked in Lean

The Netty document opens with a short proof:

```
⇐  a ⇒ (b⇒a)  portation
=  a∧b ⇒ a    specialization
=  T
```

This module, with the ones it names below, drives the kernel through it and
proves, by evaluation in Lean's kernel, that the session ends with no gaps, fully
zoomed out, and proving exactly `a ⇒ (b ⇒ a)`. Nothing here is a test in the usual sense: `Doc.step`,
`Doc.suggestions` and `Doc.outcome` are total functions on first-order data and
`Ampheck.Laws.boolean` is a literal, so `decide +kernel` settles the whole
replay: the kernel evaluates it, and the elaborator never does.

More replays are checked the same way: one that zooms in to a subexpression and
uses the context that zooming in supplies, one that reaches an outer line by a
click instead of by zooming out, one that goes back *into* a subproof it had
zoomed out of — and one that is refused because work was written after that
subproof closed — one that leaves a gap by direct entry and then closes it, one that applies a law to a *part* of a line instead of to the whole
of it, one that applies a law to a contiguous *segment* of an association that
neither the whole line nor a single operand can reach, one that zooms *into* such
a segment and splices it back, and two that exercise the
display collapses — a one-step subproof folded
into its parent line, and two zoom-ins matched by two zoom-outs drawn as one
zoom step. The grammar's named forms have replays of their own: `if … fi`, and the
quantifiers `∀` and `∃`, where a law about `∀x: d· b` has to read a line about
`∀i: nat· i ≥ 0` and the two places to zoom in to are a domain and a body.

## Where the theorems are

This module is the commands of each replay, the sessions built from laws written
out here, and what can be checked about them cheaply. The replays that run
against the *shipped* law lists (`Ampheck.Laws`) are checked in
`Ampheck.Replay.Zoom`, `Ampheck.Replay.Focus`, `Ampheck.Replay.Conditional` and
`Ampheck.Replay.Matching`, over the sessions of `Ampheck.Replay.Sessions`, and
are built by `lake build AmpheckReplay` (part of the default `lake build`), not
by `lake build ampheck`. Each of them has the kernel evaluate whole steps
against the full boolean list, every variant of every law matched at every place
of a line: tens of seconds and up to a few gigabytes of memory apiece, which a
small server building the command line should not pay. Nothing is weakened by
the move; the theorems are the same, stated and proved the same way, in another
file. Importing `Ampheck.Laws` also brings in all of `Lean` (its `lawFile%`
elaborator), which this module now does without.

`Ampheck.Demo` holds several of these proofs as *scripts*, which is what
`lake exe ampheck --demo=…` runs; `ampheck --selftest` checks that parsing each
script yields exactly the command list checked here, so the two cannot drift
apart.
-/

namespace Ampheck
namespace Replay

open Expr (var mvar num bin neg)

/-! ### The document's directions for zooming in

"positive position and any old direction makes the same new direction; negative
position and old direction ≤ makes new direction ≥ …" -/

example : Dir.zoom .down .positive = .down := by decide +kernel
example : Dir.zoom .up .positive = .up := by decide +kernel
example : Dir.zoom .down .negative = .up := by decide +kernel
example : Dir.zoom .up .negative = .down := by decide +kernel
example (p : Pos) : Dir.zoom .same p = .same := by cases p <;> decide
example (d : Dir) : Dir.zoom d .neutral = .same := by cases d <;> decide

/-! ### `a ⇒ (b ⇒ a)`, by portation and specialization -/

/-- `a ⇒ (b ⇒ a)`, the formula the document's example proves. -/
def goal : Expr := bin .imp (var "a") (bin .imp (var "b") (var "a"))

/-- The commands of the document's example. -/
def portation : List Cmd :=
  [ .start .boolean .up goal,
    .applyNamed "portation" none,
    .applyNamed "specialization" (some (.eq, .top)) ]

/-- Running a list of commands in a session and asking what it proves. -/
def provedIn (d : Doc) (cs : List Cmd) : Option Expr :=
  ((d.steps cs).toOption.bind fun d => d.outcome.toOption).map Outcome.proved

set_option maxRecDepth 100000

/-! ### Zooming in, and the context a zoom in supplies -/

/-- `(a ⇒ b) ⇒ (a ⇒ a ∧ b)`. -/
def dischargeGoal : Expr :=
  bin .imp (bin .imp (var "a") (var "b"))
    (bin .imp (var "a") (bin .and (var "a") (var "b")))

/-- Zoom in to the consequent — where `a ⇒ b` is context — discharge it, use
the context, zoom out, and finish with a base law. -/
def discharge : List Cmd :=
  [ .start .boolean .up dischargeGoal,
    .zoomIn (.operand 1),
    .applyNamed "discharge" (some (.eq, bin .imp (var "a") (var "b"))),
    -- The context law `a ⇒ b` can also be applied to a *part* of the line
    -- `a ⇒ b`, so the line it should write has to be named.
    .applyNamed "context" (some (.eq, .top)),
    .zoomOut,
    .applyNamed "base" (some (.eq, .top)) ]

/-! ### The focus lands anywhere: recomputing the zoom stack

The document lets a click land on any line of the proof. Focusing a line of an
*outer* level closes the levels that sit below it, exactly as a run of zoom-outs
would, so nothing is lost: each abandoned subproof still puts its bottom line
back into the line it was zoomed in from. -/

/-- The `discharge` proof again, but where `discharge` zooms out, this one
clicks on line 0 — the outermost line — and then carries on at that level. -/
def anywhere : List Cmd :=
  [ .start .boolean .up dischargeGoal,
    .zoomIn (.operand 1),
    .applyNamed "discharge" (some (.eq, bin .imp (var "a") (var "b"))),
    .applyNamed "context" (some (.eq, .top)),
    .setFocus 0,
    .setFocus 4,
    .applyNamed "base" (some (.eq, .top)) ]

/-- Two levels deep, one click closes both. Here the inner subproof rewrites
`a ∧ b` to `b ∧ a`, and focusing line 0 writes the two lines the two zoom-outs
would have written. -/
def nested : List Cmd :=
  [ .start .boolean .up dischargeGoal,
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .applyNamed "symmetry" (some (.eq, bin .and (var "b") (var "a"))),
    .setFocus 0 ]

/-! ### Going back into a closed subproof

A click may land on a line of a subproof that has already been zoomed out of.
The kernel takes that zoom out back — `Doc.reopenStep`, its exact inverse — so
the level is innermost again with its context in force, and the focus is on the
line that was clicked. What it refuses is a subproof closed *before* later work
was written: undoing the zoom out would undo the work. -/

/-- A new level open at the same depth is no obstacle: zoom in, step, zoom out,
zoom in again, and every line is still reachable. -/
def reopen : List Cmd :=
  [ .start .boolean .up dischargeGoal,
    .zoomIn (.operand 1),
    .applyNamed "discharge" (some (.eq, bin .imp (var "a") (var "b"))),
    .zoomOut,
    .zoomIn (.operand 1) ]

/-! ### Conditional laws at the number level

A law such as `x ≤ x + y ⇐ 0 ≤ y` has `⇐` for its main operator, so its
unconditional readings are steps a *boolean* line can take. What makes it a step a
number line can take is its *conditional* reading (`Law.conditional`): the
consequent `x ≤ x + y` is a relation that stands in a number margin, with `0 ≤ y`
left over as a premise. A premise the laws in force settle is no premise at all;
one they do not settle leaves the document's warning sign, the same gap direct
entry leaves, with the premise recorded on the line as what would close it. -/

/-- The context discharges a premise: a `context` law is exactly the premise. -/
theorem context_settles_the_premise :
    Law.settles [Law.context (bin .le (num 0) (var "m"))] (bin .le (num 0) (var "m"))
      = true := by decide +kernel

/-- `0 ≤ m ⇒ n ≤ n + m`. -/
def boundGoal : Expr :=
  bin .imp (bin .le (num 0) (var "m")) (bin .le (var "n") (bin .add (var "n") (var "m")))

/-- Zoom in to the consequent, where `0 ≤ m` becomes context; zoom in again to
`n + m`, which is a *number* level; and there the conditional law fires, its
premise discharged by that context. Then out, and the two boolean steps that
finish it. -/
def bound : List Cmd :=
  [ .start .boolean .up boundGoal,
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .applyNamed "upper bound" (some (.ge, var "n")),
    .zoomOut,
    .applyNamed "reflexive" (some (.eq, .top)),
    .zoomOut,
    .applyNamed "base" (some (.eq, .top)) ]

/-- The same law on the same line with nothing in force to settle its premise:
a number proof started at `n + m`. -/
def gapped : List Cmd :=
  [ .start .number .up (bin .add (var "n") (var "m")),
    .applyNamed "upper bound" (some (.ge, var "n")) ]

/-! ### The conditional reading at the boolean level

Item 18 read a law conditionally only where its consequent was a *number*
relation, because a boolean conditional law's own `⇒` already stands in a boolean
margin and a second reading would offer every such law twice. That limit is lifted
now, and the two things that kept it honest are still what keep it honest: the
conditional readings come last in `Law.variants`, so the dedup in
`Doc.suggestions` keeps the reading that needs nothing when two write the same
line, and `Doc.rank` puts every step that needs nothing before every step that
leaves a gap.

What the lift buys at the boolean level is the *context*. A context law is ground
— a zoom in supplies a fact, not a schema — so when the fact is itself an
implication whose consequent is a relation, its conditional reading has nothing
left unconstrained and is a step that can be taken. That is modus ponens as the
document would have a user do it: the implication in the context rewrites the
line, and what licenses the rewrite is another fact in the context. -/

/-- Whether a document offers any conditional reading, and whether every one it
offers is greyed. -/
def conditionalRows (d : Doc) : Bool × Bool :=
  let cond := d.suggestions.filter (·.premise.isSome)
  (!cond.isEmpty, cond.all fun s => !s.holes.isEmpty)

/-- `a ⇒ ((a ⇒ (b ⇒ c)) ⇒ (b ⇒ c))`: modus ponens, with the implication and its
antecedent both to be supplied by the context. -/
def ponensGoal : Expr :=
  bin .imp (var "a")
    (bin .imp (bin .imp (var "a") (bin .imp (var "b") (var "c"))) (bin .imp (var "b") (var "c")))

/-- Two zoom-ins put `a ⇒ (b ⇒ c)` and `a` in the context. The first is a ground
conditional law, so its conditional reading is one the kernel can take: at the
operand `b` of the line `b ⇒ c` it writes `c`, which is `c ⇒ c` put back, and the
premise it needs is `a` — the other context law. Then reflexivity, and the two
zoom-outs. -/
def ponens : List Cmd :=
  [ .start .boolean .up ponensGoal,
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .applyNamed "context" (some (.rimp, bin .imp (var "c") (var "c"))),
    .applyNamed "reflexive" (some (.eq, .top)),
    .zoomOut,
    .applyNamed "base" (some (.eq, .top)),
    .zoomOut,
    .applyNamed "base" (some (.eq, .top)) ]

/-- The same law with nothing in force to settle its premise: drop the outer
`a ⇒ …`, and the goal is no longer a theorem. -/
def ponensGappy : List Cmd :=
  [ .start .boolean .up
      (bin .imp (bin .imp (var "a") (bin .imp (var "b") (var "c"))) (bin .imp (var "b") (var "c"))),
    .zoomIn (.operand 1),
    .applyNamed "context" (some (.rimp, bin .imp (var "c") (var "c"))) ]

/-! ### Supplying a law variable by hand

Item 19 measured that every conditional reading of the shipped boolean laws is
greyed: a monotonicity or transitivity law relates the line to a third formula the
line does not determine, so matching leaves a variable free and the kernel will
not apply it. The document's answer is a small dialog box, and this is it as a
command: `Cmd.apply` and `Cmd.applyNamed` carry a `Subst`, and
`Doc.applySuggestion` instantiates the reading with it before taking the step.

Supplying a variable is not a new kind of step and needs no new argument for
soundness. Matching pinned some of the law's variables; the law holds for *every*
instantiation of the rest; so any expression may stand in their place. What the
bindings change is only which line the step writes and which premise it needs —
and the premise is asked again afterwards, because supplying a variable can turn
a premise the laws in force could not settle into one they can. That is what
happens here. -/

/-- `(x ⇒ y) ⇒ (x ∧ z ⇒ y ∧ z)`: monotonicity of `∧`, which is one of the laws
in force. -/
def monoGoal : Expr :=
  bin .imp (bin .imp (var "x") (var "y"))
    (bin .imp (bin .and (var "x") (var "z")) (bin .and (var "y") (var "z")))

/-- Zoom in to the consequent, where `x ⇒ y` becomes context. There the
monotonicity reading offers to rewrite the operand `x ∧ z`, and it is greyed:
nothing on the line says what `b` is, and the premise it would need is stated with
`b` still in it. Supplying `b := y` by hand makes it a step — and the premise is
then `x ⇒ y`, which the context settles, so it leaves no gap. -/
def dialog : List Cmd :=
  [ .start .boolean .up monoGoal,
    .zoomIn (.operand 1),
    .applyNamed "monotonic"
      (some (.rimp, bin .imp (bin .and (var "y") (var "z")) (bin .and (var "y") (var "z"))))
      [("b", var "y")],
    .applyNamed "reflexive" (some (.eq, .top)),
    .zoomOut,
    .applyNamed "base" (some (.eq, .top)) ]

/-- The premise path is unchanged. On a bare line, with nothing in force to settle
it, the same law and the same binding still write the line the law licenses and
still leave the document's warning sign, with the premise the binding made ground
recorded beside it. -/
def dialogGappy : List Cmd :=
  [ .start .boolean .down (bin .and (var "x") (var "z")),
    .applyNamed "monotonic" (some (.imp, bin .and (var "y") (var "z"))) [("b", var "y")] ]

/-! ### `if … then … else … fi`

The document's conditional expression, and the first of the grammar's named forms
after the boolean and number fragment. It is a form of its own — `Expr.cond`, one
node — and not sugar for anything: the law that says what it *means*,
`case analysis`, is a line of the law file like any other, not something the
kernel does silently.

It brackets itself with `fi`, so it needs no parentheses and takes a whole
expression in each of its three places. Its main operands are the condition and
the two branches: three places to zoom in to and three places a law may be
applied to. The branches are in *positive* position and the condition in
*neutral*, because changing the condition switches between the branches rather
than weakening or strengthening the whole — so zooming in to a condition admits
only `=`. Zooming in to a branch gains the condition, or its negation, as
context, exactly as zooming in to the consequent of `a ⇒ b` gains `a`. -/

/-- It renders as it is written. That the parser reads it back — and that `fi`
closes it, so `if b then x else y fi ∧ z` is the conditional and-ed with `z` and
not a conditional whose else-branch is `y ∧ z` — is checked by `ampheck --selftest`
rather than here: the parser is a `partial def`, which the kernel cannot reduce,
which is why script parsing has always been checked at run time. -/
theorem cond_renders :
    (Expr.cond (var "b") (var "x") (var "y")).render = "if b then x else y fi" := by decide +kernel

/-- Its type is its branches': a number in one of them makes the whole a number,
and two identifiers settle nothing. The condition says nothing about it. -/
theorem cond_ty :
    ((Expr.cond (var "b") (num 1) (var "y")).tyOf?, (Expr.cond (var "b") (var "x") (var "y")).tyOf?)
      = (some .number, none) := by decide +kernel

/-- The condition is neutral and the branches are positive. -/
theorem cond_positions :
    ((List.range 3).map fun i => (Expr.cond (var "b") (var "x") (var "y")).operandPos i)
      = [.neutral, .positive, .positive] := by decide +kernel

/-- A law of the list rewrites one: `if ⊤ then x else y fi = x` by `case base`. -/
def condBase : List Cmd :=
  [ .start .boolean .same (Expr.cond .top (var "x") (var "y")),
    .applyNamed "case base" (some (.eq, var "x")) ]

/-- And a proof that works *inside* one: `if b then b else ⊤ fi`, by zooming in to
the then-branch — where `b` becomes context — using it there, and folding the two
equal branches with `case idempotent`. -/
def condBranch : List Cmd :=
  [ .start .boolean .up (Expr.cond (var "b") (var "b") .top),
    .zoomIn (.operand 1),
    .applyNamed "context" (some (.eq, .top)),
    .zoomOut,
    .applyNamed "case idempotent" (some (.eq, .top)) ]

/-- The eval hooks go through the form, so it leaves no hole in the law checks.
`boolean_isTautology` covers the five `case` laws the boolean list gained, which
is the boolean evaluator; this is the number one, where a number-valued `if` needs
the *boolean* evaluator for its condition and the two are mutually recursive. -/
def absNonneg : Law :=
  { name := "absolute value", vars := ["x"],
    stmt := bin .le (num 0)
      (Expr.cond (bin .le (num 0) (mvar "x")) (mvar "x") (bin .sub (num 0) (mvar "x"))) }

theorem absNonneg_holdsOnInts : Law.holdsOnInts [-2, -1, 0, 1, 2] absNonneg = true := by decide +kernel

/-! ### `∀ids: d· b` and `∃ids: d· b`

The document's quantified expressions — `quantifier identifiers : expression ·
expression` in its grammar — and the next of the grammar's named forms after
`if … fi`. `Expr.quant` is one node: the quantifier, the identifiers it binds, the
domain they range over, and the body they are bound in. There is no abbreviated
form that leaves the domain out, because the document excluded those.

Its two main operands are the domain and the body, so those are the two places to
zoom in to and the two places a law may be applied to. The document's Scope
section fixes their positions — said there of the function `〈v:d→b〉`, which binds
the same way — "the domain is in a neutral position and the body is in a positive
position", and "for the body, we gain the context `v:d`".

Three things are new with this form, and none of them was needed before.

* A **binder**. What a quantifier binds is a list of names, not an expression: not
  an operand, not a place to zoom in to, and — this is what a law file needs — not
  an identifier of the line that states a law (`Expr.vars`), so generalizing a law
  file line leaves it alone. A quantifier in a law therefore has to match a
  quantifier in a line *modulo the binder name*: the law's own name is renamed to
  the line's before the bodies are matched, and the renaming comes back out when
  the law's other side is instantiated.
* A **domain**, which is a bunch. The kernel has no bunch type and still zooms in
  to a domain: the position is neutral, so only `=` is admitted there. What it
  cannot do is *type check* what it offers — see
  `quant_domain_is_offered_boolean_laws`.
* `:`, membership, one `BinOp` and no more of the bunch notation, because the
  context a zoom in to the body gains has to be an expression before it can be a
  law. -/

/-- `∀i: nat· i ≥ 0`: a quantified line, whose binder is spelled `i` where every
shipped quantifier law spells its own `x`. -/
def bounded : Expr := Expr.quant .all ["i"] (var "nat") (bin .ge (var "i") (num 0))

/-- It renders as the document writes it. That the parser reads it back — and that
the body runs to the end, so `∀i: nat· i ≥ 0 ∧ p` quantifies the conjunction — is
checked by `ampheck --selftest`, the parser being a `partial def` the kernel cannot
reduce. -/
theorem quant_renders : bounded.render = "∀i: nat· i ≥ 0" := by decide +kernel

/-- Nothing closes the body, so the form brackets itself as soon as anything
surrounds it. This is the difference from `if … fi`, which `fi` closes. -/
theorem quant_brackets_itself :
    (bin .and bounded (var "p")).render = "(∀i: nat· i ≥ 0) ∧ p" := by decide +kernel

/-- It is boolean — `Σ` and `Π`, the quantifiers that would give a number, are not
in the grammar — and so is its body. -/
theorem quant_ty : (bounded.tyOf?, bounded.operandTy 1 .boolean) = (some .boolean, .boolean) := by
  decide

/-- The domain is neutral and the body is positive, so zooming in to a domain
admits only `=` and zooming in to a body leaves the direction alone. -/
theorem quant_positions :
    ((List.range 2).map bounded.operandPos) = [.neutral, .positive] := by decide +kernel

/-- Two clickable pieces, the domain and the body, and what the form opens with:
the quantifier and the names it binds. Those names are not a piece — a display
writes them, and a click on them is not a zoom. -/
theorem quant_draws_as_two_pieces :
    (bounded.mainOp, bounded.operandTexts) = ("∀i", ["nat", "i ≥ 0"]) := by decide +kernel

/-- The one *free* identifier of `∀i: nat· i ≥ 0` is `nat`: what the quantifier
binds is not an identifier of the expression, so generalizing a law file line —
which is generalizing every identifier of it — turns `nat` into a law variable and
leaves the bound `i` exactly where it was. Without this a law about `∀x: d· b`
would quantify the `x` it binds and mean nothing at all. -/
theorem quant_binds_what_generalizing_must_leave_alone :
    (bounded.vars, bounded.generalize ["nat", "i"])
      = (["nat"], Expr.quant .all ["i"] (mvar "nat") (bin .ge (var "i") (num 0))) := by decide +kernel

/-- "For the body, we gain the context `v:d`" — one context law per identifier the
quantifier binds, and that is what `:` is here for. The domain gains nothing: it
is outside the scope of what is bound, and the document says it "cannot mention
`v`" — which `Ampheck.Parser` refuses to read. -/
theorem quant_body_gains_the_membership :
    (Expr.contextOf bounded 1, Expr.contextOf bounded 0)
      = ([bin .mem (var "i") (var "nat")], []) := by decide +kernel

/-- And `:` is written as the document writes it, tight on its left. -/
theorem mem_renders : (bin .mem (var "i") (var "nat")).render = "i: nat" := by decide +kernel

/-- The boolean evaluator cannot decide a quantifier, and says so rather than
guessing: what `∀i: nat· i ≥ 0` claims depends on the bunch `nat`, which is not a
boolean. This is why the quantifier law list is trusted as transcribed
(`Ampheck.quantifier_isBeyondTheBooleanEvaluator`) where the boolean one is checked
(`Ampheck.boolean_isTautology`). -/
theorem quant_is_beyond_the_boolean_evaluator : bounded.evalBool [] = none := by decide +kernel

/-- Nor can the number evaluators, for the same reason: an assignment of integers
to names says nothing about what bunch a domain is. `Σ` and `Π`, the quantifiers
that would have a number to give, are not in the grammar at all.

Like every theorem here that touches `Int` — `absNonneg_holdsOnInts` and
`Ampheck.number_holdsOnInts` among them — this one carries `Classical.choice` and
`Quot.sound` out of core's integer instances as well as `propext`. -/
theorem quant_is_beyond_the_number_evaluators :
    (bounded.evalProp [], bounded.evalInt []) = (none, none) := by decide +kernel

/-- Matching is modulo the binder name: the law's `x` matches the line's `i` once
and once only, and the law's *other* side comes back written in the line's own
name. Nothing else about a binder is read — not what it is called, only how many
names there are. -/
theorem quant_matches_modulo_the_binder_name :
    ((Expr.matchAll (neg (Expr.quant .all ["x"] (mvar "d") (mvar "b"))) (neg bounded) []).map
      fun σ => (Expr.quant .ex ["x"] (mvar "d") (neg (mvar "b"))).instantiate σ)
      = [Expr.quant .ex ["i"] (var "nat") (neg (bin .ge (var "i") (num 0)))] := by decide +kernel

/-- A law that writes the same binder twice means the same variable twice, and
refuses a line that binds two different ones: `(∀x: d· b) ∧ (∀x: d· c)` — the way
back that `generalized distribution` also reads — does not match
`(∀i: nat· p) ∧ (∀j: nat· q)`. Making it match would mean renaming inside the
line, which is a different thing from renaming the law. -/
theorem quant_binder_names_must_agree :
    Expr.matchAll
      (bin .and (Expr.quant .all ["x"] (mvar "d") (mvar "b"))
                (Expr.quant .all ["x"] (mvar "d") (mvar "c")))
      (bin .and (Expr.quant .all ["i"] (var "nat") (var "p"))
                (Expr.quant .all ["j"] (var "nat") (var "q"))) [] = [] := by decide +kernel

/-- A shipped law rewriting a quantified line: `¬(∀i: nat· i ≥ 0)` is
`∃i: nat· ¬(i ≥ 0)` by `generalized duality`, with the law's `x` written as the
line's `i`. -/
def quantDuality : List Cmd :=
  [ .start .boolean .same (neg bounded),
    .applyNamed "generalized duality"
      (some (.eq, Expr.quant .ex ["i"] (var "nat") (neg (bin .ge (var "i") (num 0))))) ]

/-- And a proof that works *inside* a body: `∀i: nat· ¬¬(i ≥ 0)`, by zooming in to
the body — where `i: nat` becomes context — folding the double negation there, and
zooming back out. -/
def quantBody : List Cmd :=
  [ .start .boolean .same
      (Expr.quant .all ["i"] (var "nat") (neg (neg (bin .ge (var "i") (num 0))))),
    .zoomIn (.operand 1),
    .applyNamed "double negation" (some (.eq, bin .ge (var "i") (num 0))),
    .zoomOut ]

/-- `∀i: nat· i ≥ 0 ∧ i ≤ 9`, which `generalized distribution` takes apart into
two quantifications of the same variable. -/
def distributionLine : Expr :=
  Expr.quant .all ["i"] (var "nat")
    (bin .and (bin .ge (var "i") (num 0)) (bin .le (var "i") (num 9)))

/-- The law is named by the line it writes, because it offers two: symmetry reads
the conjunction both ways round, so `∧` may be written in either order. -/
def quantDistribution : List Cmd :=
  [ .start .boolean .same distributionLine,
    .applyNamed "generalized distribution"
      (some (.eq, bin .and (Expr.quant .all ["i"] (var "nat") (bin .ge (var "i") (num 0)))
                           (Expr.quant .all ["i"] (var "nat") (bin .le (var "i") (num 9))))) ]

/-! ### A gap, and closing it -/

/-- Type `a` in directly under `¬¬a`, which leaves a warning sign; then move
the focus back and take the suggestion that writes the line already there,
which replaces the sign with the law's name. -/
def gap : List Cmd :=
  [ .start .boolean .up (neg (neg (var "a"))),
    .direct .eq (var "a"),
    .setFocus 0,
    .applyNamed "double negation" (some (.eq, var "a")) ]

/-! ### Matching modulo associativity, symmetry and the identity

The document says that clicking on any operand of `a + b + c` zooms in to it,
with no need of associative laws, and it has `symmetry` and `identity` laws that
a user should likewise not have to spend a step on. Applying a law reads a line
modulo all three: `specialization`, `a ∧ b ⇒ a`, matches `x ∧ y ∧ z` — which is
`(x ∧ y) ∧ z` — with `a := x` and `b := y ∧ z` as readily as with `a := x ∧ y`
and `b := z`, and, since `∧` is symmetric, with `a := y` and `b := x ∧ z` too. -/

/-- `x ∧ y ∧ z`, read as `(x ∧ y) ∧ z`. -/
def conjunction : Expr := bin .and (bin .and (var "x") (var "y")) (var "z")

/-! ### The order the suggestions come in

Every widening of matching lengthened the list, and `Doc.rank` is the order it is
offered in: applicable before unconstrained, then fewer unconstrained variables,
then the shorter line the step writes, then the more specific place, then the law
file's own order. Rather than write a hundred-line list out, what is checked here
is that the keys never go backwards — which is what it means for the list to be in
that order — and that ranking an already ranked list changes nothing, which is
what it means for the order to be total and the sort stable. -/

/-- The numbers `Doc.rank` sorts by, most important first. -/
def key (s : Suggestion) : List Nat :=
  [if s.holes.isEmpty then 0 else 1, if s.premise.isNone then 0 else 1,
   s.holes.length, s.result.size, s.part.rank]

/-- Lexicographic `≤` on those keys. -/
def leKey : List Nat → List Nat → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => if a == b then leKey as bs else a < b

/-- Whether a list of keys never goes backwards. -/
def ranked : List (List Nat) → Bool
  | k :: j :: rest => leKey k j && ranked (j :: rest)
  | _ => true

/-- A proof that the reading associativity adds really can be taken: one step
from `x ∧ y ∧ z` to `x`, where before it took an associative law first. -/
def assoc : List Cmd :=
  [ .start .boolean .down conjunction,
    .applyNamed "specialization" (some (.imp, var "x")) ]

/-- And one that symmetry adds: `x ∧ y ⇒ y`, in one step. No cut of `x ∧ y`
into contiguous segments gives `a := y`, so before this the proof needed the
symmetry law first. -/
def swap : List Cmd :=
  [ .start .boolean .down (bin .and (var "x") (var "y")),
    .applyNamed "specialization" (some (.imp, var "y")) ]

/-- A pattern operand that is not a law variable takes one operand and no
more: `a ∧ (b ∨ c)` cannot read `x ∧ y ∧ z`, because no part of it is a
disjunction — not even now that the parts need not be contiguous. -/
theorem no_match_without_a_law_variable :
    Expr.matchAll (bin .and (mvar "a") (bin .or (mvar "b") (mvar "c"))) conjunction [] = [] := by
  decide

/-! ### Symmetry and the identity, at the matcher

The three readings, each in one line. Symmetry lets a pattern operand take
operands that are not next to each other; the identity lets a pattern operand
that *is* the unit take none at all, and lets a unit the line writes be struck
out. What it does not do is let a law *variable* take none — otherwise every
binary law would match every line. -/

/-- `a ∧ b` matches `y ∧ x`, which associativity alone cannot do: the two ways
round are the two matches, the one that needs no rearrangement first. -/
theorem symmetry_matches_a_swap :
    Expr.matchAll (bin .and (mvar "a") (mvar "b")) (bin .and (var "y") (var "x")) []
      = [[("b", var "x"), ("a", var "y")], [("b", var "y"), ("a", var "x")]] := by decide +kernel

/-- A law written with a unit reads a line that left it out: `a ∧ ⊤` matches
the bare line `y`. -/
theorem identity_is_elided :
    Expr.matchAll (bin .and (mvar "a") .top) (var "y") [] = [[("a", var "y")]] := by decide +kernel

/-- A unit the line writes is struck out of it: `a ∧ a` matches `x ∧ ⊤ ∧ x`,
which it cannot do while the `⊤` is still there to be shared out. -/
theorem identity_is_struck_out :
    Expr.matchAll (bin .and (mvar "a") (mvar "a"))
      (bin .and (bin .and (var "x") .top) (var "x")) [] = [[("a", var "x")]] := by decide +kernel

/-- But a law variable never takes the unit the line does not mention, so
`a ∧ b` still does not match a line that is not a conjunction at all. That is
what keeps the identity from making every binary law apply everywhere. -/
theorem a_variable_does_not_take_the_unit :
    Expr.matchAll (bin .and (mvar "a") (mvar "b")) (var "y") [] = [] := by decide +kernel

/-- `=` is symmetric without being an association, so it is matched by trying
its two operands both ways round. -/
theorem equality_is_symmetric :
    Expr.matchAll (bin .eq (mvar "a") (var "y")) (bin .eq (var "y") (var "x")) []
      = [[("a", var "x")]] := by decide +kernel

/-! ### A law applied to a part of a line

Real Ampheck applies a law "to a part, as a result of minimization": the law
matches a subexpression of the line and the suggestion rewrites that part in
place. The kernel offers one site per main operand as well as the whole line, so
a step that used to need a zoom in, an application and a zoom out is one
application on the outer line. -/

/-- `x ∧ (y ∨ y)`, whose second main operand idempotence folds. -/
def part : Expr := bin .and (var "x") (bin .or (var "y") (var "y"))

/-- Idempotence does not match `x ∧ (y ∨ y)` at all: its main operator is `∧`,
not `∨`. So the step below is not a whole-line match under any reading. -/
theorem idempotence_misses_the_whole_line :
    Expr.matchAll (bin .or (mvar "a") (mvar "a")) part [] = [] := by decide +kernel

/-- It does match the second main operand, and the suggestion rewrites that
part in place, leaving `x` alone. -/
def minimize : List Cmd :=
  [ .start .boolean .same part,
    .applyNamed "idempotent" (some (.eq, bin .and (var "x") (var "y"))) ]

/-! ### A law applied to a contiguous segment of an association

The document reads `x ∧ y ∧ z` as having the part `y ∧ z` just as it has the part
`y`, so a contiguous run of two or more operands of an association is a site of
its own. An associative operator puts all of its operands in one position, so a
run of them is in that same position: the type, the direction and the connective
a rewrite there writes are word for word those of a single main operand, and the
soundness argument is the one minimization already had. -/

/-- `x ∧ y ∧ y ∧ z`, whose middle two operands idempotence folds. -/
def segmentLine : Expr :=
  bin .and (bin .and (bin .and (var "x") (var "y")) (var "y")) (var "z")

/-- The segments of a four-operand association: every contiguous run of two or
three of its operands. A run of one is a main operand and the run of all four is
the line, so neither is listed. -/
theorem segmentLine_segments :
    segmentLine.segments = [(0, 2), (0, 3), (1, 2), (1, 3), (2, 2)] := by decide +kernel

/-- A two-operand association has no segments at all: `x ∧ (y ∨ y)` has the two
main operands `minimize` already reaches, and nothing between them. -/
theorem a_pair_has_no_segments : part.segments = [] := by decide +kernel

/-- Idempotence matches neither the whole line — no sharing out of
`x ∧ y ∧ y ∧ z` makes its two halves equal … -/
theorem idempotence_misses_the_whole_association :
    Expr.matchAll (bin .and (mvar "a") (mvar "a")) segmentLine [] = [] := by decide +kernel

/-- … nor any single main operand, which are the bare identifiers `x`, `y`, `y`,
`z`. So neither site the kernel had before this can fold the repetition. -/
theorem idempotence_misses_every_operand :
    segmentLine.operands.all
      (fun o => Expr.matchAll (bin .and (mvar "a") (mvar "a")) o [] == []) = true := by decide +kernel

/-- The segment `y ∧ y` it does match, and the suggestion folds it where it
stands, leaving `x` and `z` alone. -/
def segmentFold : List Cmd :=
  [ .start .boolean .same segmentLine,
    .applyNamed "idempotent"
      (some (.eq, bin .and (bin .and (var "x") (var "y")) (var "z"))) ]

/-- `×` is associative, so it has segments, and its operands are neutral — the
document's position table leaves `×` out, since a factor is monotonic only when
the other is nonnegative. So a segment of it is a neutral site whatever the
level's direction: `=` inside, and `=` in the margin outside. That is the
position table read for a run of operands exactly as it is read for one. -/
theorem times_segments_are_neutral :
    (Doc.sites { ty := .number, dir := .down, start := 0 }
        (bin .mul (bin .mul (var "n") (var "m")) (var "k"))).filterMap
      (fun s => match s.part with
        | .segment start len => some (start, len, s.pos, s.dir)
        | _ => none)
      = [(0, 2, .neutral, .same), (1, 2, .neutral, .same)] := by decide +kernel

/-! ### Numbers: the directions are `≤ = ≥`, and a negative position turns them

Nothing about the kernel is boolean; the direction machinery is the same at
every type. Here is the same machinery at the number type, with a law list of
one law, showing that zooming in to the subtrahend of `n - m` — a negative
position — turns the direction from `≤` to `≥`. -/

/-- `x + 0 = x`. -/
def numberIdentity : Law :=
  { name := "identity", vars := ["x"], stmt := bin .eq (bin .add (mvar "x") (num 0)) (mvar "x") }

/-- `x ≤ x + 1`, a law whose main operator is a direction rather than `=`. -/
def numberSuccessor : Law :=
  { name := "successor", vars := ["x"],
    stmt := bin .le (mvar "x") (bin .add (mvar "x") (num 1)) }

/-- A session whose whole law list is those two laws. -/
def numberSession : Doc := { laws := [numberIdentity, numberSuccessor] }

/-- Start at `n - m` going down, zoom in to `m`, rewrite it to `m + 0`, and
zoom back out. -/
def number : List Cmd :=
  [ .start .number .down (bin .sub (var "n") (var "m")),
    .zoomIn (.operand 1),
    .applyNamed "identity" (some (.eq, bin .add (var "m") (num 0))),
    .zoomOut ]

/-- The subtrahend is in a negative position, so the subproof's direction is
`≥` where the proof's was `≤`. -/
theorem number_direction_turns :
    ((numberSession.steps (number.take 2)).toOption.bind
      fun d => d.frame?.map Frame.dir) = some .up := by decide +kernel

/-- The subproof proves an equality, so zooming out writes `=`, and the whole
calculation proves `n - m = n - (m + 0)`. -/
theorem number_proves :
    provedIn numberSession number
      = some (bin .eq (bin .sub (var "n") (var "m"))
                      (bin .sub (var "n") (bin .add (var "m") (num 0)))) := by decide +kernel

/-! ### A unit the line never writes

`BinOp.identity` names `0` as the unit of `+`, so a law written with it can read
a line that left it out. This is the one shape that matching modulo identity
adds and nothing else can: the line is not an addition at all, and no
rearranging of operands will make it one. -/

/-- `x + 0 ≤ x + 1`, a law written with the unit. -/
def numberUnit : Law :=
  { name := "unit successor", vars := ["x"],
    stmt := bin .le (bin .add (mvar "x") (num 0)) (bin .add (mvar "x") (num 1)) }

/-- A session whose whole law list is that one law. -/
def unitSession : Doc := { laws := [numberUnit] }

/-- Against the bare line `n`, the law reads `n` as `n + 0` and offers
`n + 1` — the only suggestion there is, and one no syntactic match could
make. -/
theorem numberUnit_elides_the_zero :
    ((unitSession.steps [.start .number .down (var "n")]).toOption.map fun d =>
      d.suggestions.map fun s => (s.op, s.result))
      = some [(.le, bin .add (var "n") (num 1))] := by decide +kernel

/-- And the step can be taken: `n ≤ n + 1`, with the unit never written. -/
def numberUnitProof : List Cmd :=
  [ .start .number .down (var "n"),
    .applyNamed "unit successor" (some (.le, bin .add (var "n") (num 1))) ]

theorem numberUnit_proves :
    provedIn unitSession numberUnitProof
      = some (bin .le (var "n") (bin .add (var "n") (num 1))) := by decide +kernel

/-! ### A part in a negative position, without zooming

`successor` is a `≤` law, and the subtrahend of `n - m` is in a negative
position, so applying it there turns the step around: the margin gets `≥` at
the outer level even though the law wrote `≤` at the part. This is the same
turning `number` above makes with a zoom in and a zoom out, in one step on the
outer line. -/

/-- `n - m ≥ n - (m + 1)`, by `successor` on the subtrahend. -/
def numberMinimize : List Cmd :=
  [ .start .number .up (bin .sub (var "n") (var "m")),
    .applyNamed "successor"
      (some (.ge, bin .sub (var "n") (bin .add (var "m") (num 1)))) ]

theorem numberMinimize_proves :
    provedIn numberSession numberMinimize
      = some (bin .ge (bin .sub (var "n") (var "m"))
                      (bin .sub (var "n") (bin .add (var "m") (num 1)))) := by decide +kernel

/-- The turning is the only thing the position can do here: at the whole line,
whose direction is `≥`, `successor`'s `≤` is not allowed in the margin at all,
so the only suggestion it makes is the one on the part. -/
theorem numberMinimize_is_the_only_successor_step :
    ((numberSession.steps [.start .number .up (bin .sub (var "n") (var "m"))]).toOption.map
      fun d => (d.suggestions.filter (·.law == "successor")).map fun s => (s.op, s.result))
      = some [(.ge, bin .sub (var "n") (bin .add (var "m") (num 1)))] := by decide +kernel

/-! ### The display collapses

A proof written by zooming keeps lines a reader does not need. The document
collapses two such patterns, and `Doc.shownLines` is that collapse: which lines
a display draws, at what depth, and with what law name at the end of them. The
document itself keeps every line, so what is checked here is the *drawing*. -/

/-- What a display draws, for a given list of laws: for each line it shows, the
depth it is drawn at, its margin connective, its formula and the name at the end
of it. -/
def shownIn (d₀ : Doc) (cs : List Cmd) : Option (List (Nat × Option BinOp × Expr × String)) :=
  (d₀.steps cs).toOption.map fun d =>
    d.shownLines.map fun s =>
      (s.depth, (d.lines[s.index]!).conn, (d.lines[s.index]!).expr, s.note)

/-- The long way round to `x ∧ y`: zoom in to `y ∨ y`, fold it there, and zoom
back out — the four lines that applying a law to a *part* replaces with two. -/
def fold : List Cmd :=
  [ .start .boolean .same part,
    .zoomIn (.operand 1),
    .applyNamed "idempotent" (some (.eq, var "y")),
    .zoomOut ]

/-- `x ∧ (y ∨ (¬¬z ∧ ¬¬z))`: two levels down there is a two-step subproof, so
the merge of two zooms has something to leave behind. -/
def nest : Expr :=
  bin .and (var "x")
    (bin .or (var "y") (bin .and (neg (neg (var "z"))) (neg (neg (var "z")))))

/-- Zoom in twice, take two steps, and zoom out twice. -/
def merge : List Cmd :=
  [ .start .boolean .same nest,
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .applyNamed "idempotent" (some (.eq, neg (neg (var "z")))),
    .applyNamed "double negation" (some (.eq, var "z")),
    .zoomOut,
    .zoomOut ]

/-- A merge can expose a fold: the same two zooms with a *one*-step subproof
inside collapse all the way to two lines, the law's name on the first of them.
The pass is a fixpoint, so both collapses run. -/
def mergeThenFold : List Cmd :=
  [ .start .boolean .same
      (bin .and (var "x") (bin .or (var "y") (bin .and (var "z") (var "z")))),
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .applyNamed "idempotent" (some (.eq, var "z")),
    .zoomOut,
    .zoomOut ]

/-- A gap is never collapsed away: the same fold, but with the subproof's one
step typed in directly instead of taken from a law, keeps all four lines and
its warning sign. -/
def gapInside : List Cmd :=
  [ .start .boolean .same part,
    .zoomIn (.operand 1),
    .direct .eq (var "y"),
    .zoomOut ]

/-! ### A gap carried out of the subproof that holds it

Zooming out justifies the outer step by the subproof, so a subproof that still
has a gap in it leaves the outer step unjustified too. `Doc.zoomOut` marks the
line it zoomed in from, and the outer level draws the warning sign on the line
just before the splice, which is where the document puts it. -/

/-- Two levels down, the gap is carried out twice: the direct entry gaps line 2
inside the innermost level, the first zoom out gaps line 1, and the second gaps
line 0. A gap does not get lost by being deep. -/
def gapCarries : List Cmd :=
  [ .start .boolean .same
      (bin .and (var "x") (bin .or (var "y") (bin .and (var "z") (var "z")))),
    .zoomIn (.operand 1),
    .zoomIn (.operand 1),
    .direct .eq (var "z"),
    .zoomOut,
    .zoomOut ]

/-! ### A segment as a level: zooming in to a run of operands

A part is not only a place a law is applied to; it is a level you can work
inside. `Cmd.zoomIn` takes a `Part`, so a contiguous segment of an association is
a zoom target as much as a single main operand: the subproof's first line is the
run, left-associated as `Expr.segmentExpr` builds it, its type and direction are
the ones the segment *site* carries, its context is what the operands outside the
run supply, and zooming out splices the bottom line back through the same
`Part.replace` a site rewrite uses. -/

/-- The long way round to `x ∧ y ∧ z`: zoom in to the segment `y ∧ y` — the two
operands from the first — fold it there, and zoom back out. -/
def segmentZoom : List Cmd :=
  [ .start .boolean .same segmentLine,
    .zoomIn (.segment 1 2),
    .applyNamed "idempotent" (some (.eq, var "y")),
    .zoomOut ]

/-- The scripts `lake exe ampheck --demo=…` runs, paired with the command lists
checked above; `ampheck --selftest` compares them. -/
def demos : List (String × String × List Cmd) :=
  [("portation", Demo.portation, portation),
   ("discharge", Demo.discharge, discharge),
   ("gap", Demo.gap, gap),
   ("minimize", Demo.minimize, minimize),
   ("segment", Demo.segment, segmentFold),
   ("segfold", Demo.segfold, segmentZoom),
   ("fold", Demo.fold, fold),
   ("merge", Demo.merge, merge)]

end Replay
end Ampheck
