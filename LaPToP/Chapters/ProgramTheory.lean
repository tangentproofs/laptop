import Verso
import VersoManual
import VersoBlueprint
import LaPToP.ProgramTheory.Specifications

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Program Theory" =>

:::group "program_theory_core"
Programs as predicates on pre- and post-states; refinement as implication;
sequential composition, conditionals, and assignment in Hehner's theory.
Section 4.0 of the book is formalized in the Lean module
`LaPToP.ProgramTheory.Specifications`.
:::

:::definition "program_as_predicate" (parent := "program_theory_core") (lean := "LaPToP.ProgramTheory.Spec, LaPToP.ProgramTheory.Spec.ext, LaPToP.ProgramTheory.Spec.outputs, LaPToP.ProgramTheory.Spec.Satisfiable, LaPToP.ProgramTheory.Spec.Unsatisfiable, LaPToP.ProgramTheory.Spec.Deterministic, LaPToP.ProgramTheory.Spec.Nondeterministic, LaPToP.ProgramTheory.Spec.Implementable, LaPToP.ProgramTheory.Spec.satisfiable_iff, LaPToP.ProgramTheory.Spec.unsatisfiable_iff, LaPToP.ProgramTheory.Spec.deterministic_iff, LaPToP.ProgramTheory.Spec.nondeterministic_iff, LaPToP.ProgramTheory.Spec.implementable_iff")
A program (or specification) is a Boolean expression relating initial and final
states. Implementing a specification $`S` by a program $`P` means proving
$`P \Rightarrow S` (refinement).

"A specification is a binary expression whose variables represent quantities of
interest": the prestate $`\sigma` and the poststate $`\sigma'`. In Lean a
specification over a state space $`\sigma` is a relation `Spec σ := σ → σ → Prop`
between prestate and poststate — a proposition rather than a `Binary`, since
$`\forall\sigma\cdot\exists\sigma'\cdot S` over an infinite state space is not a
computable binary value. Equality of specifications is Lean equality of
relations, which by extensionality is the book's
$`\forall\sigma, \sigma'\cdot P = Q`. The book's four counting definitions —
$`S` is *unsatisfiable* for prestate $`\sigma` when $`{\rm c\llap{/}}(\S\sigma'\cdot S) < 1`,
*satisfiable* when $`\ge 1` (equivalently $`\exists\sigma'\cdot S`), *deterministic*
when $`\le 1`, *nondeterministic* when $`> 1` — and *implementable*,
$`\forall\sigma\cdot\exists\sigma'\cdot S`, are defined and shown equivalent to
their counting forms via {uses "bunch_axioms_size"}[] and
{uses "solution_quantifier"}[]. Specifications take values in
{uses "boolean_domain"}[]; the state variables are those of
{uses "state_as_variables"}[].
:::

:::definition "specification_notations" (parent := "program_theory_core") (lean := "LaPToP.ProgramTheory.Spec.top, LaPToP.ProgramTheory.Spec.bot, LaPToP.ProgramTheory.Spec.ok, LaPToP.ProgramTheory.Spec.and, LaPToP.ProgramTheory.Spec.or, LaPToP.ProgramTheory.Spec.not, LaPToP.ProgramTheory.Spec.cond, LaPToP.ProgramTheory.Spec.seq, LaPToP.ProgramTheory.Spec.Refines, LaPToP.ProgramTheory.Spec.State, LaPToP.ProgramTheory.Spec.assign, LaPToP.ProgramTheory.Spec.assign_iff")
The specification notations of Section 4.0.0: $`\top` and $`\bot`;
$`\mathit{ok} = (\sigma' = \sigma) = (x' = x \land y' = y \land \ldots)`, satisfied by
doing nothing; $`S \land R`, $`S \lor R`, $`\neg S`;
$`\mathbf{if}\ b\ \mathbf{then}\ S\ \mathbf{else}\ R` for $`b` a binary expression of
the initial state; sequential composition
$`S.\ R = \exists\sigma''\cdot \langle\sigma'\cdot S\rangle\,\sigma'' \land \langle\sigma\cdot R\rangle\,\sigma''`
("first behaves according to $`S`, then according to $`R`, with the final state
from $`S` serving as initial state for $`R`"); and refinement $`P \Leftarrow S`,
$`\forall\sigma, \sigma'\cdot P \Leftarrow S`. A state is an assignment of values to
state variables, `State Var Val := Var → Val`, and the assignment
$`x := e = (\sigma' = \sigma \triangleleft \mathit{address}\ \text{“x”} \triangleright e) = (x' = e \land y' = y \land \ldots)`
is the poststate obtained by updating the prestate at $`x` — literally the
book's list-modification reading, cf. {uses "list_packaging"}[]. Extends
{uses "program_as_predicate"}[].
:::

:::definition "assignment_spec" (parent := "program_theory_core") (lean := "LaPToP.ProgramTheory.Spec.assign, LaPToP.ProgramTheory.Spec.assign_iff, LaPToP.ProgramTheory.Spec.implementable_assign")
The assignment $`x := e` relates pre-state and post-state by setting $`x` to
the value of $`e` in the pre-state and leaving other variables unchanged.
This is the atomic building block for {uses "program_as_predicate"}[]; in Lean
it is `Spec.assign x e`, with `assign_iff` giving the
$`x' = e \land y' = y \land \ldots` form. Defined in {uses "specification_notations"}[].
:::

:::theorem "specification_implementability" (parent := "program_theory_core") (tags := "programs, hehner-4.0") (effort := "small") (lean := "LaPToP.ProgramTheory.Spec.implementable_ok, LaPToP.ProgramTheory.Spec.implementable_top, LaPToP.ProgramTheory.Spec.not_implementable_bot, LaPToP.ProgramTheory.Spec.implementable_assign, LaPToP.ProgramTheory.Spec.implementable_or, LaPToP.ProgramTheory.Spec.implementable_cond, LaPToP.ProgramTheory.Spec.implementable_seq, LaPToP.ProgramTheory.Spec.not_implementable_and_not")
$`\mathit{ok}`, $`\top` and $`x := e` are implementable; $`\bot` is not (on a
nonempty state space). "The $`\lor` and $`\mathbf{if}\ \mathbf{then}\ \mathbf{else}`
operators have the nice property that if their operands are implementable, so is
the result; the operators $`\land` and $`\neg` do not have that property" —
$`\lor`, $`\mathbf{if}` and $`S.\ R` preserve implementability, and
$`\mathit{ok} \land \neg\mathit{ok}` is a counterexample for $`\land`, $`\neg`.
Uses {uses "specification_notations"}[].
:::

:::theorem "skip_refines_true" (parent := "program_theory_core") (tags := "programs, refinement") (effort := "small") (priority := "high") (lean := "LaPToP.ProgramTheory.Spec.top_refines_ok")
The trivial program that leaves the state unchanged (*ok* / `skip`) implements
the always-true specification. In propositional form this is the reflexivity
seed for refinement of {uses "program_as_predicate"}[].
:::

:::proof "skip_refines_true"
Immediate: the identity relation implies $`\top`.
:::

```lean "skip_refines_true"
open LaPToP.ProgramTheory in
theorem skip_refines_true {σ : Type} :
    Spec.Refines (Spec.top : Spec σ) Spec.ok :=
  Spec.top_refines _
```

:::definition "sequential_composition" (parent := "program_theory_core") (lean := "LaPToP.ProgramTheory.Spec.seq, LaPToP.ProgramTheory.Spec.implementable_seq")
Sequential composition $`P ; Q` exists when there is an intermediate state
accepted as final by $`P` and initial by $`Q`. It builds programs from
{uses "assignment_spec"}[] and larger blocks while preserving
{uses "program_as_predicate"}[]. Hehner writes it $`P.\ Q` ("dot"); in Lean it is
`Spec.seq P Q`, defined in {uses "specification_notations"}[].
:::

:::theorem "specification_laws" (parent := "program_theory_core") (tags := "programs, laws, hehner-4.0.1") (effort := "small") (lean := "LaPToP.ProgramTheory.Spec.ok_seq, LaPToP.ProgramTheory.Spec.seq_ok, LaPToP.ProgramTheory.Spec.seq_assoc, LaPToP.ProgramTheory.Spec.cond_self, LaPToP.ProgramTheory.Spec.cond_not, LaPToP.ProgramTheory.Spec.case_creation, LaPToP.ProgramTheory.Spec.cond_eq_or, LaPToP.ProgramTheory.Spec.cond_eq_and, LaPToP.ProgramTheory.Spec.cond_pos, LaPToP.ProgramTheory.Spec.cond_neg, LaPToP.ProgramTheory.Spec.or_seq_or, LaPToP.ProgramTheory.Spec.cond_op, LaPToP.ProgramTheory.Spec.cond_and, LaPToP.ProgramTheory.Spec.cond_seq, LaPToP.ProgramTheory.Spec.assign_ite")
The Specification Laws of Section 4.0.1, for specifications $`P, Q, R, S` and
binary $`b` of the prestate:
$`\mathit{ok}.\ P = P = P.\ \mathit{ok}` (Identity), $`P.\ (Q.\ R) = (P.\ Q).\ R` (Associative),
$`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ P = P` (Idempotent),
$`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ Q = \mathbf{if}\ \neg b\ \mathbf{then}\ Q\ \mathbf{else}\ P` (Case Reversal),
$`P = \mathbf{if}\ b\ \mathbf{then}\ b \Rightarrow P\ \mathbf{else}\ \neg b \Rightarrow P` (Case Creation),
$`\mathbf{if}\ b\ \mathbf{then}\ S\ \mathbf{else}\ R = b \land S \lor \neg b \land R = (b \Rightarrow S) \land (\neg b \Rightarrow R)` (Case Analysis),
$`P \lor Q.\ R \lor S = (P.\ R) \lor (P.\ S) \lor (Q.\ R) \lor (Q.\ S)` (Distributive),
$`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ Q \land R = \mathbf{if}\ b\ \mathbf{then}\ P \land R\ \mathbf{else}\ Q \land R`
(Distributive — "we can replace $`\land` with any other binary operator", stated
once for an arbitrary operator),
$`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ Q.\ R = \mathbf{if}\ b\ \mathbf{then}\ P.\ R\ \mathbf{else}\ Q.\ R`
(Distributive, $`b` unprimed), and
$`x := \mathbf{if}\ b\ \mathbf{then}\ e\ \mathbf{else}\ f = \mathbf{if}\ b\ \mathbf{then}\ x := e\ \mathbf{else}\ x := f`
(Functional-Imperative). Uses {uses "specification_notations"}[],
{uses "sequential_composition"}[] and {uses "binary_laws_case"}[].
:::

:::proof "specification_laws"
Extensionality over prestate and poststate, then propositional reasoning; the
laws about $`\mathbf{if}` split on whether the prestate satisfies $`b`.
:::

:::theorem "substitution_law" (parent := "program_theory_core") (tags := "programs, laws, hehner-4.0.1") (effort := "small") (lean := "LaPToP.ProgramTheory.Spec.assign_seq, LaPToP.ProgramTheory.Examples.assign_x_add_y, LaPToP.ProgramTheory.Examples.assign_three_seq, LaPToP.ProgramTheory.Examples.seq_step_step")
The Substitution Law: for $`e` an expression of the prestate,
$`x := e.\ P = \langle x \cdot P\rangle\,e = (\text{substitute } e \text{ for } x \text{ in } P)`
— "an assignment followed by any specification is the same as the specification
but with the assigned variable replaced by the assigned expression". In the
state-function model this is $`P` evaluated at the updated prestate. The book's
worked calculations $`x := x + y = (x' = x + y \land y' = y)`,
$`x := 3.\ y := x + y = (x' = 3 \land y' = 3 + y)`, and
$`(x' = x \lor x' = x+1).\ (x' = x \lor x' = x+1) = (x' = x \lor x' = x+1 \lor x' = x+2)`
are checked. Uses {uses "assignment_spec"}[] and {uses "sequential_composition"}[].
:::

:::proof "substitution_law"
Unfold sequential composition: the intermediate state is forced to be the
updated prestate.
:::

:::theorem "refinement_laws" (parent := "program_theory_core") (tags := "programs, refinement, hehner-4.0.2") (effort := "small") (lean := "LaPToP.ProgramTheory.Spec.refines_refl, LaPToP.ProgramTheory.Spec.refines_trans, LaPToP.ProgramTheory.Spec.refines_antisymm, LaPToP.ProgramTheory.Spec.top_refines, LaPToP.ProgramTheory.Spec.refines_bot, LaPToP.ProgramTheory.Spec.top_refines_ok, LaPToP.ProgramTheory.Spec.implementable_of_refines, LaPToP.ProgramTheory.Spec.refines_iff")
Refinement $`P \Leftarrow S` is reflexive and transitive; "two specifications
$`P` and $`Q` are equal if and only if each is satisfied whenever the other is"
(mutual refinement is equality); $`\top \Leftarrow S` for every $`S` and
$`S \Leftarrow \bot` for every $`S`; and "weaker specifications are easier to
implement": if $`P \Leftarrow S` and $`S` is implementable then so is $`P`.
Uses {uses "program_as_predicate"}[] and {uses "skip_refines_true"}[].
:::

:::theorem "refinement_examples" (parent := "program_theory_core") (tags := "programs, refinement, hehner-4.0") (effort := "small") (lean := "LaPToP.ProgramTheory.Examples.V, LaPToP.ProgramTheory.Examples.St, LaPToP.ProgramTheory.Examples.incr, LaPToP.ProgramTheory.Examples.implementable_incr, LaPToP.ProgramTheory.Examples.deterministic_incr, LaPToP.ProgramTheory.Examples.gt, LaPToP.ProgramTheory.Examples.implementable_gt, LaPToP.ProgramTheory.Examples.nondeterministic_gt, LaPToP.ProgramTheory.Examples.not_implementable_nonneg_and, LaPToP.ProgramTheory.Examples.implementable_nonneg_imp, LaPToP.ProgramTheory.Examples.refine₁, LaPToP.ProgramTheory.Examples.refine₂, LaPToP.ProgramTheory.Examples.refine₃, LaPToP.ProgramTheory.Examples.refine₄")
The book's running example in two integer state variables $`x, y`:
$`x' = x+1 \land y' = y` is implementable and deterministic for each prestate;
$`x' > x` is implementable and nondeterministic for each prestate;
$`x \ge 0 \land y' = 0` is not implementable while $`x \ge 0 \Rightarrow y' = 0` is;
and the four refinements
$`x' > x \Leftarrow x' = x+1 \land y' = y`,
$`x' = x+1 \land y' = y \Leftarrow x := x+1`,
$`x' \le x \Leftarrow \mathbf{if}\ x = 0\ \mathbf{then}\ x' = x\ \mathbf{else}\ x' < x`,
$`x' > y' > x \Leftarrow y := x+1.\ x := y+1`.
Uses {uses "refinement_laws"}[], {uses "substitution_law"}[] and
{uses "specification_implementability"}[].
:::

:::proof "refinement_examples"
Unfold and decide by linear integer arithmetic; the counterexample for
$`x \ge 0 \land y' = 0` is the prestate with $`x = -1`.
:::
