import Verso
import VersoManual
import VersoBlueprint
import LaPToP.ProgramTheory.Specifications
import LaPToP.ProgramTheory.Programs
import LaPToP.ProgramTheory.Time
import LaPToP.ProgramTheory.Space
import LaPToP.ProgramTheory.Search
import LaPToP.ProgramTheory.FastExp
import LaPToP.ProgramTheory.Fibonacci
import LaPToP.ProgramTheory.OldTheory
import LaPToP.ProgramTheory.AssertionLaws

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Program Theory" =>

:::group "program_theory_core"
Programs as predicates on pre- and post-states; refinement as implication;
sequential composition, conditionals, and assignment in Hehner's theory.
Sections 4.0–4.4 of the book are formalized in the Lean modules
`LaPToP.ProgramTheory.Specifications`, `LaPToP.ProgramTheory.Programs`,
`LaPToP.ProgramTheory.Time` (Section 4.2) and `LaPToP.ProgramTheory.Space`
(Section 4.3, the Towers of Hanoi); the old terminology of Section 4.4
(preconditions, postconditions, invariants, variants) in
`LaPToP.ProgramTheory.OldTheory`, and the assertion laws of the Reference
chapter (§11.3.12) in `LaPToP.ProgramTheory.AssertionLaws`.

Section 4.2.3 (Soundness and Completeness) is not formalized. It makes two
meta-statements about the theory: soundness — if P is implementable and the
refinement of P by something possibly involving recursive calls to P is
proved, then "observations of the corresponding computation(s) (at finite
times) will not contradict P" — and a weak completeness: when such a
refinement is true of the observations but unprovable, "there is another
implementable specification Q such that the refinements P ⇐ Q and Q ⇐ (the
same thing with Q for P) are both provable", together with the remark that
"there cannot be a theory of programming that is both sound and complete in
the stronger sense". Observations of computations are outside the object
theory formalized here; the recursive refinements of Section 4.2 are given
their meaning in Chapter 6 (least fixed points, in the Recursion and
Concurrency chapter).
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

:::definition "program_definition" (parent := "program_theory_core") (lean := "LaPToP.ProgramTheory.Spec.IsProgram, LaPToP.ProgramTheory.Spec.IsProgram.implementable, LaPToP.ProgramTheory.Spec.IsProgram.refine', LaPToP.ProgramTheory.Spec.IsProgram.top")
"A program is a specification of computer behavior; ... a program is an
implemented specification, that is, a specification for which an implementation
has been provided, so that a computer can execute it." The programming notations
of Chapter 4: (a) $`\mathit{ok}` is a program; (b) $`x := e` is a program for an
implemented expression $`e` of the initial values; (c) $`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ Q`
is a program for implemented $`b` and programs $`P, Q`; (d) $`P.\ Q` is a program
for programs $`P, Q`; (e) an implementable specification that is refined by a
program is a program. In Lean, `Spec.IsProgram` is the inductive predicate with
exactly these five rules; every program is implementable. Two notes: the
"implemented expression" restriction on $`e` and $`b` is about the expression
language and has no counterpart in this semantic model; and the implementability
hypothesis of rule (e) is redundant, since a specification refined by an
implementable one is implementable. Uses {uses "specification_notations"}[] and
{uses "specification_implementability"}[].
:::

:::theorem "refinement_by_steps_parts_cases" (parent := "program_theory_core") (tags := "programs, refinement, hehner-4.1.0") (effort := "small") (lean := "LaPToP.ProgramTheory.Spec.refines_cond_mono, LaPToP.ProgramTheory.Spec.refines_seq_mono, LaPToP.ProgramTheory.Spec.refines_and_mono, LaPToP.ProgramTheory.Spec.steps_cond, LaPToP.ProgramTheory.Spec.steps_seq, LaPToP.ProgramTheory.Spec.steps_trans, LaPToP.ProgramTheory.Spec.cond_and_cond_refines, LaPToP.ProgramTheory.Spec.parts_cond, LaPToP.ProgramTheory.Spec.seq_and_seq_refines, LaPToP.ProgramTheory.Spec.parts_seq, LaPToP.ProgramTheory.Spec.parts_and, LaPToP.ProgramTheory.Spec.refines_cond_iff, LaPToP.ProgramTheory.Examples.refine₃_by_cases")
The Refinement Laws of Section 4.1.0. *Refinement by Steps* (monotonicity,
transitivity): if $`A \Leftarrow \mathbf{if}\ b\ \mathbf{then}\ C\ \mathbf{else}\ D`, $`C \Leftarrow E`
and $`D \Leftarrow F` then $`A \Leftarrow \mathbf{if}\ b\ \mathbf{then}\ E\ \mathbf{else}\ F`; if
$`A \Leftarrow B.\ C`, $`B \Leftarrow D`, $`C \Leftarrow E` then $`A \Leftarrow D.\ E`; if
$`A \Leftarrow B`, $`B \Leftarrow C` then $`A \Leftarrow C`. *Refinement by Parts*
(monotonicity, conflation): if $`A \Leftarrow \mathbf{if}\ b\ \mathbf{then}\ C\ \mathbf{else}\ D` and
$`E \Leftarrow \mathbf{if}\ b\ \mathbf{then}\ F\ \mathbf{else}\ G` then
$`A \land E \Leftarrow \mathbf{if}\ b\ \mathbf{then}\ C \land F\ \mathbf{else}\ D \land G`; if
$`A \Leftarrow B.\ C` and $`D \Leftarrow E.\ F` then $`A \land D \Leftarrow (B \land E).\ (C \land F)`;
if $`A \Leftarrow B` and $`C \Leftarrow D` then $`A \land C \Leftarrow B \land D`.
*Refinement by Cases*: $`P \Leftarrow \mathbf{if}\ b\ \mathbf{then}\ Q\ \mathbf{else}\ R` is a theorem
if and only if $`P \Leftarrow b \land Q` and $`P \Leftarrow \neg b \land R` are theorems —
illustrated on $`x' \le x \Leftarrow \mathbf{if}\ x = 0\ \mathbf{then}\ x' = x\ \mathbf{else}\ x' < x`.
The laws rest on monotonicity of $`\mathbf{if}`, $`.` and $`\land` with respect to
refinement. Uses {uses "refinement_laws"}[] and {uses "specification_laws"}[].
:::

:::proof "refinement_by_steps_parts_cases"
Monotonicity by unfolding; Steps is monotonicity followed by transitivity;
Parts additionally uses that $`\mathbf{if}\ b\ \mathbf{then}\ C \land F\ \mathbf{else}\ D \land G`
refines $`(\mathbf{if}\ b\ \mathbf{then}\ C\ \mathbf{else}\ D) \land (\mathbf{if}\ b\ \mathbf{then}\ F\ \mathbf{else}\ G)`
and that $`(B \land E).\ (C \land F)` refines $`(B.\ C) \land (E.\ F)`; Cases by splitting
the disjunction in $`\mathbf{if}`.
:::

:::theorem "list_summation" (parent := "program_theory_core") (tags := "programs, development, hehner-4.1.1") (effort := "medium") (lean := "LaPToP.ProgramTheory.ListSummation.SV, LaPToP.ProgramTheory.ListSummation.St, LaPToP.ProgramTheory.ListSummation.len, LaPToP.ProgramTheory.ListSummation.sumFrom, LaPToP.ProgramTheory.ListSummation.sumFrom_zero, LaPToP.ProgramTheory.ListSummation.sumFrom_len, LaPToP.ProgramTheory.ListSummation.sumFrom_succ, LaPToP.ProgramTheory.ListSummation.A, LaPToP.ProgramTheory.ListSummation.B, LaPToP.ProgramTheory.ListSummation.C, LaPToP.ProgramTheory.ListSummation.D, LaPToP.ProgramTheory.ListSummation.refine_A, LaPToP.ProgramTheory.ListSummation.refine_B, LaPToP.ProgramTheory.ListSummation.refine_C, LaPToP.ProgramTheory.ListSummation.refine_D, LaPToP.ProgramTheory.ListSummation.refine_B_expanded, LaPToP.ProgramTheory.ListSummation.refine_A_expanded, LaPToP.ProgramTheory.ListSummation.implementable_A, LaPToP.ProgramTheory.ListSummation.implementable_B")
The book's first program development (Exercise 174): "write a program to find
the sum of a list of numbers". With $`L` the list (a state constant), $`s` the
accumulator and $`n` the number of items summed, the problem $`s' = \Sigma L`
is refined in four steps:
$`s' = \Sigma L \Leftarrow s := 0.\ n := 0.\ B` where
$`B = (s' = s + \Sigma L[n;..\# L])`;
$`B \Leftarrow \mathbf{if}\ n = \# L\ \mathbf{then}\ C\ \mathbf{else}\ D` (Case Creation) with
$`C = (n = \# L \Rightarrow B)`, $`D = (n \neq \# L \Rightarrow B)`;
$`C \Leftarrow \mathit{ok}`; and
$`D \Leftarrow s := s + L\,n.\ n := n + 1.\ B`, "proved by two applications of the
Substitution Law". Refinement by Steps then assembles the compiler's view
$`B \Leftarrow \mathbf{if}\ n = \# L\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ (s := s + L\,n.\ n := n + 1.\ B)`
and the whole development. The book's implicit bound $`0 \le n \le \# L` ("the
notation $`n;..\# L` is defined only for $`n \le \# L`") is made explicit in $`B`,
as the book itself suggests. The last refinement refers to $`B` again — a
recursive call, which is not a program in the sense of {uses "program_definition"}[]
until execution time and termination (Section 4.2) and recursion (Chapter 6) are
treated; $`A` and $`B` are shown implementable so that rule (e) applies once they
are. Uses {uses "refinement_by_steps_parts_cases"}[], {uses "substitution_law"}[],
{uses "list_as_function"}[] and {uses "quantifier_numeric"}[].
:::

:::proof "list_summation"
Each step by the Substitution Law (`assign_seq`) and the list facts
$`\Sigma L[0;..\# L] = \Sigma L`, $`\Sigma L[\# L;..\# L] = 0`, and
$`\Sigma L[n;..\# L] = L\,n + \Sigma L[n+1;..\# L]` for $`0 \le n < \# L`.
:::

:::definition "time_variable" (parent := "program_theory_core") (lean := "LaPToP.ProgramTheory.Time.TSt, LaPToP.ProgramTheory.Time.assignX, LaPToP.ProgramTheory.Time.assignT, LaPToP.ProgramTheory.Time.tick, LaPToP.ProgramTheory.Time.assignX_seq, LaPToP.ProgramTheory.Time.assignT_seq, LaPToP.ProgramTheory.Time.tick_seq, LaPToP.ProgramTheory.Time.ImplementableT, LaPToP.ProgramTheory.Time.implementableT_iff, LaPToP.ProgramTheory.Time.ImplementableT.implementable, LaPToP.ProgramTheory.Time.implementableT_ok, LaPToP.ProgramTheory.Time.implementableT_assignX, LaPToP.ProgramTheory.Time.implementableT_tick, LaPToP.ProgramTheory.Time.implementableT_cond, LaPToP.ProgramTheory.Time.implementableT_seq")
"To talk about time, we just add a time variable. We do not change the theory;
the time variable is treated just like any other variable, as part of the
state." The state $`\sigma = t; x; y; \ldots` has a time variable $`t` (initial
time) and $`t'` is the final time; "to allow for nontermination we take the
domain of time to be a number system extended with $`\infty`". In Lean the
book's example state is a structure with $`t : \mathit{xnat}` (as `ℕ∞`, cf.
{uses "bunch_named_bunches"}[]) and one integer variable $`x`; since $`t` and
$`x` have different types, assignments $`x := e` and $`t := e` are the relations
`assignX`, `assignT` (in particular `tick` is $`t := t+1`), each obeying the
Substitution Law of {uses "substitution_law"}[]. "Time cannot decrease, therefore
a specification $`S` with time is implementable if and only if
$`\forall\sigma\cdot\exists\sigma'\cdot S \land t' \ge t`": `ImplementableT`, which
holds for $`\mathit{ok}`, $`x := e`, $`t := t+1` and is preserved by $`\mathbf{if}`
and $`.`. Extends {uses "specification_notations"}[] and
{uses "specification_implementability"}[].
:::

:::theorem "recursive_time" (parent := "program_theory_core") (tags := "programs, time, hehner-4.2") (effort := "medium") (lean := "LaPToP.ProgramTheory.Time.cast_toNat_pred_add_one, LaPToP.ProgramTheory.Time.Prec, LaPToP.ProgramTheory.Time.refine_Prec, LaPToP.ProgramTheory.Time.Prec', LaPToP.ProgramTheory.Time.refine_Prec', LaPToP.ProgramTheory.Time.Preal, LaPToP.ProgramTheory.Time.refine_Preal")
The book's example $`P \Leftarrow \mathbf{if}\ x = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ x := x - 1.\ P`
with time. *Recursive time* ("each recursive call costs time 1; all else is
free"): $`P \Leftarrow \mathbf{if}\ x = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ x := x - 1.\ t := t + 1.\ P`
is a theorem for $`P = \mathbf{if}\ x \ge 0\ \mathbf{then}\ x' = 0 \land t' = t + x\ \mathbf{else}\ t' = \infty`
and for $`P = x' = 0 \land \mathbf{if}\ x \ge 0\ \mathbf{then}\ t' = t + x\ \mathbf{else}\ t' = \infty`.
*Real time*, with the $`\mathbf{if}`, the assignment and the call each taking
time 1: $`P \Leftarrow t := t+1.\ \mathbf{if}\ x = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ t := t+1.\ x := x-1.\ t := t+1.\ P`
is a theorem for $`P = \mathbf{if}\ x \ge 0\ \mathbf{then}\ x' = 0 \land t' = t + 3 \times x + 1\ \mathbf{else}\ t' = \infty`
— "when $`x` starts with a nonnegative value, execution of this program sets $`x`
to 0, and takes time $`3 \times x + 1` to do so; when $`x` starts with a negative
value, execution takes infinite time". (Both measures are taken in $`\mathit{xnat}`
here.) As in {uses "list_summation"}[], the recursive call is not yet a program
in the sense of {uses "program_definition"}[]. Uses {uses "time_variable"}[] and
{uses "refinement_by_steps_parts_cases"}[].
:::

:::proof "recursive_time"
Case split on $`x = 0`; the recursive case is the Substitution Law for
$`x := x-1` and $`t := t+1` followed by a case split on $`x - 1 \ge 0`, with the
$`\mathit{xnat}` identity $`(x-1) + 1 = x` for $`x \ge 1`.
:::

:::theorem "termination" (parent := "program_theory_core") (tags := "programs, time, hehner-4.2.2") (effort := "small") (lean := "LaPToP.ProgramTheory.Time.specA, LaPToP.ProgramTheory.Time.specB, LaPToP.ProgramTheory.Time.specC, LaPToP.ProgramTheory.Time.specD, LaPToP.ProgramTheory.Time.refine_a, LaPToP.ProgramTheory.Time.unsatisfiable_b, LaPToP.ProgramTheory.Time.not_implementableT_b, LaPToP.ProgramTheory.Time.implementableT_c, LaPToP.ProgramTheory.Time.refine_c, LaPToP.ProgramTheory.Time.implementableT_d, LaPToP.ProgramTheory.Time.refines_c_d, LaPToP.ProgramTheory.Time.not_refine_d")
"Here are four specifications, each of which says that variable $`x` has final
value 2": (a) $`x' = 2`; (b) $`x' = 2 \land t' < \infty`; (c) $`x' = 2 \land (t < \infty \Rightarrow t' < \infty)`;
(d) $`x' = 2 \land t' \le t + 1`. (a) is refined by the infinite loop
$`x' = 2 \Leftarrow t := t+1.\ x' = 2` — "an unkind refinement, but the customer has no
ground for complaint". (b) is unimplementable: "(b) $`\land\ t' \ge t` is
unsatisfiable for $`t = \infty`", so "the programmer has to reject (b)". (c) is
implementable "but surprisingly, it can be refined with exactly the same
construction as (a)": $`x' = 2 \land (t < \infty \Rightarrow t' < \infty) \Leftarrow t := t+1.\ x' = 2 \land (t < \infty \Rightarrow t' < \infty)`.
(d) is implementable, stronger than (c), and "an infinite loop is no longer
possible because $`x' = 2 \land t' \le t + 1 \Leftarrow t := t+1.\ x' = 2 \land t' \le t + 1`
is not a theorem". Uses {uses "time_variable"}[] and {uses "refinement_laws"}[].
:::

:::proof "termination"
Direct from the definitions; the non-theorem is refuted by the prestate
$`t = 0, x = 0` and poststate $`t = 2, x = 2`.
:::

:::theorem "linear_search" (parent := "program_theory_core") (tags := "programs, search, time, hehner-4.2.4") (effort := "medium") (lean := "LaPToP.ProgramTheory.LinearSearch.LS, LaPToP.ProgramTheory.LinearSearch.assignH, LaPToP.ProgramTheory.LinearSearch.tick, LaPToP.ProgramTheory.LinearSearch.assignH_seq, LaPToP.ProgramTheory.LinearSearch.tick_seq, LaPToP.ProgramTheory.LinearSearch.notIn, LaPToP.ProgramTheory.LinearSearch.P, LaPToP.ProgramTheory.LinearSearch.Q, LaPToP.ProgramTheory.LinearSearch.Q', LaPToP.ProgramTheory.LinearSearch.refine₁, LaPToP.ProgramTheory.LinearSearch.refine₂, LaPToP.ProgramTheory.LinearSearch.refine₃, LaPToP.ProgramTheory.LinearSearch.T, LaPToP.ProgramTheory.LinearSearch.TQ, LaPToP.ProgramTheory.LinearSearch.TQ', LaPToP.ProgramTheory.LinearSearch.time₁, LaPToP.ProgramTheory.LinearSearch.time₂, LaPToP.ProgramTheory.LinearSearch.time₃, LaPToP.ProgramTheory.LinearSearch.PT, LaPToP.ProgramTheory.LinearSearch.QT, LaPToP.ProgramTheory.LinearSearch.combined₁, LaPToP.ProgramTheory.LinearSearch.combined₂, LaPToP.ProgramTheory.LinearSearch.nonempty_variant, LaPToP.ProgramTheory.LinearSearch.SS, LaPToP.ProgramTheory.LinearSearch.appendX, LaPToP.ProgramTheory.LinearSearch.assignHs, LaPToP.ProgramTheory.LinearSearch.Qs, LaPToP.ProgramTheory.LinearSearch.sentinel_loop, LaPToP.ProgramTheory.LinearSearch.Ps, LaPToP.ProgramTheory.LinearSearch.sentinel_top")
"Exercise 186: Write a program to find the first occurrence of a given item in
a given list. The execution time must be linear in the length of the list. Let
the list be $`L` and the value we are looking for be $`x` (these are not state
variables). Our program will assign natural variable $`h` (for “here”) the index
of the first occurrence of $`x` in $`L` if $`x` is there. ... it will be convenient
to indicate that $`x` is not in $`L` by assigning $`h` the length of $`L`. The
specification is $`\lnot x : L\,(0,..h') \land (L\,h' = x \lor h' = \# L) \land t' \le t + \# L`. ...
$`\lnot x : L\,(0,..h') \land (L\,h' = x \lor h' = \# L) \Leftarrow h := 0.\ h \le \# L \Rightarrow \lnot x : L\,(h,..h') \land (L\,h' = x \lor h' = \# L)`
... We needed to generalize the starting index to describe the remaining
problem as the search progresses. ... To test $`L\,h = x` we need to know $`h < \# L`,
so we have to test $`h = \# L` first.
$`h \le \# L \Rightarrow \ldots \Leftarrow \mathbf{if}\ h = \# L\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ h < \# L \Rightarrow \ldots`;
$`h < \# L \Rightarrow \ldots \Leftarrow \mathbf{if}\ L\,h = x\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ h := h+1.\ h \le \# L \Rightarrow \ldots`.
Now for the timing: $`t' \le t + \# L \Leftarrow h := 0.\ h \le \# L \Rightarrow t' \le t + \# L - h`; ...
$`h < \# L \Rightarrow t' \le t + \# L - h \Leftarrow \mathbf{if}\ L\,h = x\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ h := h+1.\ t := t+1.\ h \le \# L \Rightarrow t' \le t + \# L - h`.
Refinement by Parts says that if the same refinement structure can be used for
two specifications, then it can be used for their conjunction. ... It is not
really necessary to take such small steps in programming. We could have written
the combined three-line refinement. But now, suppose we learn that the given
list $`L` is known to be nonempty. ... $`h := 0.\ h < \# L \Rightarrow \ldots` and that's all. ...
We can sometimes improve the execution time (real measure) by a technique
called the sentinel. We need list $`L` to be a variable so we can join one value
to the end of it. ... Then the search is sure to find $`x`, and we can skip the
test $`h = \# L` each iteration. The program, ignoring time, becomes
$`\lnot x : L\,(0,..h') \land (L\,h' = x \lor h' = \# L) \Leftarrow L := L;;[x].\ h := 0.\ Q`,
$`Q \Leftarrow \mathbf{if}\ L\,h = x\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ h := h+1.\ Q` where
$`Q = L\,(\# L - 1) = x \land h < \# L \Rightarrow L' = L \land \lnot x : L\,(h,..h') \land L\,h' = x`." A list is a
function with a length; the recursive calls are the specifications being
refined. Proved: the three refinements, the three timing refinements (time in
$`\mathit{xnat}` as in {uses "recursive_time"}[]), the combined version of the
conjunction (which {uses "refinement_by_steps_parts_cases"}[] justifies),
the nonempty variant, and both lines of the sentinel version (with the list a
variable). Uses {uses "bunch_interval"}[].
:::

:::theorem "binary_search" (parent := "program_theory_core") (tags := "programs, search, time, hehner-4.2.5") (effort := "medium") (lean := "LaPToP.ProgramTheory.BinarySearch.BS, LaPToP.ProgramTheory.BinarySearch.assignH, LaPToP.ProgramTheory.BinarySearch.assignI, LaPToP.ProgramTheory.BinarySearch.assignJ, LaPToP.ProgramTheory.BinarySearch.assignP, LaPToP.ProgramTheory.BinarySearch.tick, LaPToP.ProgramTheory.BinarySearch.assignH_seq, LaPToP.ProgramTheory.BinarySearch.assignI_seq, LaPToP.ProgramTheory.BinarySearch.assignJ_seq, LaPToP.ProgramTheory.BinarySearch.tick_seq, LaPToP.ProgramTheory.BinarySearch.occurs, LaPToP.ProgramTheory.BinarySearch.Sorted, LaPToP.ProgramTheory.BinarySearch.Prob, LaPToP.ProgramTheory.BinarySearch.R, LaPToP.ProgramTheory.BinarySearch.U, LaPToP.ProgramTheory.BinarySearch.V, LaPToP.ProgramTheory.BinarySearch.Mid, LaPToP.ProgramTheory.BinarySearch.refine₁, LaPToP.ProgramTheory.BinarySearch.refine₂, LaPToP.ProgramTheory.BinarySearch.occurs_right, LaPToP.ProgramTheory.BinarySearch.occurs_left, LaPToP.ProgramTheory.BinarySearch.refine₃, LaPToP.ProgramTheory.BinarySearch.refine₄, LaPToP.ProgramTheory.BinarySearch.T, LaPToP.ProgramTheory.BinarySearch.TU, LaPToP.ProgramTheory.BinarySearch.TV, LaPToP.ProgramTheory.BinarySearch.time₁, LaPToP.ProgramTheory.BinarySearch.time₂, LaPToP.ProgramTheory.BinarySearch.time₃")
"Exercise 187: Write a program to find a given item in a given nonempty sorted
list. The execution time must be logarithmic in the length of the list. The
strategy is to identify which half of the list contains the item if it occurs,
then which quarter, then which eighth, and so on. ... let's indicate whether $`x`
is present in $`L` by assigning binary variable $`p` the value $`\top` if it is and
$`\bot` if not. Ignoring time for the moment, the problem is
$`x : L\,(\Box L) = p' \Rightarrow L\,h' = x`. As the search progresses, we narrow the segment
of the list that we need to search. Let us introduce natural variables $`i` and
$`j`, and let specification $`R` describe the search within the segment $`h,..j`.
$`R = (x : L\,(h,..j) = p' \Rightarrow L\,h' = x)`. We can now solve the problem.
$`(x : L\,(\Box L) = p' \Rightarrow L\,h' = x) \Leftarrow h := 0.\ j := \# L.\ h < j \Rightarrow R`;
$`h < j \Rightarrow R \Leftarrow \mathbf{if}\ j - h = 1\ \mathbf{then}\ p := L\,h = x\ \mathbf{else}\ j - h \ge 2 \Rightarrow R`;
$`j - h \ge 2 \Rightarrow R \Leftarrow j - h \ge 2 \Rightarrow h' = h < i' < j' = j.\ \mathbf{if}\ L\,i \le x\ \mathbf{then}\ h := i\ \mathbf{else}\ j := i.\ h < j \Rightarrow R`;
$`j - h \ge 2 \Rightarrow h' = h < i' < j' = j \Leftarrow i := \mathit{div}\,(h+j)\,2`.
... For recursive execution time, put $`t := t+1` before the final, recursive call.
... $`T = t' \le t + \mathit{ceil}\,(\log(\# L))`, $`U = h < j \Rightarrow t' \le t + \mathit{ceil}\,(\log(j-h))`,
$`V = j - h \ge 2 \Rightarrow t' \le t + \mathit{ceil}\,(\log(j-h))`. ... the first case of the second
refinement is $`\ldots \Rightarrow (x = L\,h = L\,h = x \Rightarrow L\,h = x)`, Symmetry and Base and Reflexive
Laws $`= \top`. ... If $`h < i` and $`L\,i \le x` and $`L` is sorted, then
$`x : L\,(i,..j) = x : L\,(h,..j)`." Reading of $`R`: with Hehner's continuing operators, as
its proof of the $`j - h = 1` case confirms, $`R` says that $`p'` is whether $`x` occurs in
$`L\,(h,..j)` and, if it does, $`L\,h' = x`. Proved: the four correctness refinements
(the third from the sortedness of $`L`, via the two segment lemmas the book
states, for segments within the list), and the three timing refinements with
$`\mathit{ceil}\,(\log \ldots)` as `Nat.clog 2`, using the halving lemma of
{uses "findmax"}[]: $`1 + \mathit{ceil}\,(\log(\text{half})) \le \mathit{ceil}\,(\log(j-h))`. Uses
{uses "linear_search"}[] and {uses "recursive_time"}[].
:::

:::theorem "fast_exponentiation" (parent := "program_theory_core") (tags := "programs, time, hehner-4.2.6") (effort := "medium") (lean := "LaPToP.ProgramTheory.FastExp.ES, LaPToP.ProgramTheory.FastExp.assignX, LaPToP.ProgramTheory.FastExp.assignZ, LaPToP.ProgramTheory.FastExp.assignY, LaPToP.ProgramTheory.FastExp.tick, LaPToP.ProgramTheory.FastExp.assignX_seq, LaPToP.ProgramTheory.FastExp.assignZ_seq, LaPToP.ProgramTheory.FastExp.assignY_seq, LaPToP.ProgramTheory.FastExp.tick_seq, LaPToP.ProgramTheory.FastExp.guard, LaPToP.ProgramTheory.FastExp.Z, LaPToP.ProgramTheory.FastExp.P, LaPToP.ProgramTheory.FastExp.mul_self_pow_div_two, LaPToP.ProgramTheory.FastExp.simple₁, LaPToP.ProgramTheory.FastExp.simple₂, LaPToP.ProgramTheory.FastExp.simple₃, LaPToP.ProgramTheory.FastExp.fast₂, LaPToP.ProgramTheory.FastExp.fast₃, LaPToP.ProgramTheory.FastExp.fast₄, LaPToP.ProgramTheory.FastExp.fast₅, LaPToP.ProgramTheory.FastExp.fast₆, LaPToP.ProgramTheory.FastExp.T, LaPToP.ProgramTheory.FastExp.time₁, LaPToP.ProgramTheory.FastExp.time₂, LaPToP.ProgramTheory.FastExp.time₃, LaPToP.ProgramTheory.FastExp.time₄, LaPToP.ProgramTheory.FastExp.time₅, LaPToP.ProgramTheory.FastExp.time₆")
"Exercise 180: Given rational variables $`x` and $`z` and natural variable $`y`,
write a program for $`z' = x^y` that runs fast without using exponentiation. ...
The idea is to accumulate a product, using variable $`z` as accumulator. Define
$`P = z' = z \times x^y`. We can solve the problem as follows, though this solution
does not give the fastest possible computation. $`z' = x^y \Leftarrow z := 1.\ P`;
$`P \Leftarrow \mathbf{if}\ y = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ y > 0 \Rightarrow P`;
$`y > 0 \Rightarrow P \Leftarrow z := z \times x.\ y := y-1.\ P`. To speed up the computation, we
change our refinement of $`y > 0 \Rightarrow P` to test whether $`y` is even or odd; in the
odd case we make no improvement but in the even case we can cut $`y` in half.
... Before we consider time, here is the fast exponentiation program again.
$`z' = x^y \Leftarrow z := 1.\ P`;
$`P \Leftarrow \mathbf{if}\ \mathit{even}\ y\ \mathbf{then}\ \mathit{even}\ y \Rightarrow P\ \mathbf{else}\ \mathit{odd}\ y \Rightarrow P`;
$`\mathit{even}\ y \Rightarrow P \Leftarrow \mathbf{if}\ y = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ \mathit{even}\ y \land y > 0 \Rightarrow P`;
$`\mathit{odd}\ y \Rightarrow P \Leftarrow z := z \times x.\ y := y-1.\ \mathit{even}\ y \Rightarrow P`;
$`\mathit{even}\ y \land y > 0 \Rightarrow P \Leftarrow x := x \times x.\ y := y/2.\ y > 0 \Rightarrow P`;
$`y > 0 \Rightarrow P \Leftarrow \mathbf{if}\ \mathit{even}\ y\ \mathbf{then}\ \mathit{even}\ y \land y > 0 \Rightarrow P\ \mathbf{else}\ \mathit{odd}\ y \Rightarrow P`.
In the recursive time measure, every loop of calls must include a time
increment. In this program, a single time increment charged to the call
$`y > 0 \Rightarrow P` does the trick. ... it is easier to prove the less precise
specification $`T` defined as $`T = \mathbf{if}\ y = 0\ \mathbf{then}\ t' = t\ \mathbf{else}\ t' \le t + \log y`. To
do so, we need to refine $`T` with exactly the same refinement structure that we
used to refine the result $`z' = x^y` so that we can conjoin the result and
timing specifications according to Refinement by Parts. ... It does not matter
that specification $`T` is refined more than once. When we conjoin it with the
previous result specifications, we find that each specification is refined
only once." Proved, with the recursive calls as specifications and $`\log` as
the floor of the binary logarithm: the simple solution's three refinements,
the six refinements of the fast program ("each of these refinements is easily
proved"), and the six timing refinements with the same structure — the
conjunction then follows by {uses "refinement_by_steps_parts_cases"}[]. Uses
{uses "binary_search"}[] and {uses "recursive_time"}[].
:::

:::theorem "fibonacci" (parent := "program_theory_core") (tags := "programs, time, hehner-4.2.7") (effort := "small") (lean := "LaPToP.ProgramTheory.Fibonacci.FS, LaPToP.ProgramTheory.Fibonacci.assignX, LaPToP.ProgramTheory.Fibonacci.assignY, LaPToP.ProgramTheory.Fibonacci.assignN, LaPToP.ProgramTheory.Fibonacci.tick, LaPToP.ProgramTheory.Fibonacci.assignX_seq, LaPToP.ProgramTheory.Fibonacci.assignY_seq, LaPToP.ProgramTheory.Fibonacci.assignN_seq, LaPToP.ProgramTheory.Fibonacci.tick_seq, LaPToP.ProgramTheory.Fibonacci.Goal, LaPToP.ProgramTheory.Fibonacci.P, LaPToP.ProgramTheory.Fibonacci.Shift, LaPToP.ProgramTheory.Fibonacci.goal_refines, LaPToP.ProgramTheory.Fibonacci.P_refines, LaPToP.ProgramTheory.Fibonacci.shift_refines, LaPToP.ProgramTheory.Fibonacci.TL, LaPToP.ProgramTheory.Fibonacci.TS, LaPToP.ProgramTheory.Fibonacci.time_refines, LaPToP.ProgramTheory.Fibonacci.shift_time, LaPToP.ProgramTheory.Fibonacci.fib_odd, LaPToP.ProgramTheory.Fibonacci.fib_even, LaPToP.ProgramTheory.Fibonacci.guard, LaPToP.ProgramTheory.Fibonacci.Sq₁, LaPToP.ProgramTheory.Fibonacci.Sq₂, LaPToP.ProgramTheory.Fibonacci.P_log, LaPToP.ProgramTheory.Fibonacci.odd_refines, LaPToP.ProgramTheory.Fibonacci.even_refines, LaPToP.ProgramTheory.Fibonacci.sq₁_refines, LaPToP.ProgramTheory.Fibonacci.sq₂_refines, LaPToP.ProgramTheory.Fibonacci.TLog, LaPToP.ProgramTheory.Fibonacci.tlog₁, LaPToP.ProgramTheory.Fibonacci.tlog_odd, LaPToP.ProgramTheory.Fibonacci.tlog_even, LaPToP.ProgramTheory.Fibonacci.sq₁_time, LaPToP.ProgramTheory.Fibonacci.sq₂_time")
"In this subsection, we tackle Exercise 256. The definition of the Fibonacci
numbers $`\mathit{fib}\ 0 = 0`, $`\mathit{fib}\ 1 = 1`, $`\mathit{fib}\ (n+2) = \mathit{fib}\ n + \mathit{fib}\ (n+1)` immediately
suggests a recursive function definition ... We did not include functions in
our programming language, so we still have some work to do. Also, the
functional solution we have just given has exponential execution time, and we
can do much better. For $`n \ge 2`, we can find a Fibonacci number if we know the
previous pair of Fibonacci numbers. That suggests we keep track of a pair of
numbers. Let $`x`, $`y`, and $`n` be natural variables. We refine $`x' = \mathit{fib}\ n \Leftarrow P`
where $`P` is the problem of finding a pair of Fibonacci numbers.
$`P = x' = \mathit{fib}\ n \land y' = \mathit{fib}\ (n+1)`. When $`n = 0`, the solution is easy. When $`n \ge 1`,
we can decrease it by $`1`, find a pair of Fibonacci numbers at that previous
argument, and then move $`x` and $`y` along one place.
$`P \Leftarrow \mathbf{if}\ n = 0\ \mathbf{then}\ x := 0.\ y := 1\ \mathbf{else}\ n := n-1.\ P.\ x' = y \land y' = x+y`.
To move $`x` and $`y` along we need another variable. We could use a new variable,
but we already have $`n`; is it safe to use $`n` for this purpose? The
specification $`x' = y \land y' = x+y` allows $`n` to change, so we can use it if we want.
$`x' = y \land y' = x+y \Leftarrow n := x.\ x := y.\ y := n+y`. The time for this solution is
linear. To prove it, we keep the same refinement structure, but we replace the
specifications with new ones concerning time. We replace $`P` by $`t' = t+n` and
add $`t := t+1` in front of its use; we also change $`x' = y \land y' = x+y` into $`t' = t`.
$`t' = t+n \Leftarrow \mathbf{if}\ n = 0\ \mathbf{then}\ x := 0.\ y := 1\ \mathbf{else}\ n := n-1.\ t := t+1.\ t' = t+n.\ t' = t`;
$`t' = t \Leftarrow n := x.\ x := y.\ y := n+y`. Linear time is a lot better than exponential
time, but we can do even better. Exercise 256 asks for a solution with
logarithmic time. To get it, we need to take the hint offered in the exercise
and use the equations $`\mathit{fib}(2 \times k + 1) = (\mathit{fib}\ k)^2 + (\mathit{fib}(k+1))^2`,
$`\mathit{fib}(2 \times k + 2) = 2 \times \mathit{fib}\ k \times \mathit{fib}(k+1) + (\mathit{fib}(k+1))^2`. ...
$`P \Leftarrow \mathbf{if}\ n = 0\ \mathbf{then}\ x := 0.\ y := 1\ \mathbf{else\ if}\ \mathit{even}\ n\ \mathbf{then}\ \mathit{even}\ n \land n > 0 \Rightarrow P\ \mathbf{else}\ \mathit{odd}\ n \Rightarrow P`;
$`\mathit{odd}\ n \Rightarrow P \Leftarrow n := (n-1)/2.\ P.\ x' = x^2 + y^2 \land y' = 2 \times x \times y + y^2`;
... we can get $`\mathit{fib}(2 \times k + 3)` as the sum of $`\mathit{fib}(2 \times k + 1)` and
$`\mathit{fib}(2 \times k + 2)`.
$`\mathit{even}\ n \land n > 0 \Rightarrow P \Leftarrow n := n/2 - 1.\ P.\ x' = 2 \times x \times y + y^2 \land y' = x^2 + y^2 + x'`.
The remaining two problems ... require another variable as before, and as
before, we can use $`n`. $`x' = x^2 + y^2 \land y' = 2 \times x \times y + y^2 \Leftarrow n := x.\ x := x^2 + y^2.\ y := 2 \times n \times y + y^2`;
$`x' = 2 \times x \times y + y^2 \land y' = x^2 + y^2 + x' \Leftarrow n := x.\ x := 2 \times x \times y + y^2.\ y := n^2 + y^2 + x`.
To prove that this program is now logarithmic time, we define time
specification $`T = t' \le t + \log(n+1)` and we put $`t := t+1` before calls to $`T`.
... $`\mathit{odd}\ n \Rightarrow 1 + \log((n-1)/2 + 1) \le \log(n+1)` (logarithm law)
$`= \mathit{odd}\ n \Rightarrow \log(n-1+2) \le \log(n+1) = \top`; ... $`\mathit{even}\ n \land n > 0 \Rightarrow \log n \le \log(n+1) = \top`."
Both solutions and their timings are proved with Mathlib's $`\mathit{fib}` and the
recursive call as a specification; the doubling identities are Mathlib's,
restated in the book's form, and $`\log` is the floor of the binary logarithm,
for which the book's logarithm-law steps hold exactly. Uses
{uses "fast_exponentiation"}[], {uses "recursive_time"}[] and
{uses "nat_induction_predicate"}[].
:::

:::theorem "space" (parent := "program_theory_core") (tags := "programs, space, time, hehner-4.3") (effort := "medium") (lean := "LaPToP.ProgramTheory.Hanoi.HS, LaPToP.ProgramTheory.Hanoi.assignN, LaPToP.ProgramTheory.Hanoi.tick, LaPToP.ProgramTheory.Hanoi.assignS, LaPToP.ProgramTheory.Hanoi.assignM, LaPToP.ProgramTheory.Hanoi.assignN_seq, LaPToP.ProgramTheory.Hanoi.tick_seq, LaPToP.ProgramTheory.Hanoi.assignS_seq, LaPToP.ProgramTheory.Hanoi.assignM_seq, LaPToP.ProgramTheory.Hanoi.enat_add_one_sub_one, LaPToP.ProgramTheory.Hanoi.movePile, LaPToP.ProgramTheory.Hanoi.movePile_n, LaPToP.ProgramTheory.Hanoi.T, LaPToP.ProgramTheory.Hanoi.two_pow_succ_sub_one, LaPToP.ProgramTheory.Hanoi.time_refines, LaPToP.ProgramTheory.Hanoi.S, LaPToP.ProgramTheory.Hanoi.movePileSpace, LaPToP.ProgramTheory.Hanoi.space_refines, LaPToP.ProgramTheory.Hanoi.MS, LaPToP.ProgramTheory.Hanoi.MS_m_le, LaPToP.ProgramTheory.Hanoi.longLine, LaPToP.ProgramTheory.Hanoi.longLineSpec, LaPToP.ProgramTheory.Hanoi.longLine_refines, LaPToP.ProgramTheory.Hanoi.movePileMax, LaPToP.ProgramTheory.Hanoi.max_case_refines, LaPToP.ProgramTheory.Hanoi.maxSpace_refines, LaPToP.ProgramTheory.Hanoi.AS, LaPToP.ProgramTheory.Hanoi.Avg.assignN, LaPToP.ProgramTheory.Hanoi.Avg.assignS, LaPToP.ProgramTheory.Hanoi.Avg.assignP, LaPToP.ProgramTheory.Hanoi.Avg.assignN_seq, LaPToP.ProgramTheory.Hanoi.Avg.assignS_seq, LaPToP.ProgramTheory.Hanoi.Avg.assignP_seq, LaPToP.ProgramTheory.Hanoi.Avg.incr, LaPToP.ProgramTheory.Hanoi.Avg.Pavg, LaPToP.ProgramTheory.Hanoi.Avg.avg_refines, LaPToP.ProgramTheory.Hanoi.Avg.average_space, LaPToP.ProgramTheory.Hanoi.FS, LaPToP.ProgramTheory.Hanoi.Full.assignN, LaPToP.ProgramTheory.Hanoi.Full.assignS, LaPToP.ProgramTheory.Hanoi.Full.assignM, LaPToP.ProgramTheory.Hanoi.Full.tick, LaPToP.ProgramTheory.Hanoi.Full.addP, LaPToP.ProgramTheory.Hanoi.Full.assignN_seq, LaPToP.ProgramTheory.Hanoi.Full.assignS_seq, LaPToP.ProgramTheory.Hanoi.Full.assignM_seq, LaPToP.ProgramTheory.Hanoi.Full.tick_seq, LaPToP.ProgramTheory.Hanoi.Full.addP_seq, LaPToP.ProgramTheory.Hanoi.Full.MovePile, LaPToP.ProgramTheory.Hanoi.Full.body, LaPToP.ProgramTheory.Hanoi.Full.movePile_refines")
"Our example to illustrate space calculation is Exercise 293: the Towers of
Hanoi. ... Our solution is $`\mathit{MovePile}\ \text{“A”}\ \text{“B”}\ \text{“C”}` where we refine
$`\mathit{MovePile}` as follows.
$`\mathit{MovePile}\ \mathit{from}\ \mathit{to}\ \mathit{using} \Leftarrow \mathbf{if}\ n = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ n := n-1.\ \mathit{MovePile}\ \mathit{from}\ \mathit{using}\ \mathit{to}.\ \mathit{MoveDisk}\ \mathit{from}\ \mathit{to}.\ \mathit{MovePile}\ \mathit{using}\ \mathit{to}\ \mathit{from}.\ n := n+1`
... Our concern is just the time and space requirements, so we will ignore
the disk positions and the parameters $`\mathit{from}`, $`\mathit{to}`, and $`\mathit{using}`. All we
can prove at the moment is that if $`\mathit{MoveDisk}` satisfies $`n' = n`, so does
$`\mathit{MovePile}`. To measure time, we add a time variable $`t`, and use it to count
disk moves. We suppose that $`\mathit{MoveDisk}` takes time $`1` ... so we replace it by
$`t := t+1`. We now prove that the execution time is $`2^n - 1` by replacing
$`\mathit{MovePile}` with the specification $`t := t + 2^n - 1`. We prove
$`t := t + 2^n - 1 \Leftarrow \mathbf{if}\ n = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ n := n-1.\ t := t + 2^n - 1.\ t := t+1.\ t := t + 2^n - 1.\ n := n+1`
by cases. ... To talk about the memory space used by a computation, we just
add a space variable $`s`. Like the time variable $`t`, $`s` is not part of the
implementation, but only used in specifying and calculating space
requirements. ... To allow for the possibility that execution endlessly
consumes space, we take the domain of space to be the natural numbers extended
with $`\infty`. Wherever space is being increased, we insert $`s := s + (\text{the increase})`
... In our example, the recursive calls are not the last action in the
refinement; they require that a return address be pushed onto a stack at the
start of the call, and popped off at the end. Considering only space, ignoring
time and disk movements, we can prove
$`s' = s \Leftarrow \mathbf{if}\ n = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ n := n-1.\ s := s+1.\ s' = s.\ s := s-1.\ \mathit{ok}.\ s := s+1.\ s' = s.\ s := s-1.\ n := n+1`
which says that the space occupied is the same at the end as at the start."
Maximum space (Subsection 4.3.0): "Let $`m` be the maximum space occupied before
the start of execution ..., and $`m'` be the maximum space occupied by the end
of execution. Implementability requires $`m' \ge m`. Wherever space is being
increased, we insert $`m := m \uparrow s` to keep $`m` current. In our example, we want
to prove that the maximum space occupied is $`n`. However, in a larger context,
it may happen that the starting space $`s` is not $`0`, so we specify $`m' = s+n`.
At the start, $`s \le m`, since $`m` is the maximum value of $`s`. We assume $`m \le s+n`
so that $`m` does not start larger than the maximum we are trying to prove. The
refinement becomes
$`s \le m \le s+n \Rightarrow (m := s+n) \Leftarrow \mathbf{if}\ n = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ n := n-1.\ s := s+1.\ m := m \uparrow s.\ s \le m \le s+n \Rightarrow (m := s+n).\ s := s-1.\ \mathit{ok}.\ s := s+1.\ m := m \uparrow s.\ s \le m \le s+n \Rightarrow (m := s+n).\ s := s-1.\ n := n+1`
The proof of the refinement proceeds in the usual two cases. ... Before
proving the last case, let's simplify the long line that occurs twice.
$`s := s+1.\ m := m \uparrow s.\ s \le m \le s+n \Rightarrow (m := s+n).\ s := s-1 \ldots = m \le s+1+n \Rightarrow (m := s+1+n)`."
Average space (Subsection 4.3.1): "To find the average space occupied during
a computation, we find the cumulative space-time product, and then divide by
the execution time. Let $`p` be the cumulative space-time product at the start
of execution, and $`p'` be the cumulative space-time product at the end of
execution. We still need variable $`s`, but we no longer need variables $`t` and
$`m`. An increase in $`p` occurs where there would be an increase in $`t`, and the
increase is $`s` times the increase in $`t`. In the example, where $`t` was
increased by $`1`, $`p` is increased by $`s \times 1`. We prove
$`p := p + s \times (2^n - 1) + (n-2) \times 2^n + 2 \Leftarrow \mathbf{if}\ n = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ n := n-1.\ s := s+1.\ p := p + s \times (2^n - 1) + (n-2) \times 2^n + 2.\ s := s-1.\ p := p + s \times 1.\ s := s+1.\ p := p + s \times (2^n - 1) + (n-2) \times 2^n + 2.\ s := s-1.\ n := n+1`
... The additional amount $`(n-2) \times 2^n + 2` is due to our computation. The
average space due to our computation is this additional amount divided by the
execution time. Thus the average space occupied by our computation is
$`n + n/(2^n - 1) - 2`. ... Putting together all the proofs for the Towers of
Hanoi problem, we have
$`\mathit{MovePile} \Leftarrow \mathbf{if}\ n = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ n := n-1.\ s := s+1.\ m := m \uparrow s.\ \mathit{MovePile}.\ s := s-1.\ t := t+1.\ p := p+s.\ \mathit{ok}.\ s := s+1.\ m := m \uparrow s.\ \mathit{MovePile}.\ s := s-1.\ n := n+1`
where $`\mathit{MovePile}` is the specification
$`n' = n \land t' = t + 2^n - 1 \land s' = s \land (s \le m \le s+n \Rightarrow m' = s+n) \land p' = p + s \times (2^n - 1) + (n-2) \times 2^n + 2`."
The state has $`n`, the time, the space and the maximum space (the last three
in $`\mathit{xnat}`); disk positions and tower parameters are ignored as the book does,
and the recursive calls are the specifications being refined. Proved by the
book's two cases: $`n' = n` for $`\mathit{MovePile}` when $`\mathit{MoveDisk}` satisfies it; the
time $`2^n - 1`; no space leaks, $`s' = s`; the long line refines
$`m \le s+1+n \Rightarrow (m := s+1+n)`; the maximum-space refinement, together with
"$`m' \ge m`" for the specification; the average-space refinement ("use
substitution law 10 times") on a state with integer space and product, since
$`(n-2) \times 2^n` is signed; the identity
$`(n-2) \times 2^n + 2 = (2^n - 1) \times (n + n/(2^n - 1) - 2)`; and the combined
five-conjunct $`\mathit{MovePile}` refinement, on a state with finite space and
$`\mathit{xnat}` time and maximum. Uses {uses "recursive_time"}[],
{uses "refinement_by_steps_parts_cases"}[] and {uses "substitution_law"}[].
:::

:::theorem "old_program_theory" (parent := "program_theory_core") (tags := "programs, assertions, refinement, hehner-4.4") (effort := "medium") (lean := "LaPToP.ProgramTheory.OldTheory.prePost, LaPToP.ProgramTheory.OldTheory.ok_not_prePost, LaPToP.ProgramTheory.OldTheory.ne_not_prePost, LaPToP.ProgramTheory.OldTheory.and_not_prePost, LaPToP.ProgramTheory.OldTheory.exactPre, LaPToP.ProgramTheory.OldTheory.exactPost, LaPToP.ProgramTheory.OldTheory.refines_iff_exactPre, LaPToP.ProgramTheory.OldTheory.refines_iff_exactPost, LaPToP.ProgramTheory.OldTheory.refines_weaken_pre, LaPToP.ProgramTheory.OldTheory.refines_weaken_post, LaPToP.ProgramTheory.OldTheory.SufficientPre, LaPToP.ProgramTheory.OldTheory.NecessaryPre, LaPToP.ProgramTheory.OldTheory.SufficientPost, LaPToP.ProgramTheory.OldTheory.NecessaryPost, LaPToP.ProgramTheory.OldTheory.exactPre_sufficient_necessary, LaPToP.ProgramTheory.OldTheory.exactPost_sufficient_necessary, LaPToP.ProgramTheory.OldTheory.assignX, LaPToP.ProgramTheory.OldTheory.gt5, LaPToP.ProgramTheory.OldTheory.pre4, LaPToP.ProgramTheory.OldTheory.not_refines_gt5, LaPToP.ProgramTheory.OldTheory.not_implementable_pre4, LaPToP.ProgramTheory.OldTheory.exactPre_gt5, LaPToP.ProgramTheory.OldTheory.exactPost_pre4, LaPToP.ProgramTheory.OldTheory.refines_pre4_gt5, LaPToP.ProgramTheory.OldTheory.refines_gt5_pre4, LaPToP.ProgramTheory.OldTheory.contrapositive_form, LaPToP.ProgramTheory.OldTheory.necessary_not_sufficient_pre, LaPToP.ProgramTheory.OldTheory.sufficient_not_necessary_pre, LaPToP.ProgramTheory.OldTheory.exact_pre, LaPToP.ProgramTheory.OldTheory.necessary_not_sufficient_post, LaPToP.ProgramTheory.OldTheory.sufficient_not_necessary_post, LaPToP.ProgramTheory.OldTheory.exact_post, LaPToP.ProgramTheory.OldTheory.farther, LaPToP.ProgramTheory.OldTheory.abs_sq_gt_iff, LaPToP.ProgramTheory.OldTheory.exactPre_farther, LaPToP.ProgramTheory.OldTheory.exactPost_farther, LaPToP.ProgramTheory.OldTheory.IsInvariant, LaPToP.ProgramTheory.OldTheory.isInvariant_iff₁, LaPToP.ProgramTheory.OldTheory.isInvariant_iff₂, LaPToP.ProgramTheory.OldTheory.XY, LaPToP.ProgramTheory.OldTheory.XY.assignX, LaPToP.ProgramTheory.OldTheory.XY.assignY, LaPToP.ProgramTheory.OldTheory.XY.assignX_seq, LaPToP.ProgramTheory.OldTheory.invariant_304f, LaPToP.ProgramTheory.OldTheory.IsVariant, LaPToP.ProgramTheory.OldTheory.backward_clock, LaPToP.ProgramTheory.OldTheory.timeBound, LaPToP.ProgramTheory.OldTheory.timeBound_refines")
"The original method of proving properties of a computation was to place
assertions at strategic points within a program to describe the state of the
computation at those points. ... An assertion situated at the start of a
program is called a precondition for that program; an assertion situated at
the end of a program is called a postcondition for that program. ... An
assertion situated at the start and end of a program (often a loop) is called
an invariant for that program. ... We do not present the old theory because
it is completely superseded by the theory in this book. ... If we have a
precondition $`P` and postcondition $`R` for a program, we can form a
specification $`P \Rightarrow R'` for the program. But specifications are not
necessarily implications with only unprimed variables in the antecedent and
only primed variables in the consequent, and they are not necessarily
decomposable into a precondition and postcondition. ... For examples, the
specifications $`P = R'`, $`P \neq R'`, $`(P \Rightarrow R') \land (Q \Rightarrow S')` cannot be
written as precondition-postcondition pairs. ... Let $`P` and $`S` be
specifications. The exact precondition for $`P` to be refined by $`S` is
$`\forall \sigma' \cdot P \Leftarrow S`. The exact postcondition for $`P` to be refined by $`S` is
$`\forall \sigma \cdot P \Leftarrow S`. These are the same as refinement except that the
quantification is over only one state. ... Although $`x' > 5` is not refined by
$`x := x{+}1`, we can calculate (in one integer variable) (the exact precondition
for $`x' > 5` to be refined by $`x := x{+}1`) $`= \forall x' \cdot x' > 5 \Leftarrow x' = x{+}1 = x{+}1 > 5 = x > 4`.
This means that a computation satisfying $`x := x{+}1` will also satisfy $`x' > 5`
if and only if it starts with $`x > 4`. ... we should weaken our problem
specification with that antecedent, obtaining the refinement
$`x > 4 \Rightarrow x' > 5 \Leftarrow x := x{+}1`. ... although $`x > 4` is unimplementable,
(the exact postcondition for $`x > 4` to be refined by $`x := x{+}1`)
$`= \forall x \cdot x > 4 \Leftarrow x' = x{+}1 = x' - 1 > 4 = x' > 5` ... obtaining the refinement
$`x' > 5 \Rightarrow x > 4 \Leftarrow x := x{+}1`. For easier understanding, it may help to use the
Contrapositive Law to rewrite the specification $`x' > 5 \Rightarrow x > 4` as the
equivalent specification $`x \leq 4 \Rightarrow x' \leq 5`. ... Any assertion that implies
the exact precondition is called a sufficient precondition. Any assertion
implied by the exact precondition is called a necessary precondition. Any
assertion that implies the exact postcondition is called a sufficient
postcondition. Any assertion implied by the exact postcondition is called a
necessary postcondition. The exact precondition is the necessary and
sufficient precondition, and the exact postcondition is the necessary and
sufficient postcondition. For examples, $`x > 2` is a necessary (but not
sufficient) precondition for $`x := x{+}1` to refine $`x' > 5`; $`x > 6` is a sufficient
(but not necessary) precondition ...; $`x > 4` is the exact (necessary and
sufficient) precondition ...; for $`x > 4` to be refined by $`x := x{+}1`, a necessary
(but not sufficient) postcondition is $`x' > 3`; ... a sufficient (but not
necessary) postcondition is $`x' > 7`; ... the exact (necessary and sufficient)
postcondition is $`x' > 5`. ... The old theory ... used the words “weakest
precondition” to mean “exact precondition”, and the words “strongest
postcondition” to mean “exact postcondition”. Exercise 301(c) asks for the exact
precondition and exact postcondition for $`x := x^2` to move integer variable $`x`
farther from zero. ... $`\mathit{abs}\ x' > \mathit{abs}\ x` ... (the exact precondition ...)
$`= \forall x' \cdot \mathit{abs}\ x' > \mathit{abs}\ x \Leftarrow x' = x^2 = \mathit{abs}\ (x^2) > \mathit{abs}\ x = x \neq -1 \land x \neq 0 \land x \neq 1`.
If $`x` starts anywhere but $`-1`, $`0`, or $`1`, it will move farther from zero. (the
exact postcondition ...) $`= \forall x \cdot \mathit{abs}\ x' > \mathit{abs}\ x \Leftarrow x' = x^2 = x' \neq 0 \land x' \neq 1`.
If $`x` ends anywhere but $`0` or $`1`, it did move farther from zero. Let $`S` be a
specification, let $`I` be an assertion with all nonlocal variables unprimed, and
let $`I'` be the same as $`I` but with primes on all nonlocal variables. Then $`I` is an
invariant for $`S` if $`I \Rightarrow I'` is refined by $`S`. $`\forall \sigma, \sigma' \cdot (I \Rightarrow I') \Leftarrow S`. Here
are two equivalent definitions. $`\forall \sigma, \sigma' \cdot I \land S \Rightarrow I'`,
$`\forall \sigma, \sigma' \cdot I \Rightarrow (S \Rightarrow I')`. Executing $`S` in a state where $`I` is true
creates a state in which $`I` is again true. Exercise 304(f) asks us to prove that
$`y = x^2` is an invariant for $`(x := x{+}1.\ y := y + 2 \times x - 1)` where the variables are
$`x` and $`y`. ... $`= \top`. ... In addition to the invariant associated with a loop,
the old theory had a variant (or bound function, or well-founded relation) for
the purpose of proving termination. A variant is a natural-valued expression
whose value decreases each iteration. A variant is really just a time bound,
using the recursive measure, with a clock that runs backward. It enables proof
that a computation terminates, but it does not enable proof that a computation
does not terminate. The theory in this book enables us to prove both
termination and nontermination."

Model notes. `prePost P R` is $`P \Rightarrow R'`; the three non-decomposable
specifications are instantiated in one integer variable as $`x' = x` (that is,
{uses "specification_notations"}[]'s $`ok`), $`x' \neq x` and
$`(x = 0 \Rightarrow x' = 0) \land (x = 1 \Rightarrow x' = 1)`, each shown not to be any `prePost`.
`exactPre`/`exactPost` are the two one-state quantifications, with
{uses "refinement_laws"}[]' refinement recovered by quantifying the other state
(`refines_iff_exactPre`, `refines_iff_exactPost`) and the "weaken our problem
specification" refinements proved in general (`refines_weaken_pre/post`). All
the book's computations in one integer variable are proved as equalities of
assertions (`exactPre_gt5`, `exactPost_pre4`, `exactPre_farther`,
`exactPost_farther`, with $`\mathit{abs}\ (x^2) > \mathit{abs}\ x \Leftrightarrow x \neq -1 \land x \neq 0 \land x \neq 1`
as `abs_sq_gt_iff`), together with the unrefinability of $`x' > 5` by $`x := x{+}1`, the
unimplementability of $`x > 4`, the two refinements, the Contrapositive form, and
the six sufficient/necessary examples with their counterexamples ($`x = 3`, $`x = 5`,
$`x' = 4`, $`x' = 6`). `IsInvariant` and its two equivalent forms are proved, and
Exercise 304(f) by the {uses "substitution_law"}[]. "A variant is really just a
time bound": `backward_clock` is the one-step statement $`t' + v' \leq t + v` when
$`v' < v` and $`t' = t{+}1`, and `timeBound_refines` proves, for the loop
$`L \Leftarrow \mathbf{if}\ b\ \mathbf{then}\ S.\ t := t{+}1.\ L\ \mathbf{else}\ ok` on the timed state of
{uses "recursive_time"}[], that a variant of the memory variable decreased by
$`S` gives the time bound $`t' \leq t + v` (refined by the loop body with the bound as
the recursive call). The remark that variants cannot prove nontermination, the
remaining uses of {uses "assertions"}[] and of invariants in {uses "for_loop"}[],
are prose.
:::

:::theorem "assertion_laws" (parent := "program_theory_core") (tags := "programs, assertions, laws, hehner-11.3.12") (effort := "small") (lean := "LaPToP.ProgramTheory.Spec.pre, LaPToP.ProgramTheory.Spec.post, LaPToP.ProgramTheory.Spec.pre_and_seq, LaPToP.ProgramTheory.Spec.pre_imp_seq_refines, LaPToP.ProgramTheory.Spec.seq_and_post, LaPToP.ProgramTheory.Spec.seq_post_imp_refines, LaPToP.ProgramTheory.Spec.seq_pre_and, LaPToP.ProgramTheory.Spec.seq_refines_and_post_imp, LaPToP.ProgramTheory.Spec.sufficientPre_iff, LaPToP.ProgramTheory.Spec.sufficientPost_iff, LaPToP.ProgramTheory.Spec.seq_cond_eq_or, LaPToP.ProgramTheory.Spec.det, LaPToP.ProgramTheory.Spec.det_seq, LaPToP.ProgramTheory.Spec.det_seq_cond")
The Assertions table of the Reference chapter (Section 11.3.12): "Let $`P` and
$`Q` be specifications. Let $`A` be an assertion and let $`A'` be the same as $`A` but
with primes on all the variables. $`A \land (P.\ Q) = A \land P.\ Q`;
$`A \Rightarrow (P.Q) \Leftarrow A \Rightarrow P.\ Q`; $`(P.Q) \land A' = P.\ Q \land A'`;
$`(P.Q) \Leftarrow A' \Leftarrow P.\ Q \Leftarrow A'`; $`P.\ A \land Q = P \land A'.\ Q`;
$`P.\ Q \Leftarrow P \land A'.\ A \Rightarrow Q`. $`A` is a sufficient precondition for $`P` to
be refined by $`S` if and only if $`A \Rightarrow P` is refined by $`S`. $`A` is a sufficient
postcondition for $`P` to be refined by $`S` if and only if $`A' \Rightarrow P` is refined by
$`S`." And from Section 11.3.10 the last distributivity law of
{uses "sequential_composition"}[]:
"$`P.\ \mathbf{if}\ b\ \mathbf{then}\ Q\ \mathbf{else}\ R = \mathbf{if}\ P.\ b\ \mathbf{then}\ P.\ Q\ \mathbf{else}\ P.\ R` distributivity
(unprimed $`b`)".

Model notes. An assertion is a predicate on states; `pre A` reads it on the
prestate and `post A` ($`A'`) on the poststate. The six laws are equalities and
refinements of specifications, proved by unfolding sequential composition (the
assertion on the intermediate state moves across the dot). The two "sufficient"
characterizations connect the {uses "old_program_theory"}[] definitions with
refinement ({uses "specification_laws"}[]). For the distributivity law, $`P.\ b`
with $`b` a binary expression of the intermediate state is not itself a
specification: the law is proved for deterministic $`P` (`det e`, covering the
assignments of {uses "assertions"}[]' examples), where $`P.\ b` is $`b` at the unique
intermediate state, and in general in the form
$`P.\ \mathbf{if}\ b\ \mathbf{then}\ Q\ \mathbf{else}\ R = (P \land b'.\ Q) \lor (P \land \lnot b'.\ R)`, which is
its content when the intermediate state is nondeterministic.
:::
