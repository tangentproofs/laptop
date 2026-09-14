import Verso
import VersoManual
import VersoBlueprint
import LaPToP.ProgramTheory.Specifications
import LaPToP.ProgramTheory.Programs
import LaPToP.ProgramTheory.Time

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Program Theory" =>

:::group "program_theory_core"
Programs as predicates on pre- and post-states; refinement as implication;
sequential composition, conditionals, and assignment in Hehner's theory.
Sections 4.0–4.2 of the book are formalized in the Lean modules
`LaPToP.ProgramTheory.Specifications`, `LaPToP.ProgramTheory.Programs` and
`LaPToP.ProgramTheory.Time`.
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
