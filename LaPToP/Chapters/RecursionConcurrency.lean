import Verso
import VersoManual
import VersoBlueprint
import LaPToP.RecursiveDefinition.Nat
import LaPToP.RecursiveDefinition.Programs

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Recursion and Concurrency" =>

:::group "recursion_concurrency_core"
Recursive programs, time bounds, and concurrent composition as developed in
later chapters of *A Practical Theory of Programming*. Recursive data
definition (Section 6.0) is formalized in `LaPToP.RecursiveDefinition.Nat` and
recursive program definition (Section 6.1) in `LaPToP.RecursiveDefinition.Programs`.
:::

:::definition "recursive_program" (parent := "recursion_concurrency_core") (lean := "LaPToP.RecursiveDefinition.IsFixedPoint, LaPToP.RecursiveDefinition.IsLeastFixedPoint, LaPToP.RecursiveDefinition.IsLeastFixedPoint.unique")
A recursive program is the least fixed point of a monotonic transformer on
specifications. Termination and partial-correctness arguments are expressed in
the same predicate calculus as straight-line code.

"A fixed-point of a function $`f` is an element $`x` of its domain such that
$`f` maps $`x` to itself: $`x = f\,x`. A least fixed-point of $`f` is a smallest
such $`x`." The notions are defined generally (`IsFixedPoint`,
`IsLeastFixedPoint`, unique when it exists); their use for recursive *data*
definition is {uses "least_fixed_points"}[], and the specification-level
account of recursive programs is {uses "recursive_program_zap"}[].
:::

:::theorem "nat_induction_predicate" (parent := "recursion_concurrency_core") (tags := "recursion, nat, hehner-6.0.0") (effort := "small") (lean := "LaPToP.RecursiveDefinition.natConstructor, LaPToP.RecursiveDefinition.natConstructor_subset, LaPToP.RecursiveDefinition.nat_subset_of_natConstructor_subset, LaPToP.RecursiveDefinition.mem_natConstructor, LaPToP.RecursiveDefinition.Version0, LaPToP.RecursiveDefinition.ConstructionPred, LaPToP.RecursiveDefinition.mem_nat, LaPToP.RecursiveDefinition.version0_of_bunchInduction, LaPToP.RecursiveDefinition.bunchInduction_of_version0, LaPToP.RecursiveDefinition.constructionPred_of_bunchConstruction, LaPToP.RecursiveDefinition.bunchConstruction_of_constructionPred, LaPToP.RecursiveDefinition.version0, LaPToP.RecursiveDefinition.constructionPred, LaPToP.RecursiveDefinition.single_axiom")
"To define $`\mathit{nat}`, we need to say what its elements are": the
construction axioms $`0 : \mathit{nat}`, $`\mathit{nat}+1 : \mathit{nat}` ("$`0` and
$`\mathit{nat}+1` are called the nat constructors") and the induction axiom
$`0, B+1 : B \Rightarrow \mathit{nat} : B` ("of all these bunches, nat is the smallest").
"In predicate notation, the nat induction axiom can be stated as follows: if
$`P : \mathit{nat} \to \mathit{bin}`, $`P\,0 \land (\forall n : \mathit{nat} \cdot P\,n \Rightarrow P(n+1)) \Rightarrow \forall n : \mathit{nat} \cdot P\,n`",
and construction as the reverse implication. The book proves the bunch and
predicate forms equivalent — taking $`B = \S n : \mathit{nat} \cdot P\,n` in one
direction and $`P = \langle n : \mathit{nat} \cdot n : B \rangle` in the other — and both
derivations are reproduced *as derivations* (each form as a hypothesis yields
the other). "A corollary is that nat can be defined by the single axiom
$`P\,0 \land (\forall n : \mathit{nat} \cdot P\,n \Rightarrow P(n+1)) = \forall n : \mathit{nat} \cdot P\,n`."
Uses {uses "bunch_nat_axioms"}[], {uses "quantifier_forall_exists"}[] and
{uses "solution_quantifier"}[].
:::

:::proof "nat_induction_predicate"
Bunch ⟹ predicate: apply bunch induction to $`\{n \mid n : \mathit{nat} \land P\,n\}`;
predicate ⟹ bunch: apply predicate induction to $`n \mapsto n : B`. Construction
likewise, with $`P = \langle n : \mathit{nat} \cdot n : \mathit{nat} \rangle`.
:::

:::theorem "nat_induction_versions" (parent := "recursion_concurrency_core") (tags := "recursion, nat, hehner-6.0.0") (effort := "medium") (lean := "LaPToP.RecursiveDefinition.Version1, LaPToP.RecursiveDefinition.Version2, LaPToP.RecursiveDefinition.Version3, LaPToP.RecursiveDefinition.Version4, LaPToP.RecursiveDefinition.Version5, LaPToP.RecursiveDefinition.version2_of_version0, LaPToP.RecursiveDefinition.version0_of_version2, LaPToP.RecursiveDefinition.version4_of_version0, LaPToP.RecursiveDefinition.version0_of_version4, LaPToP.RecursiveDefinition.version1_iff_version0_not, LaPToP.RecursiveDefinition.version3_iff_version2_not, LaPToP.RecursiveDefinition.version5_iff_version4_not, LaPToP.RecursiveDefinition.version1, LaPToP.RecursiveDefinition.version2, LaPToP.RecursiveDefinition.version3, LaPToP.RecursiveDefinition.version4, LaPToP.RecursiveDefinition.version5, LaPToP.RecursiveDefinition.versions_equivalent")
"There are other predicate versions of induction; here is the usual one again
plus five more":
0. $`P\,0 \land (\forall n : \mathit{nat} \cdot P\,n \Rightarrow P(n+1)) \Rightarrow \forall n : \mathit{nat} \cdot P\,n`;
1. $`P\,0 \lor (\exists n : \mathit{nat} \cdot \neg P\,n \land P(n+1)) \Leftarrow \exists n : \mathit{nat} \cdot P\,n`;
2. $`(\forall n : \mathit{nat} \cdot P\,n \Rightarrow P(n+1)) \Rightarrow \forall n : \mathit{nat} \cdot P\,0 \Rightarrow P\,n`;
3. $`(\exists n : \mathit{nat} \cdot \neg P\,n \land P(n+1)) \Leftarrow \exists n : \mathit{nat} \cdot \neg P\,0 \land P\,n`;
4. $`(\forall n : \mathit{nat} \cdot (\forall m : \mathit{nat} \cdot m < n \Rightarrow P\,m) \Rightarrow P\,n) \Rightarrow \forall n : \mathit{nat} \cdot P\,n`;
5. $`(\exists n : \mathit{nat} \cdot (\forall m : \mathit{nat} \cdot m < n \Rightarrow \neg P\,m) \land P\,n) \Leftarrow \exists n : \mathit{nat} \cdot P\,n`.
"These six versions are all equivalent to each other, and all equivalent to the
bunch form of induction." Each is proved outright; the book's remarks are
proved too — "version 1 is obtained from version 0 by the duality laws and a
renaming" (version 1 for $`P` is version 0 for $`\neg P`, and likewise 3 from 2
and 5 from 4), version 2 ("the prettiest", "related to the for-loop rule" of
{uses "for_loop"}[]) and version 4 (strong induction) are interderivable with
version 0 by changing the predicate; finally each version, taken for all
predicates, is equivalent to bunch induction. Uses
{uses "nat_induction_predicate"}[].
:::

:::proof "nat_induction_versions"
Duality by classical contraposition; version 2 from version 0 at
$`P\,0 \Rightarrow P\,n`; version 4 from version 0 at $`\forall m : \mathit{nat} \cdot m \le n \Rightarrow P\,m`;
the converses by instantiation.
:::

:::definition "least_fixed_points" (parent := "recursion_concurrency_core") (lean := "LaPToP.RecursiveDefinition.IsFixedPoint, LaPToP.RecursiveDefinition.IsLeastFixedPoint, LaPToP.RecursiveDefinition.IsLeastFixedPoint.unique, LaPToP.RecursiveDefinition.nat_fixedPoint_construction, LaPToP.RecursiveDefinition.nat_fixedPoint_induction, LaPToP.RecursiveDefinition.nat_isFixedPoint, LaPToP.RecursiveDefinition.nat_isLeastFixedPoint, LaPToP.RecursiveDefinition.natConstructor_mono")
"We now prove two similar-looking theorems: $`\mathit{nat} = 0, \mathit{nat}+1`
(nat fixed-point construction) and $`B = 0, B+1 \Rightarrow \mathit{nat} : B` (nat
fixed-point induction). ... Fixed-point construction has the form
$`\mathit{name} = (\text{expression involving } \mathit{name})` and so it says that
$`\mathit{name}` is a fixed-point of the expression on the right. Fixed-point
induction tells us that $`\mathit{name}` is the smallest bunch satisfying
fixed-point construction, and in that sense it is the least fixed-point of the
constructor." Fixed-point construction "is stronger than nat construction, so
the proof will also have to use nat induction"; fixed-point induction follows
"just by strengthening the antecedent of nat induction". Hence
$`\mathit{nat}` is the least fixed point of its (monotonic) constructor
$`B \mapsto 0, B+1`: "we could have defined nat ... as the least fixed-point of
its constructor". Uses {uses "recursive_program"}[],
{uses "nat_induction_predicate"}[] and {uses "bunch_operator_distribution"}[].
:::

:::theorem "recursive_program_zap" (parent := "recursion_concurrency_core") (tags := "recursion, programs, hehner-6.1") (effort := "medium") (lean := "LaPToP.RecursiveDefinition.ZS, LaPToP.RecursiveDefinition.Zap.assignX, LaPToP.RecursiveDefinition.Zap.assignY, LaPToP.RecursiveDefinition.Zap.tick, LaPToP.RecursiveDefinition.Zap.assignX_seq, LaPToP.RecursiveDefinition.Zap.tick_seq, LaPToP.RecursiveDefinition.Zap.timeNondecreasing, LaPToP.RecursiveDefinition.Zap.ImplementableT, LaPToP.RecursiveDefinition.Zap.zapC, LaPToP.RecursiveDefinition.Zap.step, LaPToP.RecursiveDefinition.Zap.zapC_apply, LaPToP.RecursiveDefinition.Zap.XY, LaPToP.RecursiveDefinition.Zap.T, LaPToP.RecursiveDefinition.Zap.T_step, LaPToP.RecursiveDefinition.Zap.solA, LaPToP.RecursiveDefinition.Zap.solB, LaPToP.RecursiveDefinition.Zap.solC, LaPToP.RecursiveDefinition.Zap.solD, LaPToP.RecursiveDefinition.Zap.solE, LaPToP.RecursiveDefinition.Zap.solF, LaPToP.RecursiveDefinition.Zap.base_iff, LaPToP.RecursiveDefinition.Zap.zapC_solA, LaPToP.RecursiveDefinition.Zap.zapC_solB, LaPToP.RecursiveDefinition.Zap.zapC_solC, LaPToP.RecursiveDefinition.Zap.zapC_solD, LaPToP.RecursiveDefinition.Zap.zapC_solE, LaPToP.RecursiveDefinition.Zap.zapC_solF, LaPToP.RecursiveDefinition.Zap.solA_refines_solB, LaPToP.RecursiveDefinition.Zap.solA_refines_solC, LaPToP.RecursiveDefinition.Zap.solB_refines_solD, LaPToP.RecursiveDefinition.Zap.solC_refines_solD, LaPToP.RecursiveDefinition.Zap.solC_refines_solE, LaPToP.RecursiveDefinition.Zap.solD_refines_solF, LaPToP.RecursiveDefinition.Zap.solE_refines_solF, LaPToP.RecursiveDefinition.Zap.not_solB_refines_solC, LaPToP.RecursiveDefinition.Zap.not_solC_refines_solB, LaPToP.RecursiveDefinition.Zap.not_solD_refines_solE, LaPToP.RecursiveDefinition.Zap.not_solE_refines_solD, LaPToP.RecursiveDefinition.Zap.implementableT_solA, LaPToP.RecursiveDefinition.Zap.implementableT_solB, LaPToP.RecursiveDefinition.Zap.implementableT_solC, LaPToP.RecursiveDefinition.Zap.implementableT_solD, LaPToP.RecursiveDefinition.Zap.not_implementableT_solE, LaPToP.RecursiveDefinition.Zap.not_implementable_solF, LaPToP.RecursiveDefinition.Zap.deterministic_solD, LaPToP.RecursiveDefinition.Zap.solA_refines_of_prefixed, LaPToP.RecursiveDefinition.Zap.refines_of_eq, LaPToP.RecursiveDefinition.Zap.solA_refines_of_fixedPoint, LaPToP.RecursiveDefinition.Zap.solA_weakest, LaPToP.RecursiveDefinition.Zap.zap_use_and_execute")
"Programs, and more generally, specifications, can be defined by axioms just as
data can. For our first example, let $`x` and $`y` be integer variables. The
name $`\mathit{zap}` is introduced, and the fixed-point equation
$`\mathit{zap} = \mathbf{if}\ x = 0\ \mathbf{then}\ y := 0\ \mathbf{else}\ x := x - 1.\ t := t + 1.\ \mathit{zap}`
is given as an axiom. The right side of the equation is the constructor."
The book's six solutions — (a) $`x \ge 0 \Rightarrow x' = y' = 0 \land t' = t + x`;
(b) $`\mathbf{if}\ x \ge 0\ \mathbf{then}\ x' = y' = 0 \land t' = t + x\ \mathbf{else}\ t' = \infty`;
(c) $`x' = y' = 0 \land (x \ge 0 \Rightarrow t' = t + x)`;
(d) $`x' = y' = 0 \land \mathbf{if}\ x \ge 0\ \mathbf{then}\ t' = t + x\ \mathbf{else}\ t' = \infty`;
(e) $`x' = y' = 0 \land t' = t + x`; (f) $`x \ge 0 \land x' = y' = 0 \land t' = t + x` — are
each proved to be fixed points; their refinement order is the book's picture
((a) weakest, (f) strongest, with (b),(c) and (d),(e) incomparable, "the
solutions are not totally ordered"); (a)–(d) are implementable with
nondecreasing time, "(e) and (f) are so strong that they are unimplementable",
and (d) "is also deterministic, a strongest implementable solution". Since
(e) and (f) contain $`t' = t + x` for negative $`x`, the time variable ranges
over the extended integers $`\mathit{xint}` without $`-\infty` here, in which
$`t + x` is total and $`\infty + x = \infty`. Fixed-point induction
"$`\forall\sigma, \sigma' \cdot (Z = \mathrm{constructor}\ Z) \Rightarrow \forall\sigma, \sigma' \cdot \mathit{zap} \Leftarrow Z`"
is proved as a theorem about every solution (indeed about every $`Z` with
$`\mathrm{constructor}\ Z \Leftarrow Z`), so (a) is the weakest fixed point, and
any $`\mathit{zap}` satisfying the equation "refines the weakest solution
$`(a) \Leftarrow \mathit{zap}`, so we can use it to solve problems, and it is refined
by its constructor $`\mathit{zap} \Leftarrow \mathrm{constructor}\ \mathit{zap}`, so we can
execute it". Uses {uses "recursive_program"}[], {uses "least_fixed_points"}[],
{uses "time_variable"}[] and {uses "recursive_time"}[].
:::

:::proof "recursive_program_zap"
Each fixed-point check unfolds the constructor by the Substitution Law into
the case $`x = 0` (where $`y := 0` gives $`x' = y' = 0 \land t' = t`) and the case
$`x \ne 0`, where $`t' = t + x` is invariant under $`x := x - 1.\ t := t + 1`. The
weakest-fixed-point theorem is by induction on $`x` for $`x \ge 0`.
:::

:::theorem "recursive_program_construction" (parent := "recursion_concurrency_core") (tags := "recursion, programs, hehner-6.1.0") (effort := "small") (lean := "LaPToP.RecursiveDefinition.Zap.zapN, LaPToP.RecursiveDefinition.Zap.zapN_eq, LaPToP.RecursiveDefinition.Zap.zapN_one, LaPToP.RecursiveDefinition.Zap.zapN_refines_solA, LaPToP.RecursiveDefinition.Zap.solA_eq_iInf_zapN")
"We start with $`\mathit{zap}_0` describing the computation as well as we can
without looking at the definition of zap ... a specification that is satisfied
by every computation, $`\mathit{zap}_0 = \top`. We obtain the next description of zap
by substituting $`\mathit{zap}_0` for zap in the constructor, and so on. ... In
general, $`\mathit{zap}_n` describes the computation as well as possible after $`n`
uses of the constructor. We can now guess (and prove using nat induction if we
want) $`\mathit{zap}_n = (0 \le x < n \Rightarrow x' = y' = 0 \land t' = t + x)`. The next
step is to replace $`n` with $`\infty`": $`\mathit{zap}_\infty` is solution (a), which
"satisfies the fixed-point equation, and in fact it is the weakest fixed-point".
Proved: the closed form of $`\mathit{zap}_n` by induction, and (a) as the intersection
of all $`\mathit{zap}_n`. Uses {uses "recursive_program_zap"}[] and
{uses "nat_induction_predicate"}[].
:::

:::definition "loop_definition" (parent := "recursion_concurrency_core") (lean := "LaPToP.RecursiveDefinition.LoopDefinition.whileC, LaPToP.RecursiveDefinition.LoopDefinition.WhileAxioms, LaPToP.RecursiveDefinition.LoopDefinition.whileC_mono, LaPToP.RecursiveDefinition.LoopDefinition.WhileAxioms.prefixed, LaPToP.RecursiveDefinition.LoopDefinition.WhileAxioms.fixedPoint, LaPToP.RecursiveDefinition.LoopDefinition.WhileAxioms.fixedPoint_induction, LaPToP.RecursiveDefinition.LoopDefinition.exists_whileAxioms, LaPToP.RecursiveDefinition.LoopDefinition.WhileAxioms.unique, LaPToP.RecursiveDefinition.LoopDefinition.xGe, LaPToP.RecursiveDefinition.LoopDefinition.whileRefines_xGe, LaPToP.RecursiveDefinition.LoopDefinition.WhileAxioms.refines_top_time, LaPToP.RecursiveDefinition.LoopDefinition.not_xGe_refines_while")
"Loops can be defined by construction and induction. The axioms for the
while-loop are $`t' \ge t \Leftarrow \mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od}`;
$`\mathbf{if}\ b\ \mathbf{then}\ P.\ t := t+1.\ \mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od}\ \mathbf{else}\ \mathit{ok} \Leftarrow \mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od}`;
$`\forall\sigma, \sigma' \cdot (t' \ge t \land \mathbf{if}\ b\ \mathbf{then}\ P.\ t := t+1.\ W\ \mathbf{else}\ \mathit{ok} \Leftarrow W) \Rightarrow \forall\sigma, \sigma' \cdot \mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od} \Leftarrow W`.
... These three axioms are closely analogous to the axioms $`0 : \mathit{nat}`,
$`\mathit{nat}+1 : \mathit{nat}`, $`0, B+1 : B \Rightarrow \mathit{nat} : B` that define nat."
The axioms are a structure `WhileAxioms`; from them the fixed-point theorems
$`\mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od} = t' \ge t \land \mathbf{if}\ b\ \mathbf{then}\ P.\ t := t+1.\ \mathbf{while} \ldots\ \mathbf{else}\ \mathit{ok}`
and fixed-point induction are derived, the axioms are shown consistent (the
union of all pre-fixed points satisfies them) and to determine the loop
uniquely. "This account differs from that presented in Section 5.2; we have
gained some theorems, and lost some theorems. For example, from this least
fixed-point definition, we cannot prove $`x' \ge x \Leftarrow \mathbf{while}\ b\ \mathbf{do}\ x' \ge x\ \mathbf{od}`,
which was easily proved according to Section 5.2" — both halves are proved:
the refinement is a theorem for {uses "while_loop"}[], while any loop
satisfying the axioms (for $`b = \top`) admits every final state at time
$`\infty`, so the refinement fails. Uses {uses "recursive_program_zap"}[],
{uses "nat_induction_predicate"}[] and {uses "time_variable"}[].
:::

:::theorem "nat_repeat_zero" (parent := "recursion_concurrency_core") (tags := "recursion, nat") (effort := "small")
Repeating a step zero times is the identity on states represented as natural
numbers: $`\mathsf{repeat}\, f\, 0\, n = n`.
A kernel-level stand-in for the base case of {uses "recursive_program"}[].
:::

:::proof "nat_repeat_zero"
By the definition of `Nat.repeat`.
:::

```lean "nat_repeat_zero"
theorem nat_repeat_zero (f : Nat → Nat) (n : Nat) :
    Nat.repeat f 0 n = n := rfl
```

:::definition "concurrent_composition" (parent := "recursion_concurrency_core")
Concurrent composition combines independent (or weakly dependent) processes.
LaPToP treats concurrency in the same refinement framework as sequential
programs, once communication and timing are modeled. This node depends on
{uses "recursive_program"}[] for looping clients of concurrent servers.
:::
