import Verso
import VersoManual
import VersoBlueprint
import LaPToP.RecursiveDefinition.Nat
import LaPToP.RecursiveDefinition.Programs
import LaPToP.RecursiveDefinition.DataConstruction
import LaPToP.Concurrency.Composition
import LaPToP.Concurrency.ListConcurrency
import LaPToP.Concurrency.Transformation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Recursion and Concurrency" =>

:::group "recursion_concurrency_core"
Recursive programs, time bounds, and concurrent composition as developed in
later chapters of *A Practical Theory of Programming*. Recursive data
definition (Section 6.0) is formalized in `LaPToP.RecursiveDefinition.Nat` and
`LaPToP.RecursiveDefinition.DataConstruction`, recursive program definition
(Section 6.1) in `LaPToP.RecursiveDefinition.Programs`, and concurrent
composition (Section 8.0) in `LaPToP.Concurrency.Composition` and
`LaPToP.Concurrency.ListConcurrency`, and the sequential-to-concurrent
transformation (Section 8.1) in `LaPToP.Concurrency.Transformation`.
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

:::definition "recursive_data_construction" (parent := "recursion_concurrency_core") (lean := "LaPToP.RecursiveDefinition.chain, LaPToP.RecursiveDefinition.chain_succ, LaPToP.RecursiveDefinition.limit, LaPToP.RecursiveDefinition.chain_mono, LaPToP.RecursiveDefinition.chain_subset_of_prefixed, LaPToP.RecursiveDefinition.limit_subset_of_fixedPoint, LaPToP.RecursiveDefinition.isLeastFixedPoint_of_test, LaPToP.RecursiveDefinition.limit_subset_apply")
"Recursive construction is a procedure for constructing solutions from
constructors. It usually works, but not always. We seek a solution of
$`\mathit{name} :: (\text{expression involving } \mathit{name})` or
$`\mathit{name} = (\text{expression involving } \mathit{name})`." The steps:
0. construct $`\mathit{name}_0 = \mathit{null}`, $`\mathit{name}_{n+1} = (\text{expression involving } \mathit{name}_n)`;
1. find an expression for $`\mathit{name}_n` not involving $`\mathit{name}`;
2. form $`\mathit{name}_\infty` by replacing $`n` with $`\infty`;
3. test that $`\mathit{name}_\infty` is a solution;
4. for the smallest solution, test $`B = (\text{expression involving } B) \Rightarrow \mathit{name}_\infty : B`.
For a *monotone* constructor the general facts are proved: the sequence is
increasing, its union (the honest reading of step 2) is included in every
fixed point — so step 4 is automatic — and if the union passes the test of
step 3 it is the least fixed point; the union is always a post-fixed point.
The book's caveat stands: "the bunch $`\mathit{name}_\infty` is usually a solution,
but not always, so we must test it" — when the test fails the procedure yields
nothing, and the property ("continuity") that would guarantee success is
"left to other books". Uses {uses "least_fixed_points"}[].
:::

:::theorem "pow_least_fixed_point" (parent := "recursion_concurrency_core") (tags := "recursion, data, hehner-6.0.2") (effort := "small") (lean := "LaPToP.RecursiveDefinition.powConstructor, LaPToP.RecursiveDefinition.powConstructor_mono, LaPToP.RecursiveDefinition.powN, LaPToP.RecursiveDefinition.powN_zero, LaPToP.RecursiveDefinition.powN_one, LaPToP.RecursiveDefinition.powN_two, LaPToP.RecursiveDefinition.powN_three, LaPToP.RecursiveDefinition.powN_eq, LaPToP.RecursiveDefinition.powInf, LaPToP.RecursiveDefinition.powInf_eq_limit, LaPToP.RecursiveDefinition.powConstructor_powInf, LaPToP.RecursiveDefinition.powInf_subset_of_fixedPoint, LaPToP.RecursiveDefinition.powInf_isLeastFixedPoint, LaPToP.RecursiveDefinition.pow_eq_powInf, LaPToP.RecursiveDefinition.limit_powConstructor_isLeastFixedPoint")
The book's illustration: $`\mathit{pow} = 1, 2 \times \mathit{pow}` and
$`B = 1, 2 \times B \Rightarrow \mathit{pow} : B`. Step 0: $`\mathit{pow}_0 = \mathit{null}`,
$`\mathit{pow}_1 = 1`, $`\mathit{pow}_2 = 1, 2`, $`\mathit{pow}_3 = 1, 2, 4`. Step 1: "perhaps
now we can guess $`\mathit{pow}_n = 2^{0,..n}`. We could prove this by nat
induction, but it is not really necessary" (it is proved here). Step 2:
$`\mathit{pow}_\infty = 2^{0,..\infty} = 2^{\mathit{nat}}`, the union of the $`\mathit{pow}_n`.
Step 3: $`2^{\mathit{nat}} = 1, 2 \times 2^{\mathit{nat}}` "$`\Leftarrow \mathit{nat} = 0, \mathit{nat}+1`,
nat fixed-point construction". Step 4: $`2^{\mathit{nat}} : B \Leftarrow B = 1, 2 \times B`,
"use the predicate form of nat induction". "Since $`2^{\mathit{nat}}` is the least
fixed-point of the pow constructor, we conclude $`\mathit{pow} = 2^{\mathit{nat}}`" — any
bunch satisfying both axioms equals it, by uniqueness of least fixed points;
the same conclusion follows from the general procedure. Uses
{uses "recursive_data_construction"}[], {uses "nat_induction_predicate"}[] and
{uses "bunch_operator_distribution"}[] ($`2 \times B` distributes over union).
:::

:::proof "pow_least_fixed_point"
The closed form by induction on $`n`; the tests by case analysis on the
exponent ($`2^0 = 1`, $`2^{k+1} = 2 \times 2^k`); leastness by induction on the
exponent inside a fixed point.
:::

:::theorem "inconsistent_axiom_bad" (parent := "recursion_concurrency_core") (tags := "recursion, data, hehner-6.0.2") (effort := "small") (lean := "LaPToP.RecursiveDefinition.badConstructor, LaPToP.RecursiveDefinition.zero_mem_iff_not_mem, LaPToP.RecursiveDefinition.not_exists_bad, LaPToP.RecursiveDefinition.badConstructor_antitone, LaPToP.RecursiveDefinition.badN, LaPToP.RecursiveDefinition.badN_zero, LaPToP.RecursiveDefinition.badN_one, LaPToP.RecursiveDefinition.badN_two, LaPToP.RecursiveDefinition.badN_add_two, LaPToP.RecursiveDefinition.badN_not_mono")
"Whenever we add axioms, we must be careful to remain consistent with the
theory we already have. A badly chosen axiom can cause inconsistency. ...
Suppose we make $`\mathit{bad} = \S n : \mathit{nat} \cdot \neg\, n : \mathit{bad}` an axiom. Thus
$`\mathit{bad}` is defined as the bunch of all naturals that are not in $`\mathit{bad}`.
From this axiom we find $`0 : \mathit{bad} = \neg\, 0 : \mathit{bad}` is a theorem ... also an
antitheorem. To avoid the inconsistency, we must withdraw this axiom." Proved:
no bunch satisfies the axiom. "Sometimes recursive construction does not
produce any answer": the sequence $`\mathit{bad}_0 = \mathit{null}`, $`\mathit{bad}_1 = \mathit{nat}`,
$`\mathit{bad}_2 = \mathit{null}`, "and so on, alternating between $`\mathit{null}` and
$`\mathit{nat}`. We cannot say what $`\mathit{bad}_\infty` is" — the constructor is
antitone, not monotone, and the sequence is not increasing. Uses
{uses "recursive_data_construction"}[] and {uses "solution_quantifier"}[].
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

:::definition "concurrent_composition" (parent := "recursion_concurrency_core") (lean := "LaPToP.Concurrency.par, LaPToP.Concurrency.parWith, LaPToP.Concurrency.par_eq_parWith, LaPToP.Concurrency.assignF, LaPToP.Concurrency.assignF_seq, LaPToP.Concurrency.parT, LaPToP.Concurrency.parT_comm, LaPToP.Concurrency.parT_time_nondecreasing, LaPToP.Concurrency.parT_finish")
Concurrent composition combines independent (or weakly dependent) processes.
LaPToP treats concurrency in the same refinement framework as sequential
programs, once communication and timing are modeled. This node depends on
{uses "recursive_program"}[] for looping clients of concurrent servers.

"We define the concurrent composition of specifications $`P` and $`Q` so that
$`P \parallel Q` is satisfied by a computer that behaves according to $`P` and,
at the same time, concurrently, according to $`Q`. ... For concurrent
composition $`P \parallel Q`, we require that $`P` and $`Q` have completely
different state variables, and the state variables of the composition are
those of both. If we ignore time and space, concurrent composition is
conjunction: $`P \parallel Q = P \land Q`." The partition is made explicit by a
product state: a process on $`\sigma_1` and a process on $`\sigma_2` compose to
`Spec.par P Q` on $`\sigma_1 \times \sigma_2`; a process may mention the other's
variables "but only as constants" — `Spec.parWith` lets each read the *initial*
values of the other's variables. "The time variable is not subject to
partitioning; it belongs to both processes. ... With time,
$`P \parallel Q = \exists t_P, t_Q \cdot \langle t' \cdot P \rangle t_P \land \langle t' \cdot Q \rangle t_Q \land t' = t_P \uparrow t_Q`":
`Spec.parT`, symmetric, time-nondecreasing when a process is, and finishing
no earlier than either process. Uses {uses "specification_notations"}[] and
{uses "time_variable"}[].
:::

:::theorem "concurrent_composition_examples" (parent := "recursion_concurrency_core") (tags := "concurrency, hehner-8.0") (effort := "small") (lean := "LaPToP.Concurrency.Examples.incr_par, LaPToP.Concurrency.Examples.swap_par, LaPToP.Concurrency.Examples.beq_par, LaPToP.Concurrency.Examples.incr_decr, LaPToP.Concurrency.Examples.seq_par, LaPToP.Concurrency.Examples.subst_example, LaPToP.Concurrency.Examples.two_stage")
The book's examples, in integer variables: $`x := x+1 \parallel y := y+2 = (x' = x+1 \land y' = y+2)`
("$`x` has to belong to the left process and $`y` to the right");
$`x := y \parallel y := x = (x' = y \land y' = x)` — "variables $`x` and $`y` swap values,
apparently without a temporary variable"; $`b := (x = x) \parallel x := x+1 = b := \top \parallel x := x+1`
— "both occurrences of $`x` in the left process refer to the initial value of
variable $`x`"; $`(x := x+1.\ x := x-1) \parallel y := x = \mathit{ok} \parallel y := x = y := x` —
"the intermediate values of variables are local to the sequential
composition; ... the occurrence of $`x` in the right process refers to the
initial value"; the Substitution Law example
$`(x := x+y \parallel y := x \times y).\ z' = x - y = (z' = (x+y) - (x \times y))`; and
"synchronization is sequencing": $`(x := x+y \parallel y := x-y).\ (x := x \times y \parallel y := x/y)`
computed by concurrent substitution. Uses {uses "concurrent_composition"}[]
and {uses "substitution_law"}[].
:::

:::theorem "concurrent_composition_laws" (parent := "recursion_concurrency_core") (tags := "concurrency, laws, hehner-8.0.0") (effort := "small") (lean := "LaPToP.Concurrency.par_comm, LaPToP.Concurrency.assoc, LaPToP.Concurrency.par_assoc, LaPToP.Concurrency.par_or, LaPToP.Concurrency.par_cond, LaPToP.Concurrency.cond_par, LaPToP.Concurrency.par_assignF_seq, LaPToP.Concurrency.parWith_assignF_seq, LaPToP.Concurrency.par_mono, LaPToP.Concurrency.steps_par, LaPToP.Concurrency.parts_par")
The laws of Section 8.0.0, for different state variables $`x, y`, expressions
$`e, f, b` of the prestate, and specifications $`P, Q, R, S`:
concurrent substitution $`(x := e \parallel y := f).\ P = (\text{substitute } e \text{ for } x \text{ and concurrently } f \text{ for } y \text{ in } P)`
— "each substitution replaces all and only the original occurrences of its
variable"; symmetry $`P \parallel Q = Q \parallel P` and associativity
$`P \parallel (Q \parallel R) = (P \parallel Q) \parallel R` ("we can compose any number of
processes without worrying how they are grouped"), each up to the evident
reshuffling of the product state; distributivity $`P \parallel (Q \lor R) = (P \parallel Q) \lor (P \parallel R)`,
$`P \parallel \mathbf{if}\ b\ \mathbf{then}\ Q\ \mathbf{else}\ R = \mathbf{if}\ b\ \mathbf{then}\ P \parallel Q\ \mathbf{else}\ P \parallel R`,
$`\mathbf{if}\ b\ \mathbf{then}\ P \parallel Q\ \mathbf{else}\ R \parallel S = (\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ R) \parallel (\mathbf{if}\ b\ \mathbf{then}\ Q\ \mathbf{else}\ S)`
(each process reading the other's initial variables to evaluate $`b`);
"Refinement by Steps works for concurrent composition: if $`A \Leftarrow B \parallel C`,
$`B \Leftarrow D`, $`C \Leftarrow E` then $`A \Leftarrow D \parallel E`; so does Refinement by Parts:
if $`A \Leftarrow B \parallel C` and $`D \Leftarrow E \parallel F` then $`A \land D \Leftarrow (B \land E) \parallel (C \land F)`."
Uses {uses "concurrent_composition"}[], {uses "specification_laws"}[] and
{uses "refinement_by_steps_parts_cases"}[].
:::

:::definition "list_concurrency" (parent := "recursion_concurrency_core") (lean := "LaPToP.Concurrency.LS, LaPToP.Concurrency.ListConc.assignItem, LaPToP.Concurrency.ListConc.tick, LaPToP.Concurrency.ListConc.tick_seq, LaPToP.Concurrency.ListConc.parSeg, LaPToP.Concurrency.ListConc.segSup, LaPToP.Concurrency.ListConc.segSup_singleton, LaPToP.Concurrency.ListConc.segSup_split, LaPToP.Concurrency.ListConc.segSup_congr")
"We have defined concurrent composition by partitioning the variables. For
finer-grained concurrency, we can extend this same idea to the individual items
within list variables. ... $`L\,i := e = (L'\,i = e \land (\forall j \cdot j \neq i \Rightarrow L'\,j = L\,j) \land x' = x \land \ldots)`
... For concurrent composition, we must specify the final values of only the
items and variables in one side of the partition." The state is a list
variable $`L` (an indexed sequence) with the time $`t`; segment concurrency
composes a process owning the items $`i,..m` with one owning $`m,..j`: both
start from the same state, the final list takes each process's values on its
segment, items outside $`i,..j` are unchanged, and $`t' = t_P \uparrow t_Q`. The
segment maximum $`\Uparrow L[i;..j]` is a supremum in $`\mathit{xint}`, $`-\infty` on an
empty segment as in {uses "quantifier_numeric"}[]; it is the item on a
one-item segment and splits as $`\Uparrow L[i;..j] = \Uparrow L[i;..m] \uparrow \Uparrow L[m;..j]`.
Uses {uses "concurrent_composition"}[], {uses "list_axioms"}[] and
{uses "time_variable"}[].
:::

:::theorem "findmax" (parent := "recursion_concurrency_core") (tags := "concurrency, lists, time, hehner-8.0.1") (effort := "medium") (lean := "LaPToP.Concurrency.ListConc.clog_two_split, LaPToP.Concurrency.ListConc.coe_max_enat, LaPToP.Concurrency.ListConc.max_add_add_left_enat, LaPToP.Concurrency.ListConc.findmax, LaPToP.Concurrency.ListConc.findmax_zero, LaPToP.Concurrency.ListConc.mid, LaPToP.Concurrency.ListConc.findmax_refines")
Exercise 172, "find the maximum item in a list": "our specification will be
$`L'\,0 = \Uparrow L \land t' = t + \lceil \log(\# L) \rceil`. ... The first step is to
generalize from the maximum of a nonempty list to the maximum of a nonempty
segment: $`\mathit{findmax} = \langle i, j \cdot i < j \Rightarrow L'\,i = \Uparrow L[i;..j] \land t' = t + \lceil \log(j - i) \rceil \rangle`.
Our specification is $`\mathit{findmax}\ 0\ (\# L)`. We refine as follows:
$`\mathit{findmax}\ i\ j \Leftarrow \mathbf{if}\ j - i = 1\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ t := t+1.\ (\mathit{findmax}\ i\ m \parallel \mathit{findmax}\ m\ j).\ L\,i := L\,i \uparrow L\,m`
with $`m = \mathit{div}\,(i+j)\,2`. If $`j - i = 1` the segment contains one item; to
place the maximum item (the only item) at index $`i` requires no change. In the
other case ... we divide the segment into two halves, placing the maximum of
each half at the beginning of the half. In the concurrent composition, the two
processes change disjoint segments of the list. We finish by placing the
maximum of the two maximums at the start of the whole segment. The recursive
execution time is $`\lceil \log(j - i) \rceil`." The refinement is proved with the
recursive calls taken as specifications (as in {uses "recursive_program_zap"}[]),
and the timing exactly, from $`\lceil \log n \rceil = 1 + \lceil \log \lfloor n/2 \rfloor \rceil \uparrow \lceil \log \lceil n/2 \rceil \rceil`
for $`n \ge 2` (`Nat.clog`). Uses {uses "list_concurrency"}[],
{uses "recursive_time"}[] and {uses "specification_laws"}[].
:::

:::theorem "sequential_to_concurrent" (parent := "recursion_concurrency_core") (tags := "concurrency, transformation, hehner-8.1") (effort := "small") (lean := "LaPToP.Concurrency.liftL, LaPToP.Concurrency.liftR, LaPToP.Concurrency.liftLWith, LaPToP.Concurrency.liftRWith, LaPToP.Concurrency.liftL_eq_liftLWith, LaPToP.Concurrency.liftR_eq_liftRWith, LaPToP.Concurrency.seq_liftL_liftR, LaPToP.Concurrency.seq_liftR_liftL, LaPToP.Concurrency.seq_liftRWith_liftL, LaPToP.Concurrency.seq_liftLWith_liftR, LaPToP.Concurrency.seq_liftLWith_par, LaPToP.Concurrency.seq_liftRWith_par, LaPToP.Concurrency.Examples.xy, LaPToP.Concurrency.Examples.xinc, LaPToP.Concurrency.Examples.zy, LaPToP.Concurrency.Examples.step₁, LaPToP.Concurrency.Examples.step₂, LaPToP.Concurrency.Examples.result")
"The goal of this section is to transform programs without concurrency into
programs with concurrency. A simple example illustrates the idea.
$`x := y.\ x := x+1.\ z := y \;=\; x := y.\ (x := x+1 \parallel z := y) \;=\; (x := y.\ x := x+1) \parallel z := y`
... The first two assignments cannot be executed concurrently, but the last two
can, so we transform the program. ... Now we have the first and last
assignments next to each other, in sequence; they too can be executed
concurrently. Whenever two programs occur in sequence, and neither assigns to
any variable assigned in the other, and no variable assigned in the first
appears in the second, they can be placed in parallel; a copy must be made of
the initial value of any variable appearing in the first and assigned in the
second. Whenever two programs occur in sequence, and neither assigns to any
variable appearing in the other, they can be placed in parallel without any
copying of initial values. This transformation does not change the result of a
computation, but it may decrease the time, and that is the reason for doing
it." With the variables partitioned as a product (see
{uses "concurrent_composition"}[]), a program that assigns only the left
variables is a lifted left process, reading the right variables as constants
or not at all; the two sentences are the equalities
$`\mathit{liftL}\,P.\ \mathit{liftR}\,Q = P \parallel Q` (no copying) and
$`\mathit{liftRWith}\,Q.\ \mathit{liftL}\,P = P \parallel Q` with $`Q` reading the
initial value of the left variables — the copy is exactly the initial-value
parameter of $`\parallel` in {uses "concurrent_composition_laws"}[]. A further
law absorbs a preceding program into one process, which gives the second step
of the example; the three programs all compute $`x' = y+1 \land y' = y \land z' = y`.
Model note: "assigns to" and "appears in" are expressed by the shape of the
lifting, not by syntactic inspection of named variables; the time remark is
not formalized here. Uses {uses "specification_laws"}[].
:::

:::theorem "buffer" (parent := "recursion_concurrency_core") (tags := "concurrency, buffer, hehner-8.1.0") (effort := "small") (lean := "LaPToP.Concurrency.Buffer.BS, LaPToP.Concurrency.Buffer.produce, LaPToP.Concurrency.Buffer.consume, LaPToP.Concurrency.Buffer.consumeC, LaPToP.Concurrency.Buffer.copy, LaPToP.Concurrency.Buffer.consume_produce, LaPToP.Concurrency.Buffer.copy_consumeC_produce, LaPToP.Concurrency.Buffer.consume_produce_eq, LaPToP.Concurrency.Buffer.consume_produce_eq_copy_par, LaPToP.Concurrency.Buffer.controlBody, LaPToP.Concurrency.Buffer.newcontrolBody, LaPToP.Concurrency.Buffer.newcontrolBody_eq, LaPToP.Concurrency.Buffer.control_of_newcontrol")
"Consider two programs, $`\mathit{produce}` and $`\mathit{consume}`, whose only common
variable is $`b`. $`\mathit{produce}` assigns to $`b` and $`\mathit{consume}` uses the value of
$`b`. ... $`\mathit{produce} = \cdots b := e \cdots`, $`\mathit{consume} = \cdots x := b \cdots`.
These two programs are executed alternately, repeatedly, forever.
$`\mathit{control} = \mathit{produce}.\ \mathit{consume}.\ \mathit{control}`. ... Variable $`b` is
called a buffer. ... we cannot put them in parallel because the first assigns to
$`b` and the second uses $`b`. So we unroll the loop once.
$`\mathit{control} = \mathit{produce}.\ \mathit{newcontrol}`,
$`\mathit{newcontrol} = \mathit{consume}.\ \mathit{produce}.\ \mathit{newcontrol}` and
$`\mathit{newcontrol}` can be transformed to
$`\mathit{newcontrol} = (\mathit{consume} \parallel \mathit{produce}).\ \mathit{newcontrol}`. In
this transformed program, a compiler will have to capture a copy of the initial
value of $`b` for $`\mathit{consume}` to use. Or, we could do this capture at source
level, using variable $`c`: $`\mathit{consume} = \cdots x := c \cdots`,
$`\mathit{newcontrol} = c := b.\ (\mathit{consume} \parallel \mathit{produce}).\ \mathit{newcontrol}`."
The unrolled body $`\mathit{consume}.\ \mathit{produce}` is the concurrent composition by
the copy law of {uses "sequential_to_concurrent"}[]; the source-level form
computes the same $`b'`, $`x'` and differs only in the auxiliary $`c`. Since
$`\mathit{control}` is a recursively defined specification
({uses "recursive_program_zap"}[]), the unrolling is stated as: any fixed point
$`\mathit{newcontrol}` of its equation gives the fixed point
$`\mathit{produce}.\ \mathit{newcontrol}` of the equation for $`\mathit{control}`. The
infinite buffer with write and read counters $`w`, $`r` (concurrent whenever
$`w \neq r`) and the cyclic buffer of length $`n` are left informal, as the book
says the pattern "is not expressible as a source program without additional
interactive constructs (Chapter 9)".
:::
