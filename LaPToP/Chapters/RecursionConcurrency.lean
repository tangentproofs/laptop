import Verso
import VersoManual
import VersoBlueprint
import LaPToP.RecursiveDefinition.Nat

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Recursion and Concurrency" =>

:::group "recursion_concurrency_core"
Recursive programs, time bounds, and concurrent composition as developed in
later chapters of *A Practical Theory of Programming*. Recursive data
definition (Section 6.0) is formalized in `LaPToP.RecursiveDefinition.Nat`.
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
account of recursive programs (Section 6.1) is future work.
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
