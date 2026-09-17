import Verso
import VersoManual
import VersoBlueprint
import LaPToP.FunctionTheory.Functions
import LaPToP.FunctionTheory.Quantifiers
import LaPToP.FunctionTheory.FinePoints
import LaPToP.FunctionTheory.HigherOrder
import LaPToP.FunctionTheory.Limits
import LaPToP.FunctionTheory.QuantifierDistribution

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Function Theory" =>

:::group "function_theory_core"
Functions with an explicit domain, selective union, predicates and relations,
and the quantifiers built on them: Hehner's Chapter 3, the prerequisite for the
specifications and refinements of Program Theory. The formal counterparts are the
Lean modules `LaPToP.FunctionTheory.Functions`,
`LaPToP.FunctionTheory.Quantifiers`, `LaPToP.FunctionTheory.FinePoints`
(Section 3.2, function fine points), `LaPToP.FunctionTheory.HigherOrder`
(Sections 3.2.1–3.2.2, functions as data), `LaPToP.FunctionTheory.Limits`
(Section 3.4, limits and reals) and `LaPToP.FunctionTheory.QuantifierDistribution`
(the distributive laws of §11.3.8).
:::

:::definition "function_notation" (parent := "function_theory_core") (lean := "LaPToP.FunctionTheory.Fn, LaPToP.FunctionTheory.Fn.lam, LaPToP.FunctionTheory.Fn.domain, LaPToP.FunctionTheory.Fn.size, LaPToP.FunctionTheory.Fn.apply, LaPToP.FunctionTheory.Fn.arrow, LaPToP.FunctionTheory.Fn.ext")
$`\langle v : D \cdot b \rangle`, "map $`v` in $`D` to $`b`", is a function of
variable $`v` with domain $`D` (a bunch) and body $`b`; the inclusion $`v : D`
is a local axiom within the body. $`\square f` is the domain of $`f`,
$`\# f = {\rm c\llap{/}}\square f` its size, and $`f\,x` ("$`f` applied to $`x`") its
value at an element $`x` of its domain. $`x \to y` abbreviates
$`\langle v : x \cdot y \rangle` with an unused variable.

In Lean a function is a structure `Fn α β` with a domain `dom : Bunch α` and a
body defined *only on the domain*, `body : (x : α) → x ∈ dom → β`; application
`Fn.apply f x h` takes the proof `h : x ∈ ☐f`, which is the book's local axiom
made explicit. Because the body is defined only on the domain, Lean equality of
`Fn` values is exactly Hehner's function equality — same domain, same values on
it (`Fn.ext`). Domains are the bunches of {uses "bunch_vs_set"}[].
:::

:::theorem "function_axioms" (parent := "function_theory_core") (tags := "function, hehner-3.0") (effort := "small") (lean := "LaPToP.FunctionTheory.Fn.domain_lam, LaPToP.FunctionTheory.Fn.size_eq, LaPToP.FunctionTheory.Fn.apply_lam, LaPToP.FunctionTheory.Fn.extension, LaPToP.FunctionTheory.Fn.renaming_axiom, LaPToP.FunctionTheory.Fn.apply_arrow, LaPToP.FunctionTheory.Fn.domain_arrow")
The axioms of Section 3.0: the Domain Axiom $`\square\langle v : D \cdot b \rangle = D`;
$`\# f = {\rm c\llap{/}}\square f`; the Application Axiom
$`x : D \Rightarrow \langle v : D \cdot b \rangle\,x = (\text{substitute } x \text{ for } v \text{ in } b)`;
the Axiom of Extension $`f = \langle w : \square f \cdot f\,w \rangle`; and the
Renaming Axiom $`\langle v : D \cdot b \rangle = \langle w : D \cdot \langle v : D \cdot b \rangle\,w \rangle`,
which is an instance of Extension. Also $`(x \to y)\,x = y` and
$`\square(x \to y) = x`. Uses {uses "function_notation"}[].
:::

:::proof "function_axioms"
All definitional: substitution is β-reduction and Extension is structure eta,
so every axiom is `rfl`.
:::

:::definition "selective_union" (parent := "function_theory_core") (lean := "LaPToP.FunctionTheory.Fn.orElse, LaPToP.FunctionTheory.Fn.domain_orElse, LaPToP.FunctionTheory.Fn.apply_orElse, LaPToP.FunctionTheory.Fn.apply_orElse_left, LaPToP.FunctionTheory.Fn.apply_orElse_right, LaPToP.FunctionTheory.Fn.orElse_self, LaPToP.FunctionTheory.Fn.orElse_assoc, LaPToP.FunctionTheory.Fn.orElse_comp")
$`f \mid g`, "$`f` otherwise $`g`", "behaves like $`f` when applied to an
argument in the domain of $`f`, and otherwise behaves like $`g`". Its axioms are
$`\square(f \mid g) = \square f, \square g` and
$`(f \mid g)\,x = \mathbf{if}\ x : \square f\ \mathbf{then}\ f\,x\ \mathbf{else}\ g\,x`,
with the two cases spelled out as corollaries. The Reference chapter's laws
$`f \mid f = f`, $`f \mid (g \mid h) = (f \mid g) \mid h` and $`(g \mid h)\,f = g\,f \mid h\,f`
(§11.3.7) are `orElse_self`, `orElse_assoc` and `orElse_comp` (the last in the
higher-order module, with composition). Uses {uses "function_notation"}[]
and {uses "bunch_axioms_membership"}[].
:::

:::definition "predicates_relations" (parent := "function_theory_core") (lean := "LaPToP.FunctionTheory.Pred, LaPToP.FunctionTheory.even, LaPToP.FunctionTheory.odd, LaPToP.FunctionTheory.divides, LaPToP.FunctionTheory.two_mem_nat_add_one, LaPToP.FunctionTheory.divides_two, LaPToP.FunctionTheory.divides_two_three, LaPToP.FunctionTheory.odd_apply")
"A predicate is a function whose body is a binary expression": `Pred α := Fn α Binary`,
with values in {uses "boolean_domain"}[]. The book's examples
$`\mathit{even} = \langle i : \mathit{int} \cdot i/2 : \mathit{int} \rangle` and
$`\mathit{odd} = \langle i : \mathit{int} \cdot \neg\, i/2 : \mathit{int} \rangle` read
"$`i/2` is an integer" as $`2 \mid i`. "A relation is a function whose body is
a predicate":
$`\mathit{divides} = \langle n : \mathit{nat}+1 \cdot \langle i : \mathit{int} \cdot i/n : \mathit{int} \rangle\rangle`,
with $`\mathit{divides}\ 2 = \mathit{even}` and $`\mathit{divides}\ 2\ 3 = \bot`
checked. Domains are the named bunches of {uses "bunch_named_bunches"}[].
:::

:::definition "quantifier_forall_exists" (parent := "function_theory_core") (lean := "LaPToP.FunctionTheory.Fn.all, LaPToP.FunctionTheory.Fn.ex, LaPToP.FunctionTheory.Fn.all_null, LaPToP.FunctionTheory.Fn.all_elem, LaPToP.FunctionTheory.Fn.all_union, LaPToP.FunctionTheory.Fn.not_ex_null, LaPToP.FunctionTheory.Fn.ex_elem, LaPToP.FunctionTheory.Fn.ex_union")
"A quantifier is a one-operand prefix operator that applies to functions."
For a predicate $`p`, $`\forall p` conjoins and $`\exists p` disjoins the
results of applying $`p` to all its domain elements. The axioms, for bunches
$`A, B`, an element $`x` and a binary body $`b`:
$`\forall v : \mathit{null} \cdot b = \top`,
$`\forall v : x \cdot b = \langle v : x \cdot b \rangle\,x`,
$`\forall v : A, B \cdot b = (\forall v : A \cdot b) \land (\forall v : B \cdot b)`, and dually
$`\exists v : \mathit{null} \cdot b = \bot`,
$`\exists v : x \cdot b = \langle v : x \cdot b \rangle\,x`,
$`\exists v : A, B \cdot b = (\exists v : A \cdot b) \lor (\exists v : B \cdot b)`.
The book's $`\forall p` and $`\exists p` are binary values; over an infinite
domain they are not computable, so in Lean they are propositions (`Fn.all`,
`Fn.ex`) and the axioms are equivalences. Uses {uses "predicates_relations"}[].
:::

:::definition "solution_quantifier" (parent := "function_theory_core") (lean := "LaPToP.FunctionTheory.Fn.sols, LaPToP.FunctionTheory.Fn.sols_null, LaPToP.FunctionTheory.Fn.sols_elem, LaPToP.FunctionTheory.Fn.sols_union, LaPToP.FunctionTheory.Fn.sols_subset_domain, LaPToP.FunctionTheory.Fn.mem_sols")
The solution quantifier $`\S p`, "those", "gives the bunch of solutions of a
predicate": $`\S\langle i : \mathit{int} \cdot i^2 = 4 \rangle = 2, -2`. Axioms:
$`\S v : \mathit{null} \cdot b = \mathit{null}`,
$`\S v : x \cdot b = \mathbf{if}\ \langle v : x \cdot b \rangle\,x\ \mathbf{then}\ x\ \mathbf{else}\ \mathit{null}`,
$`\S v : A, B \cdot b = (\S v : A \cdot b), (\S v : B \cdot b)`; also $`\S p : \square p`
and $`x : \S p = x : \square p \land p\,x`. Uses {uses "predicates_relations"}[] and
{uses "bunch_primitives"}[].
:::

:::theorem "quantifier_laws_basic" (parent := "function_theory_core") (tags := "function, quantifier, hehner-3.1") (effort := "small") (lean := "LaPToP.FunctionTheory.Fn.all_apply, LaPToP.FunctionTheory.Fn.ex_of_apply, LaPToP.FunctionTheory.Fn.ex_of_all, LaPToP.FunctionTheory.Fn.all_eq_imp, LaPToP.FunctionTheory.Fn.ex_eq_and")
Specialization and Generalization: if $`p` is a predicate and $`x : \square p`,
then $`\forall p \Rightarrow p\,x \Rightarrow \exists p`. The One-Point Laws: if
$`x : D` (and $`v` does not appear in $`x`),
$`\forall v : D \cdot v = x \Rightarrow b \;=\; \langle v : D \cdot b \rangle\,x` and
$`\exists v : D \cdot v = x \land b \;=\; \langle v : D \cdot b \rangle\,x`.
Uses {uses "quantifier_forall_exists"}[] and {uses "binary_laws_basic"}[].
:::

:::proof "quantifier_laws_basic"
Specialization instantiates the universal at $`x`; Generalization exhibits
$`x`. For One-Point, the antecedent/conjunct $`v = x` pins the variable, and
the equality is decided in `Bool`.
:::

:::definition "quantifier_numeric" (parent := "function_theory_core") (lean := "LaPToP.FunctionTheory.Fn.values, LaPToP.FunctionTheory.Fn.values_lam, LaPToP.FunctionTheory.Fn.sup, LaPToP.FunctionTheory.Fn.inf, LaPToP.FunctionTheory.Fn.sum, LaPToP.FunctionTheory.Fn.prod, LaPToP.FunctionTheory.Fn.sup_eq_max")
"Any two-operand symmetric associative operator can be used to define a
quantifier": $`+`, $`\times`, $`\uparrow`, $`\downarrow` give $`\Sigma`, $`\Pi`,
$`\Uparrow`, $`\Downarrow`. For a numeric function $`f`, $`\Uparrow f` and
$`\Downarrow f` are the least upper bound and greatest lower bound of the
results of $`f` on its domain (its *range*, `Fn.values`), taken in the extended
reals of {uses "number_domain"}[], which form a complete linear order;
$`\uparrow`/$`\downarrow` are $`\sqcup`/$`\sqcap` ($`\max`/$`\min`).
$`\Sigma f` and $`\Pi f` are Mathlib's finite sum and product over the domain.
These are faithful only for finite domains — Mathlib's `∑ᶠ` is
$`0` when the support is infinite, whereas the book's
$`\Sigma n : \mathit{nat}+1 \cdot 1/2^n = 1` is a convergent series; the laws
below that split a domain carry finiteness hypotheses, and nothing here claims
anything about infinite sums. Uses {uses "function_notation"}[].
:::

:::theorem "quantifier_numeric_axioms" (parent := "function_theory_core") (tags := "function, quantifier, hehner-3.1") (effort := "small") (lean := "LaPToP.FunctionTheory.Fn.sup_null, LaPToP.FunctionTheory.Fn.inf_null, LaPToP.FunctionTheory.Fn.sup_elem, LaPToP.FunctionTheory.Fn.inf_elem, LaPToP.FunctionTheory.Fn.sup_union, LaPToP.FunctionTheory.Fn.inf_union, LaPToP.FunctionTheory.Fn.sup_sols, LaPToP.FunctionTheory.Fn.inf_sols, LaPToP.FunctionTheory.Fn.sum_null, LaPToP.FunctionTheory.Fn.sum_elem, LaPToP.FunctionTheory.Fn.sum_union_add_sum_inter, LaPToP.FunctionTheory.Fn.sum_sols, LaPToP.FunctionTheory.Fn.prod_null, LaPToP.FunctionTheory.Fn.prod_elem, LaPToP.FunctionTheory.Fn.prod_union_mul_prod_inter, LaPToP.FunctionTheory.Fn.prod_sols, LaPToP.FunctionTheory.Fn.size_eq_sum_one")
The axioms of Section 3.1 for the numeric quantifiers, for bunches $`A, B, D`,
an element $`x`, a number body $`n` and a binary $`b`:
$`\Sigma v : \mathit{null} \cdot n = 0`, $`\Sigma v : x \cdot n = \langle v : x \cdot n \rangle\,x`,
$`(\Sigma v : A, B \cdot n) + (\Sigma v : A \mathbin{\lq} B \cdot n) = (\Sigma v : A \cdot n) + (\Sigma v : B \cdot n)`;
$`\Pi` likewise with $`1` and $`\times`;
$`\Downarrow v : \mathit{null} \cdot n = \infty`, $`\Downarrow v : x \cdot n = \langle v : x \cdot n \rangle\,x`,
$`\Downarrow v : A, B \cdot n = (\Downarrow v : A \cdot n) \downarrow (\Downarrow v : B \cdot n)`;
$`\Uparrow` likewise with $`-\infty` and $`\uparrow`; and the $`\S`-domain laws
$`\Sigma v : (\S v : D \cdot b) \cdot n = \Sigma v : D \cdot \mathbf{if}\ b\ \mathbf{then}\ n\ \mathbf{else}\ 0`
(and $`1`, $`\infty`, $`-\infty` for $`\Pi`, $`\Downarrow`, $`\Uparrow`). Also
Cardinality $`{\rm c\llap{/}}A = \Sigma(A \to 1)` for finite $`A`. The $`\Sigma`/$`\Pi`
splitting laws are stated for finite $`A, B`. Uses {uses "quantifier_numeric"}[],
{uses "solution_quantifier"}[] and {uses "bunch_axioms_size"}[].
:::

:::proof "quantifier_numeric_axioms"
$`\Uparrow`/$`\Downarrow`: `sSup`/`sInf` of the empty set, a singleton, a union
(`sSup_union`); the $`\S`-domain law by antisymmetry of $`\le`. $`\Sigma`/$`\Pi`:
`finsum_mem_empty`, `finsum_mem_singleton`, `finsum_mem_union_inter`, and
restriction to the support for the $`\S`-domain law.
:::

:::theorem "quantifier_laws_numeric" (parent := "function_theory_core") (tags := "function, quantifier, hehner-11.3.8") (effort := "small") (lean := "LaPToP.FunctionTheory.Fn.inf_le_apply, LaPToP.FunctionTheory.Fn.apply_le_sup, LaPToP.FunctionTheory.Fn.neg_sSup, LaPToP.FunctionTheory.Fn.neg_sup, LaPToP.FunctionTheory.Fn.neg_inf, LaPToP.FunctionTheory.Fn.sup_le_iff, LaPToP.FunctionTheory.Fn.le_inf_iff, LaPToP.FunctionTheory.Fn.inf_lt_iff, LaPToP.FunctionTheory.Fn.lt_sup_iff, LaPToP.FunctionTheory.Fn.forall_lt_of_sup_lt, LaPToP.FunctionTheory.Fn.forall_lt_of_lt_inf, LaPToP.FunctionTheory.Fn.inf_le_of_exists, LaPToP.FunctionTheory.Fn.le_sup_of_exists, LaPToP.FunctionTheory.Fn.inf_int, LaPToP.FunctionTheory.Fn.sup_int, LaPToP.FunctionTheory.Fn.le_iff_forall_le_imp, LaPToP.FunctionTheory.Fn.le_iff_forall_lt_imp, LaPToP.FunctionTheory.Fn.le_iff_forall_le_imp', LaPToP.FunctionTheory.Fn.le_iff_forall_lt_imp', LaPToP.FunctionTheory.Fn.sup_image, LaPToP.FunctionTheory.Fn.inf_image")
Laws of §11.3.8 for $`\Uparrow`, $`\Downarrow`: Specialize and Generalize
$`\Downarrow f \le f\,x \le \Uparrow f` for $`x : \square f`; Duality
$`-\Uparrow v \cdot n = \Downarrow v \cdot -n`, $`-\Downarrow v \cdot n = \Uparrow v \cdot -n`;
Bounding $`n \ge (\Uparrow v : D \cdot m) = (\forall v : D \cdot n \ge m)`,
$`n \le (\Downarrow v : D \cdot m) = (\forall v : D \cdot n \le m)`,
$`n > (\Downarrow v : D \cdot m) = (\exists v : D \cdot n > m)`,
$`n < (\Uparrow v : D \cdot m) = (\exists v : D \cdot n < m)`, and the four one-directional
forms (the book's proviso $`D \neq \mathit{null}` is not needed for these);
Extreme $`(\Downarrow n : \mathit{int} \cdot n) = -\infty`, $`(\Uparrow n : \mathit{int} \cdot n) = \infty`;
Connection $`n \le m = \forall k \cdot k \le n \Rightarrow k \le m` and its three variants;
Change of Variable $`\Uparrow r : f\,D \cdot b = \Uparrow d : D \cdot \langle r : f\,D \cdot b \rangle (f\,d)`
and dually. The distributive laws of $`+ - \times \uparrow \downarrow` over
$`\Uparrow \Downarrow` are deferred. Uses {uses "quantifier_numeric"}[] and
{uses "number_laws_order"}[].
:::

:::proof "quantifier_laws_numeric"
`le_sSup`/`sInf_le`, `sSup_le_iff`/`le_sInf_iff`, `lt_sSup_iff`/`sInf_lt_iff`;
Duality by antisymmetry using $`a \le -b = b \le -a`; Extreme by `sInf_eq_bot`/
`sSup_eq_top` with $`\lfloor r \rfloor - 1` and $`\lceil r \rceil + 1` as witnesses.
:::

:::theorem "quantifier_distributive_laws" (parent := "function_theory_core") (tags := "function, quantifier, distributive, hehner-11.3.8") (effort := "medium") (lean := "LaPToP.FunctionTheory.Fn.sup_lam_eq_iSup, LaPToP.FunctionTheory.Fn.inf_lam_eq_iInf, LaPToP.FunctionTheory.Fn.sup_sup_distrib, LaPToP.FunctionTheory.Fn.inf_inf_distrib, LaPToP.FunctionTheory.Fn.sup_inf_distrib, LaPToP.FunctionTheory.Fn.inf_sup_distrib, LaPToP.FunctionTheory.Fn.monotone_sup, LaPToP.FunctionTheory.Fn.monotone_inf, LaPToP.FunctionTheory.Fn.antitone_sup, LaPToP.FunctionTheory.Fn.antitone_inf, LaPToP.FunctionTheory.Fn.continuousAt_add_left, LaPToP.FunctionTheory.Fn.continuousAt_sub_left, LaPToP.FunctionTheory.Fn.continuousAt_sub_right, LaPToP.FunctionTheory.Fn.continuousAt_mul_left, LaPToP.FunctionTheory.Fn.add_sup, LaPToP.FunctionTheory.Fn.add_inf, LaPToP.FunctionTheory.Fn.sub_sup, LaPToP.FunctionTheory.Fn.sub_inf, LaPToP.FunctionTheory.Fn.sup_sub, LaPToP.FunctionTheory.Fn.inf_sub, LaPToP.FunctionTheory.Fn.mul_sup_of_nonneg, LaPToP.FunctionTheory.Fn.mul_inf_of_nonneg, LaPToP.FunctionTheory.Fn.mul_sup_of_nonpos, LaPToP.FunctionTheory.Fn.mul_inf_of_nonpos, LaPToP.FunctionTheory.Fn.mulLeftHom, LaPToP.FunctionTheory.Fn.mul_sum, LaPToP.FunctionTheory.Fn.prod_pow, LaPToP.FunctionTheory.Fn.realBunch, LaPToP.FunctionTheory.Fn.inf_real, LaPToP.FunctionTheory.Fn.sup_real")
The Distributive laws of the Quantifiers table (Section 11.3.8): "Distributive
— if $`D \neq \mathit{null}` and $`v` does not appear in $`n`:
$`n \uparrow (\Uparrow v : D \cdot m) = (\Uparrow v : D \cdot n \uparrow m)`,
$`n \downarrow (\Downarrow v : D \cdot m) = (\Downarrow v : D \cdot n \downarrow m)`,
$`n \uparrow (\Downarrow v : D \cdot m) = (\Downarrow v : D \cdot n \uparrow m)`,
$`n \downarrow (\Uparrow v : D \cdot m) = (\Uparrow v : D \cdot n \downarrow m)`,
$`n + (\Uparrow v : D \cdot m) = (\Uparrow v : D \cdot n + m)`,
$`n + (\Downarrow v : D \cdot m) = (\Downarrow v : D \cdot n + m)`,
$`n - (\Uparrow v : D \cdot m) = (\Downarrow v : D \cdot n - m)`,
$`n - (\Downarrow v : D \cdot m) = (\Uparrow v : D \cdot n - m)`,
$`(\Uparrow v : D \cdot m) - n = (\Uparrow v : D \cdot m - n)`,
$`(\Downarrow v : D \cdot m) - n = (\Downarrow v : D \cdot m - n)`,
$`n \geq 0 \Rightarrow n \times (\Uparrow v : D \cdot m) = (\Uparrow v : D \cdot n \times m)`,
$`n \geq 0 \Rightarrow n \times (\Downarrow v : D \cdot m) = (\Downarrow v : D \cdot n \times m)`,
$`n \leq 0 \Rightarrow n \times (\Uparrow v : D \cdot m) = (\Downarrow v : D \cdot n \times m)`,
$`n \leq 0 \Rightarrow n \times (\Downarrow v : D \cdot m) = (\Uparrow v : D \cdot n \times m)`,
$`n \times (\Sigma v : D \cdot m) = (\Sigma v : D \cdot n \times m)`,
$`(\Pi v : D \cdot m)^n = (\Pi v : D \cdot m^n)`." And the Extreme laws for the reals:
"$`(\Downarrow n : \mathit{real} \cdot n) = -\infty`, $`(\Uparrow n : \mathit{real} \cdot n) = \infty`" (the integer
versions are in {uses "quantifier_laws_numeric"}[]).

Model notes. $`\Uparrow`, $`\Downarrow` are the suprema and infima of
{uses "quantifier_numeric"}[] in the extended reals of {uses "number_domain"}[],
and $`\uparrow`, $`\downarrow` are the lattice `⊔`, `⊓`. The four lattice laws hold in the
complete linear order ($`D \neq \mathit{null}` is needed for $`n \uparrow \Uparrow` and $`n \downarrow \Downarrow`,
as the book says; the two mixed ones hold unconditionally). The ten arithmetic
laws are proved from a single principle — a monotone (antitone) operation that
is continuous on the extended reals commutes with $`\Uparrow` and $`\Downarrow` (turns them
into each other) over a nonempty domain — applied to $`n + \cdot`, $`n - \cdot`,
$`\cdot - n` and $`n \times \cdot`, for a *finite* $`n`: the book's $`n` ranges over all its
numbers, but $`\infty + (\Uparrow v : D \cdot m)` with $`\Uparrow v : D \cdot m = -\infty` is $`\infty + -\infty`,
which the book's number theory leaves undetermined, so finiteness of $`n` is the
honest side condition (the case $`n = 0` of the $`\times` laws is handled separately,
since $`0 \times \pm\infty = 0` is not continuous). $`n \times \Sigma` is proved for finite $`D` and
$`0 \leq n < \infty` (multiplication by such an $`n` is additive on the extended reals,
`mulLeftHom`), and $`(\Pi)^n` for finite $`D` and natural $`n` — the domains for which
{uses "quantifier_numeric_axioms"}[] define $`\Sigma` and $`\Pi`.
:::

:::theorem "quantifier_laws_logical" (parent := "function_theory_core") (tags := "function, quantifier, hehner-11.3.8") (effort := "small") (lean := "LaPToP.FunctionTheory.Fn.all_lam, LaPToP.FunctionTheory.Fn.ex_lam, LaPToP.FunctionTheory.Fn.all_top, LaPToP.FunctionTheory.Fn.not_ex_bot, LaPToP.FunctionTheory.Fn.all_const, LaPToP.FunctionTheory.Fn.ex_const, LaPToP.FunctionTheory.Fn.not_all, LaPToP.FunctionTheory.Fn.not_ex, LaPToP.FunctionTheory.Fn.and_all, LaPToP.FunctionTheory.Fn.and_ex, LaPToP.FunctionTheory.Fn.or_all, LaPToP.FunctionTheory.Fn.or_ex, LaPToP.FunctionTheory.Fn.imp_all, LaPToP.FunctionTheory.Fn.imp_ex, LaPToP.FunctionTheory.Fn.ex_imp, LaPToP.FunctionTheory.Fn.all_imp, LaPToP.FunctionTheory.Fn.apply_and_ex, LaPToP.FunctionTheory.Fn.apply_or_all, LaPToP.FunctionTheory.Fn.apply_and_all, LaPToP.FunctionTheory.Fn.apply_or_ex, LaPToP.FunctionTheory.Fn.all_and, LaPToP.FunctionTheory.Fn.ex_and, LaPToP.FunctionTheory.Fn.all_or, LaPToP.FunctionTheory.Fn.ex_or, LaPToP.FunctionTheory.Fn.all_imp_all, LaPToP.FunctionTheory.Fn.all_imp_ex, LaPToP.FunctionTheory.Fn.all_beq_all, LaPToP.FunctionTheory.Fn.all_beq_ex, LaPToP.FunctionTheory.Fn.forall_forall_comm, LaPToP.FunctionTheory.Fn.exists_exists_comm, LaPToP.FunctionTheory.Fn.exists_forall_imp, LaPToP.FunctionTheory.Fn.forall_exists_iff_exists_fun, LaPToP.FunctionTheory.Fn.all_image, LaPToP.FunctionTheory.Fn.ex_image")
Laws of §11.3.8 for $`\forall`, $`\exists`: Identity $`\forall v \cdot \top`, $`\neg\exists v \cdot \bot`;
Idempotent $`\forall v : D \cdot b = b`, $`\exists v : D \cdot b = b` for $`D \neq \mathit{null}` and $`v` not in $`b`;
Duality $`\neg\forall v \cdot b = \exists v \cdot \neg b`, $`\neg\exists v \cdot b = \forall v \cdot \neg b`;
Distributive $`a \land \forall v : D \cdot b = \forall v : D \cdot a \land b` and the five
companions with $`\land \lor \Rightarrow` over $`\forall \exists`; Antidistributive
$`a \Leftarrow \exists v : D \cdot b = \forall v : D \cdot a \Leftarrow b`,
$`a \Leftarrow \forall v : D \cdot b = \exists v : D \cdot a \Leftarrow b`
(the book's proviso $`D \neq \mathit{null}` is carried exactly where it is needed);
Absorption (four laws, for $`x : D`); Splitting (eight laws, e.g.
$`\forall v \cdot a \land b = (\forall v \cdot a) \land (\forall v \cdot b)`,
$`\exists v \cdot a \land b \Rightarrow (\exists v \cdot a) \land (\exists v \cdot b)`);
Commutative $`\forall v \cdot \forall w \cdot b = \forall w \cdot \forall v \cdot b` and for $`\exists`;
Semicommutative $`\exists v \cdot \forall w \cdot b \Rightarrow \forall w \cdot \exists v \cdot b` and
$`\forall x \cdot \exists y \cdot p\,x\,y = \exists f \cdot \forall x \cdot p\,x\,(f\,x)`; Change of Variable.
Since $`\forall p` is a proposition here, nested quantifications are written as
iterated bounded quantifiers. Uses {uses "quantifier_forall_exists"}[] and
{uses "binary_laws_algebra"}[].
:::

:::proof "quantifier_laws_logical"
Unfold $`\forall\langle v : D \cdot b \rangle` to $`\forall v \in D,\ b\,v = \top` and reason
propositionally; the nonempty domain supplies a witness where needed; the choice
function of the last Semicommutative law is `Classical.choose`.
:::

:::theorem "quantifier_laws_solution" (parent := "function_theory_core") (tags := "function, quantifier, hehner-11.3.8") (effort := "small") (lean := "LaPToP.FunctionTheory.Fn.sols_lam, LaPToP.FunctionTheory.Fn.all_sols, LaPToP.FunctionTheory.Fn.ex_sols, LaPToP.FunctionTheory.Fn.sols_sols, LaPToP.FunctionTheory.Fn.sols_inter, LaPToP.FunctionTheory.Fn.subset_iff_all, LaPToP.FunctionTheory.Fn.subset_iff_forall_exists, LaPToP.FunctionTheory.Fn.image_subset_image_iff_forall_exists, LaPToP.FunctionTheory.Fn.sols_top, LaPToP.FunctionTheory.Fn.sols_bot, LaPToP.FunctionTheory.Fn.sols_subset_sols, LaPToP.FunctionTheory.Fn.sols_union_sols, LaPToP.FunctionTheory.Fn.sols_inter_sols, LaPToP.FunctionTheory.Fn.all_iff_sols_eq_domain, LaPToP.FunctionTheory.Fn.ex_iff_sols_ne_null, LaPToP.FunctionTheory.Fn.all_of_subset, LaPToP.FunctionTheory.Fn.ex_of_subset, LaPToP.FunctionTheory.Fn.all_mem_imp, LaPToP.FunctionTheory.Fn.ex_mem_and")
Laws of §11.3.8 for the solution quantifier and for domains: the $`\S`-domain laws
$`\forall v : (\S v : D \cdot b) \cdot c = \forall v : D \cdot b \Rightarrow c`,
$`\exists v : (\S v : D \cdot b) \cdot c = \exists v : D \cdot b \land c`,
$`\S v : (\S v : D \cdot b) \cdot c = \S v : D \cdot b \land c`,
$`\S v : A \mathbin{\lq} B \cdot b = (\S v : A \cdot b) \mathbin{\lq} (\S v : B \cdot b)`;
Solution $`\S v : D \cdot \top = D`, $`\S v : D \cdot \bot = \mathit{null}`,
$`(\S v \cdot b) : (\S v \cdot c) = \forall v \cdot b \Rightarrow c`,
$`(\S v \cdot b), (\S v \cdot c) = \S v \cdot b \lor c`, $`(\S v \cdot b) \mathbin{\lq} (\S v \cdot c) = \S v \cdot b \land c`,
$`\forall f = ((\S f) = (\square f))`, $`\exists f = ((\S f) \neq \mathit{null})`;
Inclusion $`A : B = \forall x : A \cdot x : B`; Bunch-Element Conversion
$`A : B = \forall a : A \cdot \exists b : B \cdot a = b` and
$`f\,A : g\,B = \forall a : A \cdot \exists b : B \cdot f\,a = g\,b`; Domain Change
$`A : B \Rightarrow (\forall v : A \cdot b) \Leftarrow (\forall v : B \cdot b)`,
$`A : B \Rightarrow (\exists v : A \cdot b) \Rightarrow (\exists v : B \cdot b)`,
$`\forall v : A \cdot v : B \Rightarrow p = \forall v : A \mathbin{\lq} B \cdot p`,
$`\exists v : A \cdot v : B \land p = \exists v : A \mathbin{\lq} B \cdot p`.
Uses {uses "solution_quantifier"}[], {uses "quantifier_forall_exists"}[] and
{uses "bunch_axioms_inclusion"}[].
:::

:::proof "quantifier_laws_solution"
Unfold $`\S\langle v : D \cdot b \rangle` to $`\{v \mid v \in D \land b\,v = \top\}` and
reason by extensionality and propositional logic.
:::

:::definition "function_on_bunches" (parent := "function_theory_core") (lean := "LaPToP.FunctionTheory.Fn.applyBunch, LaPToP.FunctionTheory.Fn.applyFns, LaPToP.FunctionTheory.Fn.applyBunch_null, LaPToP.FunctionTheory.Fn.applyBunch_union, LaPToP.FunctionTheory.Fn.applyBunch_elem, LaPToP.FunctionTheory.Fn.values_eq_applyBunch_domain, LaPToP.FunctionTheory.Fn.applyBunch_sols, LaPToP.FunctionTheory.Fn.applyFns_union, LaPToP.FunctionTheory.Fn.applyFns_elem, LaPToP.FunctionTheory.Fn.double, LaPToP.FunctionTheory.Fn.double_two_three, LaPToP.FunctionTheory.Fn.apply_ite, LaPToP.FunctionTheory.Fn.ite_apply")
"A union of functions applied to an argument gives the union of the results",
$`(f, g)\,x = f\,x, g\,x`, and "a function applied to a union of arguments gives
the union of the results": $`f\,\mathit{null} = \mathit{null}`, $`f\,(A, B) = f\,A, f\,B`,
$`f\,(\S g) = \S y : f\,(\square g) \cdot \exists x : \square g \cdot f\,x = y \land g\,x`.
"So function application distributes over bunch union. The range of function
$`f` is $`f\,(\square f)`." In Lean `Fn.applyBunch f A` is the bunch of results of
$`f` on $`A : \square f`, and `Fn.applyFns F x` applies a bunch of functions; the
book's example $`\mathit{double}\,(2, 3) = 4, 6` is checked. Uses
{uses "function_axioms"}[] and {uses "solution_quantifier"}[].
The Reference chapter's $`f\,(\mathbf{if}\ b\ \mathbf{then}\ x\ \mathbf{else}\ y) = \mathbf{if}\ b\ \mathbf{then}\ f\,x\ \mathbf{else}\ f\,y` and
$`(\mathbf{if}\ b\ \mathbf{then}\ f\ \mathbf{else}\ g)\,x = \mathbf{if}\ b\ \mathbf{then}\ f\,x\ \mathbf{else}\ g\,x` (§11.3.7) are `apply_ite` and
`ite_apply`, for arguments in the domains. Not modelled: a bunch of functions applied as a
function — $`\square(f, g) = \square f \mathbin{\lq} \square g`, $`(f, g)\,x = f\,x, g\,x` and the function intersection
$`f \mathbin{\lq} g` (`applyFns` gives the bunch of results of a bunch of functions, which is the
first of these read as a bunch equation).
:::

:::definition "function_totality" (parent := "function_theory_core") (lean := "LaPToP.FunctionTheory.Fn.Total, LaPToP.FunctionTheory.Fn.Partial, LaPToP.FunctionTheory.Fn.Deterministic, LaPToP.FunctionTheory.Fn.Nondeterministic, LaPToP.FunctionTheory.Fn.toBunch, LaPToP.FunctionTheory.Fn.total_toBunch, LaPToP.FunctionTheory.Fn.deterministic_toBunch, LaPToP.FunctionTheory.Fn.pair, LaPToP.FunctionTheory.Fn.pair_three, LaPToP.FunctionTheory.Fn.total_pair, LaPToP.FunctionTheory.Fn.nondeterministic_pair, LaPToP.FunctionTheory.Fn.below, LaPToP.FunctionTheory.Fn.partial_below, LaPToP.FunctionTheory.Fn.nondeterministic_below")
For a function whose body is a bunch (`Fn α (Bunch β)`): "a function that
sometimes produces no result is called *partial*; ... always produces at least
one result, *total*; ... always produces at most one result, *deterministic*;
... sometimes produces more than one result, *nondeterministic*". An ordinary
function is viewed as a bunch-valued one with elementary results (`Fn.toBunch`),
and is total and deterministic. The book's examples
$`\langle n : \mathit{nat} \cdot n, n+1 \rangle` (total, nondeterministic; it maps
$`3` to $`3, 4`) and $`\langle n : \mathit{nat} \cdot 0,..n \rangle` ("both partial
and nondeterministic") are verified. Uses {uses "function_on_bunches"}[] and
{uses "bunch_interval"}[].
:::

:::theorem "function_inclusion" (parent := "function_theory_core") (tags := "function, hehner-3.2") (effort := "small") (lean := "LaPToP.FunctionTheory.Fn.Incl, LaPToP.FunctionTheory.Fn.arrowB, LaPToP.FunctionTheory.Fn.arrowSet, LaPToP.FunctionTheory.Fn.eq_iff, LaPToP.FunctionTheory.Fn.incl_antisymm, LaPToP.FunctionTheory.Fn.incl_refl, LaPToP.FunctionTheory.Fn.incl_arrowB, LaPToP.FunctionTheory.Fn.mem_arrowSet_iff, LaPToP.FunctionTheory.Fn.incl_toBunch_arrowB_iff, LaPToP.FunctionTheory.Fn.incl_arrowB_null, LaPToP.FunctionTheory.Fn.arrowB_incl_arrowB, LaPToP.FunctionTheory.Fn.arrowB_union_inter_incl, LaPToP.FunctionTheory.Fn.arrowB_incl_inter_union, LaPToP.FunctionTheory.Fn.arrowB_union_eq_orElse, LaPToP.FunctionTheory.Fn.suc, LaPToP.FunctionTheory.Fn.suc_three, LaPToP.FunctionTheory.Fn.suc_incl, LaPToP.FunctionTheory.Fn.even_incl, LaPToP.FunctionTheory.Fn.odd_incl, LaPToP.FunctionTheory.Fn.divides_incl")
The Function Inclusion Law
$`f : g = \square f :: \square g \land \forall x : \square g \cdot f\,x : g\,x`, and, "using it
both ways round", function equality
$`f = g = \square f = \square g \land \forall x : \square f \cdot f\,x = g\,x`. $`A \to B`
abbreviates $`\langle n : A \cdot B \rangle`, "a nondeterministic function whose
result, for each element of its domain $`A`, is the bunch $`B`"; "it is also the
bunch of all functions whose domain includes $`A` and whose result is included
in $`B`" — both readings are defined (`Fn.arrowB`, `Fn.arrowSet`) and shown to
agree. Laws: $`f : A \to B = \square f :: A \land f\,A : B`; the Arrow laws of §11.3.7
$`f : \mathit{null} \to A`, $`(A, B) \to (C \mathbin{\lq} D) : A \to C : (A \mathbin{\lq} B) \to (C, D)`,
$`(A, B) \to C = A \to C \mid B \to C`, and
$`A \to B : C \to D = A :: C \land B : D` *corrected*: the second conjunct is
needed only when $`C \neq \mathit{null}` (for $`C = \mathit{null}` the inclusion holds
vacuously, since $`f : \mathit{null} \to D` for every $`f`). The book's worked
inclusions $`\mathit{suc} : \mathit{nat} \to \mathit{nat}`, $`\mathit{even} : \mathit{int} \to \mathit{bin}`,
$`\mathit{odd} : \mathit{int} \to \mathit{bin}`, $`\mathit{divides} : (\mathit{nat}+1) \to \mathit{int} \to \mathit{bin}`
are proved. Uses {uses "function_totality"}[], {uses "selective_union"}[],
{uses "predicates_relations"}[] and {uses "bunch_nat_axioms"}[].
Not modelled: $`(A, B) \to C = A \to C \mathbin{\lq} B \to C` (§11.3.7), the function intersection
$`\mathbin{\lq}`; the $`\mid` form is `arrowB_union_eq_orElse`.
:::

:::proof "function_inclusion"
Unfolding; equality via `Fn.ext`; $`\mathit{suc} : \mathit{nat} \to \mathit{nat}` by the
construction axiom $`0 \le n \Rightarrow 0 \le n+1`.
:::

:::theorem "list_as_function" (parent := "function_theory_core") (tags := "function, list, hehner-3.3") (effort := "small") (lean := "LaPToP.DataStructures.HList.toFn, LaPToP.DataStructures.HList.toFn_apply, LaPToP.DataStructures.HList.toFn_domain, LaPToP.DataStructures.HList.toFn_size, LaPToP.DataStructures.HList.toFn_comp, LaPToP.DataStructures.HList.toFn_inj, LaPToP.DataStructures.HList.sum_toFn, LaPToP.DataStructures.HList.map, LaPToP.DataStructures.HList.suc_map_example, LaPToP.DataStructures.HList.neg_map_example, LaPToP.DataStructures.HList.orElse_arrow_toFn, LaPToP.DataStructures.HList.orElse_arrow_example, LaPToP.DataStructures.HList.toFn_applyBunch, LaPToP.DataStructures.HList.comp_pack")
"A list $`L` has much in common with the function $`\langle n : \square L \cdot L\,n \rangle`":
list indexing is function application $`L\,m = \langle n : \square L \cdot L\,n \rangle\,m`;
list composition coincides with function composition
$`L\,M\,m = \langle n : \square L \cdot L\,n \rangle\,\langle n : \square M \cdot M\,n \rangle\,m`;
list domain and size are function domain and size; list equality is function
equality; quantifiers apply to lists, $`\Sigma L = \Sigma n : \square L \cdot L\,n`.
Functions compose with lists ($`\mathit{suc}\,[3; 5; 2] = [4; 6; 3]`,
$`-[3; 5; 2] = [-3; -5; -2]`), and lists and functions mix in a selective union:
$`1 \to 21 \mid [10; 11; 12] = [10; 21; 12]`, in general
$`n \to i \mid L = (n \to i \mid L)` for an index $`n` of $`L`. Uses
{uses "list_packaging"}[], {uses "function_axioms"}[], {uses "selective_union"}[]
and {uses "quantifier_numeric"}[].
The Reference chapter's $`L\,\{A\} = \{L\,A\}` and $`L\,[S] = [L\,S]` (§11.3.6) are `toFn_applyBunch`
(a list applied to a bunch of indices gives the bunch of items at those indices) and `comp_pack`.
:::

:::proof "list_as_function"
`HList.toFn L := ⟨n: ☐L· L n⟩`; the coincidences are `rfl` or `Fn.ext`; size via
`Finset.range`; $`\Sigma L` via `Fin.sum_univ_getElem`; the selective-union law by
extensionality and `List.getElem?_set_self`/`_ne`.
:::

:::theorem "limits" (parent := "function_theory_core") (tags := "function, limits, reals, hehner-3.4") (effort := "medium") (lean := "LaPToP.FunctionTheory.Limits.Seq, LaPToP.FunctionTheory.Limits.lowerLimit, LaPToP.FunctionTheory.Limits.upperLimit, LaPToP.FunctionTheory.Limits.IsLimit, LaPToP.FunctionTheory.Limits.lowerLimit_eq_liminf, LaPToP.FunctionTheory.Limits.upperLimit_eq_limsup, LaPToP.FunctionTheory.Limits.lowerLimit_le_upperLimit, LaPToP.FunctionTheory.Limits.exists_isLimit, LaPToP.FunctionTheory.Limits.isLimit_iff_of_eq, LaPToP.FunctionTheory.Limits.isLimit_iff_of_tendsto, LaPToP.FunctionTheory.Limits.inf_le_isLimit_le_sup, LaPToP.FunctionTheory.Limits.sup_toFn, LaPToP.FunctionTheory.Limits.inf_toFn, LaPToP.FunctionTheory.Limits.isLimit_iff_of_monotone, LaPToP.FunctionTheory.Limits.isLimit_iff_of_antitone, LaPToP.FunctionTheory.Limits.invSucc, LaPToP.FunctionTheory.Limits.isLimit_invSucc_iff, LaPToP.FunctionTheory.Limits.altSign, LaPToP.FunctionTheory.Limits.altSign_even, LaPToP.FunctionTheory.Limits.altSign_odd, LaPToP.FunctionTheory.Limits.neg_one_le_one', LaPToP.FunctionTheory.Limits.altSign_bounds, LaPToP.FunctionTheory.Limits.lowerLimit_altSign, LaPToP.FunctionTheory.Limits.upperLimit_altSign, LaPToP.FunctionTheory.Limits.isLimit_altSign_iff, LaPToP.FunctionTheory.Limits.isLimit_altSign_neg_one, LaPToP.FunctionTheory.Limits.isLimit_altSign_one, LaPToP.FunctionTheory.Limits.natSeq, LaPToP.FunctionTheory.Limits.isLimit_natSeq_iff, LaPToP.FunctionTheory.Limits.IsPredLimit, LaPToP.FunctionTheory.Limits.exists_forall_add_iff_eventually, LaPToP.FunctionTheory.Limits.forall_exists_add_iff_frequently, LaPToP.FunctionTheory.Limits.exists_isPredLimit, LaPToP.FunctionTheory.Limits.isPredLimit_of_eventually, LaPToP.FunctionTheory.Limits.not_isPredLimit_of_eventually_not, LaPToP.FunctionTheory.Limits.not_isPredLimit_invSucc_eq_zero, LaPToP.FunctionTheory.Limits.ratApprox, LaPToP.FunctionTheory.Limits.ratApprox_tendsto, LaPToP.FunctionTheory.Limits.exists_rat_seq_isLimit, LaPToP.FunctionTheory.Limits.real_eq_xreal_remove")
"Let $`f : \mathit{nat} \to \mathit{rat}` so that $`f\,0;\ f\,1;\ f\,2;\ \ldots` is a sequence of
rationals. The limit of the function (limit of the sequence) is expressed as
$`\Updownarrow f`. ... We define the limit quantifier $`\Updownarrow` by the following Limit
Axiom: $`(\Uparrow m \cdot \Downarrow n \cdot f\,(m{+}n)) \leq \Updownarrow f \leq (\Downarrow m \cdot \Uparrow n \cdot f\,(m{+}n))` with
all domains being $`\mathit{nat}`. This axiom gives a lower bound (limit inferior) and
an upper bound (limit superior) for $`\Updownarrow f`. When those bounds are equal, the
Limit Axiom tells us $`\Updownarrow f` exactly. For example, $`\Updownarrow n \cdot 1/(n{+}1) = 0`. For
some functions, the Limit Axiom tells us a little less. For example,
$`-1 \leq (\Updownarrow n \cdot (-1)^n) \leq 1`. In general, $`\Downarrow f \leq \Updownarrow f \leq \Uparrow f`. For
monotonic (nondecreasing) $`f`, $`\Updownarrow f = \Uparrow f`. For antimonotonic (nonincreasing)
$`f`, $`\Updownarrow f = \Downarrow f`. We define the extended real numbers as the limits of all
functions with domain at least $`\mathit{nat}` and range at most $`\mathit{rat}`. And we define
the reals as the extended reals without $`\infty` and $`-\infty`.
$`x : \mathit{xreal} = \exists f : \mathit{nat} \to \mathit{rat} \cdot x = \Updownarrow f`, $`\mathit{real} = \mathit{xreal} -, (\infty, -\infty)`.
... Let $`p : \mathit{nat} \to \mathit{bin}` so that $`p` is a predicate and $`p\,0;\ p\,1;\ p\,2;\ \ldots` is
a sequence of binary expressions. The limit of predicate $`p` is defined by the
axiom $`\exists m \cdot \forall n \cdot p\,(m{+}n) \Rightarrow \Updownarrow p \Rightarrow \forall m \cdot \exists n \cdot p\,(m{+}n)` with all
domains being $`\mathit{nat}`. ... $`\exists m \cdot \forall i \cdot i \geq m \Rightarrow p\,i \Rightarrow \Updownarrow p`,
$`\exists m \cdot \forall i \cdot i \geq m \Rightarrow \lnot p\,i \Rightarrow \lnot \Updownarrow p`. ... For example,
$`\lnot \Updownarrow n \cdot 1/(n{+}1) = 0`. Even though the limit of $`1/(n{+}1)` is $`0`, the limit of
$`1/(n{+}1) = 0` is $`\bot`. If, for some particular assignment of values to variables,
the sentence never settles on one binary value, then the axiom does not
determine the value of $`\Updownarrow p` for that assignment of values." The Reference
chapter adds $`\Updownarrow n \cdot n = \infty` (Section 11.3.9).

Model notes. The book's $`\Updownarrow f` is underdetermined — the Limit Axiom only bounds
it — and the formalization keeps it so: a sequence is $`u : \mathbb{N} \to \mathit{xreal}`
(the extended reals of {uses "number_domain"}[], so that $`\Uparrow`, $`\Downarrow` of
{uses "quantifier_numeric"}[] always exist); `lowerLimit u` and `upperLimit u`
are the two bounds of the axiom, literally $`\Uparrow m \cdot \Downarrow n \cdot u\,(m{+}n)` and
$`\Downarrow m \cdot \Uparrow n \cdot u\,(m{+}n)` (`sup_toFn`/`inf_toFn` identify $`\Uparrow`, $`\Downarrow` of the book's
function $`\langle n : \mathit{nat} \cdot f\,n \rangle` with the suprema and infima used); `IsLimit u L`
says $`L` satisfies the axiom. The bounds are Mathlib's `liminf`/`limsup` along
`atTop`, so a value always exists, the bounds are consistent, and the value is
unique exactly when they agree — in particular for convergent sequences
(`isLimit_iff_of_tendsto`). Proved as stated: $`\Downarrow f \leq \Updownarrow f \leq \Uparrow f`
({uses "quantifier_laws_numeric"}[]); monotone ⇒ $`\Updownarrow f = \Uparrow f`, antitone ⇒
$`\Updownarrow f = \Downarrow f`; every value of $`\Updownarrow n \cdot 1/(n{+}1)` is $`0`; the values of
$`\Updownarrow n \cdot (-1)^n` are exactly the numbers of $`[-1, 1]`, so $`-1` and $`1` both are values
("a little less"); every value of $`\Updownarrow n \cdot n` is $`\infty`. For predicates,
`IsPredLimit p b` places $`b` between "eventually $`p`" and "frequently $`p`"
(the book's two bounds, proved equal to Mathlib's `∀ᶠ`/`∃ᶠ` along `atTop`), with the
two one-sided forms and the example that every value of
$`\Updownarrow n \cdot (1/(n{+}1) = 0)` is $`\bot`. Every extended real is a value of the limit of a
rational sequence ($`n`, $`-n`, and $`\lfloor x(n{+}1) \rfloor/(n{+}1)` for a real $`x`), and the reals
are the extended reals other than $`\pm\infty`. Not formalized: that
$`\Updownarrow n \cdot (1 + 1/n)^n` is $`e`.
:::
