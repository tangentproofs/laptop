import Verso
import VersoManual
import VersoBlueprint
import LaPToP.FunctionTheory.Functions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Function Theory" =>

:::group "function_theory_core"
Functions with an explicit domain, selective union, predicates and relations,
and the quantifiers built on them: Hehner's Chapter 3, the prerequisite for the
specifications and refinements of Program Theory. The formal counterpart is the
Lean module `LaPToP.FunctionTheory.Functions`.
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

:::definition "selective_union" (parent := "function_theory_core") (lean := "LaPToP.FunctionTheory.Fn.orElse, LaPToP.FunctionTheory.Fn.domain_orElse, LaPToP.FunctionTheory.Fn.apply_orElse, LaPToP.FunctionTheory.Fn.apply_orElse_left, LaPToP.FunctionTheory.Fn.apply_orElse_right")
$`f \mid g`, "$`f` otherwise $`g`", "behaves like $`f` when applied to an
argument in the domain of $`f`, and otherwise behaves like $`g`". Its axioms are
$`\square(f \mid g) = \square f, \square g` and
$`(f \mid g)\,x = \mathbf{if}\ x : \square f\ \mathbf{then}\ f\,x\ \mathbf{else}\ g\,x`,
with the two cases spelled out as corollaries. Uses {uses "function_notation"}[]
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
