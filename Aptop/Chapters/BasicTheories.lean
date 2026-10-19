import Verso
import VersoManual
import VersoBlueprint
import Aptop.BasicTheories.Bunch
import Aptop.BasicTheories.Numbers
import Aptop.BasicTheories.NumberLaws
import Aptop.BasicTheories.Calculation
import Aptop.BasicTheories.GenericLaws
import Aptop.DataStructures.Lists

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Basic Theories" =>

:::group "basic_theories_core"
Basic theories: numbers, bunches, sets, and the calculation style that
underpins later program reasoning in Aptop. The bunch and set material is
Hehner's Sections 2.0 and 2.1; the formal counterpart lives in the Lean module
`Aptop.BasicTheories.Bunch` (axioms and laws) and
`Aptop.BasicTheories.Numbers` (named bunches, the interval, distribution).
The number laws of Section 1.1 (reference §11.3.2) are in
`Aptop.BasicTheories.NumberLaws`, and the calculation style of Section 1.0.1
(`calc`, the Law of Portation) in `Aptop.BasicTheories.Calculation`. The
Generic laws of the Reference chapter (§11.3.0: equality, `if`, and the order
and `↑ ↓` laws for any linear order) are in `Aptop.BasicTheories.GenericLaws`;
the survey of all Reference-chapter law tables against the Lean theorems is
`.sci/laws-survey.md` in the repository.
:::

:::definition "bunch_vs_set" (parent := "basic_theories_core") (lean := "Aptop.BasicTheories.Bunch, Aptop.BasicTheories.HSet")
Hehner distinguishes *bunches* (unordered, uncontained collections that may be
used as types/domains) from *sets* (a bunch packaged into a single value, so
that it can be an element of another collection). "All sets are elements; not
all bunches are elements; that is the difference between sets and bunches."

Lean is typed, so the formalization stratifies Hehner's untyped world: a bunch
of elements of type $`\alpha` is a predicate on $`\alpha`, i.e. a Mathlib
`Set α` (`Bunch α`), and a Hehner set is a one-field structure `HSet α`
wrapping a bunch. The book's operators translate as
$`A, B \mapsto A \cup B`, $`A \mathbin{\lq} B \mapsto A \cap B`, $`A \mathbin{-\!,} B \mapsto A \setminus B`,
$`A : B \mapsto A \subseteq B`, $`x : A \mapsto x \in A`, $`\mathit{null} \mapsto \varnothing`.
Because bunches are sets in Lean, the *axioms* of Bunch Theory become *theorems*.
:::

:::definition "bunch_primitives" (parent := "basic_theories_core") (lean := "Aptop.BasicTheories.Bunch.null, Aptop.BasicTheories.Bunch.elem, Aptop.BasicTheories.Bunch.size")
The empty bunch $`\mathit{null}`, the elementary bunch of a single element
$`x` (written just $`x` in the book, `{x}` in Lean), and the size
$`{\rm c\llap{/}}A` of a bunch. Size takes values in the extended naturals so that
$`{\rm c\llap{/}}\,\mathit{nat} = \infty` as in the book. These are the primitives used by
{uses "bunch_vs_set"}[].
:::

:::theorem "bunch_axioms_membership" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.elem_subset_elem, Aptop.BasicTheories.Bunch.elem_subset_iff, Aptop.BasicTheories.Bunch.mem_union, Aptop.BasicTheories.Bunch.mem_inter, Aptop.BasicTheories.Bunch.mem_remove")
For elements $`x, y` and bunches $`A, B`:
$`x : y = (x = y)` (elementary),
$`x : A, B = x : A \lor x : B` (union),
$`x : A \mathbin{\lq} B = x : A \land x : B` (intersection),
$`x : A \mathbin{-\!,} B = x : A \land \neg x : B` (removal).
In the typed model the elementary axiom reads $`\{x\} \subseteq \{y\} \iff x = y`,
and a bridging lemma identifies $`\{x\} \subseteq A` with $`x \in A`.
Uses {uses "bunch_primitives"}[].
:::

:::proof "bunch_axioms_membership"
Each is the corresponding Mathlib membership lemma for `Set`.
:::

:::theorem "bunch_axioms_algebra" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.union_self, Aptop.BasicTheories.Bunch.union_comm, Aptop.BasicTheories.Bunch.union_assoc, Aptop.BasicTheories.Bunch.inter_self, Aptop.BasicTheories.Bunch.inter_comm, Aptop.BasicTheories.Bunch.inter_assoc, Aptop.BasicTheories.Bunch.remove_union, Aptop.BasicTheories.Bunch.remove_remove, Aptop.BasicTheories.Bunch.inter_remove, Aptop.BasicTheories.Bunch.inter_remove_comm, Aptop.BasicTheories.Bunch.union_inter_distrib, Aptop.BasicTheories.Bunch.inter_union_distrib")
For bunches $`A, B, C`: union and intersection are idempotent, symmetric and
associative; removal satisfies
$`A \mathbin{-\!,} (B, C) = (A \mathbin{-\!,} B) \mathbin{-\!,} C = (A \mathbin{-\!,} B) \mathbin{\lq} (A \mathbin{-\!,} C)` (union removal) and
$`A \mathbin{\lq} (B \mathbin{-\!,} C) = (A \mathbin{\lq} B) \mathbin{-\!,} C = B \mathbin{\lq} (A \mathbin{-\!,} C)` (intersection removal); and
$`A, (B \mathbin{\lq} C) = (A, B) \mathbin{\lq} (A, C)`, $`A \mathbin{\lq} (B, C) = (A \mathbin{\lq} B), (A \mathbin{\lq} C)` (distributivity).
Uses {uses "bunch_vs_set"}[].
:::

:::proof "bunch_axioms_algebra"
Lattice and set-difference identities for `Set`; the two removal laws without a
direct Mathlib name are settled by extensionality and propositional reasoning.
:::

:::theorem "bunch_axioms_inclusion" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.subset_inter_iff, Aptop.BasicTheories.Bunch.union_subset_iff, Aptop.BasicTheories.Bunch.subset_union, Aptop.BasicTheories.Bunch.inter_subset, Aptop.BasicTheories.Bunch.subset_refl, Aptop.BasicTheories.Bunch.subset_antisymm_iff, Aptop.BasicTheories.Bunch.subset_trans, Aptop.BasicTheories.Bunch.superset_iff")
For bunches $`A, B, C`:
$`A : B \mathbin{\lq} C = A : B \land A : C` (distributivity),
$`A, B : C = A : C \land B : C` (antidistributivity),
$`A : A, B` (generalization), $`A \mathbin{\lq} B : A` (specialization),
$`A : A` (reflexivity), $`A : B \land B : A = (A = B)` (antisymmetry),
$`A : B \land B : C \Rightarrow A : C` (transitivity), and
$`A :: B = B : A` (mirror).
Uses {uses "bunch_vs_set"}[].
:::

:::proof "bunch_axioms_inclusion"
Inclusion is `Set` subset, a partial order with the lattice structure of union
and intersection; each law is the matching Mathlib fact.
:::

:::theorem "bunch_axioms_size" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.size_elem, Aptop.BasicTheories.Bunch.size_union_add_size_inter, Aptop.BasicTheories.Bunch.not_mem_iff_size_inter_elem, Aptop.BasicTheories.Bunch.size_le_size")
For an element $`x` and bunches $`A, B`:
$`{\rm c\llap{/}}x = 1`, $`{\rm c\llap{/}}(A, B) + {\rm c\llap{/}}(A \mathbin{\lq} B) = {\rm c\llap{/}}A + {\rm c\llap{/}}B`,
$`\neg x : A = ({\rm c\llap{/}}(A \mathbin{\lq} x) = 0)`, and $`A : B \Rightarrow {\rm c\llap{/}}A \le {\rm c\llap{/}}B`.
Uses {uses "bunch_primitives"}[].
:::

:::proof "bunch_axioms_size"
Size is Mathlib's `Set.encard`, valued in $`\mathbb{N}_\infty`; the laws are
`encard_singleton`, `encard_union_add_encard_inter`, `encard_eq_zero`, and
monotonicity of `encard`. No finiteness hypotheses are needed.
:::

:::theorem "bunch_null_laws" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.null_subset, Aptop.BasicTheories.Bunch.size_eq_zero_iff, Aptop.BasicTheories.Bunch.union_null, Aptop.BasicTheories.Bunch.inter_null, Aptop.BasicTheories.Bunch.size_null")
The empty bunch is defined in the book by $`\mathit{null} : A` and
$`{\rm c\llap{/}}A = 0 = (A = \mathit{null})`, giving $`A, \mathit{null} = A` (identity),
$`A \mathbin{\lq} \mathit{null} = \mathit{null}` (base), and $`{\rm c\llap{/}}\,\mathit{null} = 0` (size).
Uses {uses "bunch_primitives"}[] and {uses "bunch_axioms_size"}[].
:::

:::proof "bunch_null_laws"
$`\mathit{null}` is the empty set; all five are standard `Set` and `encard` facts.
:::

:::theorem "bunch_derived_laws" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.union_inter_self, Aptop.BasicTheories.Bunch.inter_union_self, Aptop.BasicTheories.Bunch.union_subset_union_right, Aptop.BasicTheories.Bunch.inter_subset_inter_right, Aptop.BasicTheories.Bunch.subset_iff_union_eq, Aptop.BasicTheories.Bunch.union_eq_iff_inter_eq, Aptop.BasicTheories.Bunch.union_union_distrib, Aptop.BasicTheories.Bunch.inter_inter_distrib, Aptop.BasicTheories.Bunch.union_subset_union, Aptop.BasicTheories.Bunch.inter_subset_inter, Aptop.BasicTheories.Bunch.union_remove")
Laws Hehner lists as provable from the axioms:
$`A, (A \mathbin{\lq} B) = A` and $`A \mathbin{\lq} (A, B) = A` (absorption);
$`A : B \Rightarrow C, A : C, B` and $`A : B \Rightarrow C \mathbin{\lq} A : C \mathbin{\lq} B` (monotonicity);
$`A : B = (A, B = B) = (A = A \mathbin{\lq} B)` (inclusion);
$`A, (B, C) = (A, B), (A, C)` and $`A \mathbin{\lq} (B \mathbin{\lq} C) = (A \mathbin{\lq} B) \mathbin{\lq} (A \mathbin{\lq} C)` (distributivity);
$`A : B \land C : D \Rightarrow A, C : B, D` and
$`A : B \land C : D \Rightarrow A \mathbin{\lq} C : B \mathbin{\lq} D` (conflation).
Uses {uses "bunch_axioms_algebra"}[] and {uses "bunch_axioms_inclusion"}[].
The third union-removal law of the Reference chapter (§11.3.3),
$`(A, B) -, C = A -, C,\ B -, C`, is `union_remove`.
:::

:::proof "bunch_derived_laws"
In Lean these are proved directly from Mathlib's lattice lemmas rather than by
calculation from the axiom nodes; the dependency edges record the book's
derivation.
:::

:::definition "bunch_named_bunches" (parent := "basic_theories_core") (lean := "Aptop.BasicTheories.Bunch.bin, Aptop.BasicTheories.Bunch.nat, Aptop.BasicTheories.Bunch.int, Aptop.BasicTheories.XInt, Aptop.BasicTheories.Bunch.xnat, Aptop.BasicTheories.Bunch.xint, Aptop.BasicTheories.Bunch.toXInt")
Hehner's useful bunches: $`\mathit{bin} = \top, \bot`, $`\mathit{nat} = 0, 1, 2, \ldots`,
$`\mathit{int} = \ldots, -1, 0, 1, \ldots`, and the extended versions
$`\mathit{xnat} = \mathit{nat}, \infty` and $`\mathit{xint} = -\infty, \mathit{int}, \infty`.
In the typed model $`\mathit{nat}` and $`\mathit{int}` are bunches of Lean integers
($`\mathit{nat}` is $`\{n \mid 0 \le n\}`), and the extended integers are
`XInt := WithBot (WithTop ℤ)` with $`\bot = -\infty`, $`\top = \infty`, so
$`\mathit{xnat}` and $`\mathit{xint}` are bunches of `XInt`; `toXInt` embeds
$`\mathit{int}` into them. Builds on {uses "bunch_primitives"}[].
:::

:::theorem "bunch_named_bunch_laws" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.bin_eq, Aptop.BasicTheories.Bunch.int_eq, Aptop.BasicTheories.Bunch.xnat_eq, Aptop.BasicTheories.Bunch.xint_eq, Aptop.BasicTheories.Bunch.size_nat, Aptop.BasicTheories.Bunch.nat_eq_Ici")
The book's defining equations for the named bunches:
$`\mathit{bin} = \top, \bot`, $`\mathit{int} = \mathit{nat}, -\mathit{nat}`,
$`\mathit{xnat} = \mathit{nat}, \infty`, $`\mathit{xint} = -\infty, \mathit{int}, \infty`.
Here $`-\mathit{nat}` is pointwise negation (see {uses "bunch_operator_distribution"}[]),
and the extended equations go through the embedding of
{uses "bunch_named_bunches"}[].
The size law $`{\rm c\llap{/}}\mathit{nat} = \infty` of the Reference chapter (§11.3.3) is `size_nat`.
$`\mathit{nat} = 0,..\infty` (§11.3.3) is `nat_eq_Ici`: the interval notation of this formalization has
integer bounds, so the bound $`\infty` is rendered by the unbounded interval.
:::

:::proof "bunch_named_bunch_laws"
Extensionality; the extended cases split on $`-\infty`, a finite integer, or
$`\infty` and reduce to the finite statement by cast lemmas.
:::

:::theorem "bunch_nat_axioms" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.nat_construction, Aptop.BasicTheories.Bunch.nat_induction")
The two axioms defining $`\mathit{nat}`:
$`0, \mathit{nat}+1 : \mathit{nat}` (construction) and
$`0, B+1 : B \Rightarrow \mathit{nat} : B` (induction).
"Construction says that 0, 1, 2, and so on, are in nat. Induction says that
nothing else is in nat by saying that of all the bunches B satisfying the
construction axiom, nat is the smallest." Here $`B + 1` is the pointwise sum
$`B + \{1\}` of {uses "bunch_operator_distribution"}[], applied to
{uses "bunch_named_bunches"}[].
:::

:::proof "bunch_nat_axioms"
Construction is immediate from $`0 \le n \Rightarrow 0 \le n+1`. Induction
unpacks the hypothesis into a base case and a successor step and applies
integer induction from $`0` upward (`Int.leInduction`).
:::

:::definition "bunch_interval" (parent := "basic_theories_core") (lean := "Aptop.BasicTheories.Bunch.interval")
The interval $`x,..y` ("$`x` to $`y`", not "$`x` through $`y`") for
$`x \le y`, with axiom $`i : x,..y = i : \mathit{xint} \land x \le i < y`. The
asymmetric notation is a reminder that the left end is included and the right
end excluded. In Lean the bounds are integers and the interval is `Set.Ico x y`;
it is a bunch in the sense of {uses "bunch_vs_set"}[].
:::

:::theorem "bunch_interval_laws" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.mem_interval, Aptop.BasicTheories.Bunch.interval_zero_three, Aptop.BasicTheories.Bunch.interval_five_five, Aptop.BasicTheories.Bunch.interval_self, Aptop.BasicTheories.Bunch.interval_succ, Aptop.BasicTheories.Bunch.size_interval, Aptop.BasicTheories.Bunch.size_interval_of_le, Aptop.BasicTheories.Bunch.nat_eq_iUnion_interval")
The defining axiom $`i : x,..y = x \le i < y` and the book's examples:
$`0,..3 = 0, 1, 2`, $`5,..5 = \mathit{null}` (indeed $`x,..x = \mathit{null}`),
$`x,..x+1 = x`, and $`{\rm c\llap{/}}(x,..y) = y - x`. With integer bounds,
$`0,..\infty = \mathit{nat}` becomes: $`\mathit{nat}` is the union of the
intervals $`0,..y`. The size law is stated with the truncated difference
$`(y-x)_{\ge 0}`, which equals $`y - x` under the book's proviso $`x \le y`.
Uses {uses "bunch_interval"}[], {uses "bunch_primitives"}[] and
{uses "bunch_named_bunches"}[].
:::

:::proof "bunch_interval_laws"
Membership is definitional; the examples are extensionality plus linear
integer arithmetic; the size law is `Set.encard` of a finite integer interval
(`Int.card_Ico`).
:::

:::theorem "bunch_operator_distribution" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "Aptop.BasicTheories.Bunch.neg_null, Aptop.BasicTheories.Bunch.neg_union, Aptop.BasicTheories.Bunch.add_null, Aptop.BasicTheories.Bunch.null_add, Aptop.BasicTheories.Bunch.union_add_union, Aptop.BasicTheories.Bunch.add_elem")
"Other operators can be applied to bunches with the understanding that they
apply to the elements of the bunch. In other words, they distribute over bunch
union." The book's examples:
$`-\mathit{null} = \mathit{null}`, $`-(A, B) = -A, -B`,
$`A + \mathit{null} = \mathit{null} = \mathit{null} + A`, and
$`(A, B) + (C, D) = A+C, A+D, B+C, B+D`.
In Lean these are Mathlib's pointwise operations on sets (`Set.neg`,
`Set.add`), which have exactly this meaning; an elementary bunch adds like its
element, $`A + x = \{a + x \mid a : A\}`. Uses {uses "bunch_axioms_algebra"}[]
and {uses "bunch_primitives"}[].
Not modelled: the bunch-valued arithmetic of §11.3.3 — $`\infty, -\infty : x/0`, $`\mathit{xreal} : 0/0`, and the
exponent inclusions $`x^{y+z} : x^y \times x^z`, $`x^{y \times z} : (x^y)^z` — division and exponentiation are
functions here, not bunch-valued operators.
:::

:::proof "bunch_operator_distribution"
Pointwise-set lemmas from Mathlib (`Set.union_add`, `Set.add_union`,
`Set.add_empty`, `Set.add_singleton`) and extensionality for negation.
:::

:::definition "set_packaging" (parent := "basic_theories_core") (lean := "Aptop.BasicTheories.Bunch.pack, Aptop.BasicTheories.HSet.contents, Aptop.BasicTheories.Bunch.power, Aptop.BasicTheories.HSet.card")
Set formation $`\{A\}` packages a bunch into a set (`Bunch.pack`); contents
$`\sim S` unpackages it (`HSet.contents`); the power operator $`𝒫A` is the bunch
of all sets whose contents are included in $`A`; and $`\$S` is the size of a set.
The set operators $`\in`, $`\subseteq`, $`\cup`, $`\cap` are "promoted" from the
bunch operators by acting on contents. Builds on {uses "bunch_vs_set"}[].
:::

:::theorem "set_axioms" (parent := "basic_theories_core") (tags := "basic, set, hehner-2.1") (effort := "small") (lean := "Aptop.BasicTheories.HSet.pack_contents, Aptop.BasicTheories.HSet.contents_pack, Aptop.BasicTheories.HSet.card_pack, Aptop.BasicTheories.HSet.mem_pack, Aptop.BasicTheories.HSet.pack_subset_pack, Aptop.BasicTheories.HSet.pack_mem_power, Aptop.BasicTheories.HSet.pack_union_pack, Aptop.BasicTheories.HSet.pack_inter_pack, Aptop.BasicTheories.HSet.pack_inj")
Hehner's Set Theory axioms, for a set $`S`, bunches $`A, B` and element $`x`:
$`\{\sim S\} = S` (set formation), $`\sim\{A\} = A` (contents),
$`\$\{A\} = {\rm c\llap{/}}A` (size), $`x \in \{B\} = x : B` (elements),
$`\{A\} \subseteq \{B\} = A : B` (subset), $`\{A\} : 𝒫B = A : B` (power),
$`\{A\} \cup \{B\} = \{A, B\}` (union), $`\{A\} \cap \{B\} = \{A \mathbin{\lq} B\}` (intersection),
and $`\{A\} = \{B\} = (A = B)` (equation).
The remaining axiom $`\{A\} \neq A` (structure) is not an equation in the typed
model: a set and its contents have different Lean types, which is exactly the
distinction it records.
Uses {uses "set_packaging"}[] and {uses "bunch_axioms_inclusion"}[].
The Reference chapter's $`\{A\} : B` (§11.3.4), a set as an element of a bunch of sets, is set
membership in this model; its instance $`\{A\} : \mathcal{P}B = A : B` is `pack_mem_power`, and
$`\{A\} \neq A` is a type distinction (see the bunch/set node).
:::

:::proof "set_axioms"
Every law is definitional (`rfl` / `Iff.rfl`) once the set operators are defined
on contents; injectivity of packaging is structure eta.
:::

:::definition "number_domain" (parent := "basic_theories_core") (lean := "Aptop.BasicTheories.Number, Aptop.BasicTheories.Number.Finite, Aptop.BasicTheories.Number.Finite.exists_coe, Aptop.BasicTheories.Number.finite_coe")
Hehner's numbers are the extended reals $`\mathit{xreal} = -\infty, \mathit{real}, \infty`;
Number Theory (Section 1.1) is "the theory of numbers as you learned it in
school", with $`\infty` and $`-\infty` added and their laws stated under
provisos such as $`-\infty < x < \infty`. In Lean a number is Mathlib's `EReal`
(`Number`), $`\bot = -\infty`, $`\top = \infty`, and the proviso is the
predicate `Number.Finite`. Mathlib fixes values the book leaves unspecified
($`\infty + -\infty = -\infty`, $`\infty \times 0 = 0`, $`x / 0 = 0`,
$`1/\infty = 0`); the laws below are stated under the book's provisos, and the
few laws the book states unconditionally that fail at those points carry the
hypothesis excluding them. The named bunches $`\mathit{xnat}`, $`\mathit{xint}`
of {uses "bunch_named_bunches"}[] are the corresponding sub-bunches.
:::

:::theorem "number_laws_additive" (parent := "basic_theories_core") (tags := "basic, number, hehner-11.3.2") (effort := "small") (lean := "Aptop.BasicTheories.Number.add_zero, Aptop.BasicTheories.Number.add_comm, Aptop.BasicTheories.Number.add_assoc, Aptop.BasicTheories.Number.add_left_cancel_iff, Aptop.BasicTheories.Number.top_add, Aptop.BasicTheories.Number.bot_add, Aptop.BasicTheories.Number.neg_eq_zero_sub, Aptop.BasicTheories.Number.neg_neg, Aptop.BasicTheories.Number.neg_add, Aptop.BasicTheories.Number.neg_sub, Aptop.BasicTheories.Number.neg_mul, Aptop.BasicTheories.Number.neg_mul_eq_mul_neg, Aptop.BasicTheories.Number.neg_div, Aptop.BasicTheories.Number.neg_div_eq_div_neg, Aptop.BasicTheories.Number.sub_zero, Aptop.BasicTheories.Number.sub_eq_add_neg, Aptop.BasicTheories.Number.add_sub, Aptop.BasicTheories.Number.sub_add, Aptop.BasicTheories.Number.sub_left_cancel_iff, Aptop.BasicTheories.Number.sub_self, Aptop.BasicTheories.Number.top_sub, Aptop.BasicTheories.Number.bot_sub")
Addition, negation and subtraction laws (reference §11.3.2):
$`x + 0 = x`, $`x + y = y + x`, $`x + (y + z) = (x + y) + z`;
$`-\infty < x < \infty \Rightarrow (x + y = x + z) = (y = z)` (Cancellation);
$`-\infty < x \Rightarrow \infty + x = \infty`, $`x < \infty \Rightarrow -\infty + x = -\infty` (Absorption);
$`-x = 0 - x`, $`- -x = x`, $`-(x + y) = -x + -y`, $`-(x - y) = y - x`,
$`-x \times y = -(x \times y) = x \times -y`, $`-x / y = -(x / y) = x / -y`;
$`x - 0 = x`, $`x - y = x + -y`, $`x + (y - z) = (x + y) - z`, $`x - (y + z) = (x - y) - z`;
$`-\infty < x < \infty \Rightarrow (x - y = x - z) = (y = z)`, $`-\infty < x < \infty \Rightarrow x - x = 0`;
$`x < \infty \Rightarrow \infty - x = \infty`, $`-\infty < x \Rightarrow -\infty - x = -\infty`.
The three laws involving $`-(y + z)` or $`-(y - z)` exclude the unspecified
case $`\{y, z\} = \{\infty, -\infty\}`, where Mathlib's model disagrees with
the book. Uses {uses "number_domain"}[].
Not stated as laws: the Counting laws of §11.3.2 ($`d0 + 1 = d1`, …, $`d9 + 1 = (d{+}1)0`) — decimal
notation, decided by `norm_num` on instances.
:::

:::proof "number_laws_additive"
Mathlib's `EReal` lemmas; the cancellation laws reduce a finite $`x` to a real
number and subtract it.
:::

:::theorem "number_laws_multiplicative" (parent := "basic_theories_core") (tags := "basic, number, hehner-11.3.2") (effort := "small") (lean := "Aptop.BasicTheories.Number.mul_zero, Aptop.BasicTheories.Number.mul_one, Aptop.BasicTheories.Number.mul_comm, Aptop.BasicTheories.Number.mul_add, Aptop.BasicTheories.Number.mul_assoc, Aptop.BasicTheories.Number.mul_left_cancel_iff, Aptop.BasicTheories.Number.mul_top, Aptop.BasicTheories.Number.mul_bot, Aptop.BasicTheories.Number.div_one, Aptop.BasicTheories.Number.zero_div, Aptop.BasicTheories.Number.div_self, Aptop.BasicTheories.Number.mul_div, Aptop.BasicTheories.Number.mul_div_eq_div_mul, Aptop.BasicTheories.Number.div_mul_eq_div_div, Aptop.BasicTheories.Number.div_div, Aptop.BasicTheories.Number.div_mul_cancel, Aptop.BasicTheories.Number.div_top, Aptop.BasicTheories.Number.div_bot, Aptop.BasicTheories.Number.pow_zero, Aptop.BasicTheories.Number.pow_one")
Multiplication, division and exponentiation laws (reference §11.3.2):
$`-\infty < x < \infty \Rightarrow x \times 0 = 0`, $`x \times 1 = x`, $`x \times y = y \times x`,
$`x \times (y + z) = x \times y + x \times z`, $`x \times (y \times z) = (x \times y) \times z`;
$`-\infty < x < \infty \land x \neq 0 \Rightarrow (x \times y = x \times z) = (y = z)`;
$`0 < x \Rightarrow x \times \infty = \infty`, $`0 < x \Rightarrow x \times -\infty = -\infty`;
$`x / 1 = x`, $`x \neq 0 \Rightarrow 0 / x = 0`, $`-\infty < x < \infty \land x \neq 0 \Rightarrow x / x = 1`;
$`x \times (y / z) = (x \times y) / z = (x / z) \times y = x / (z / y)`, $`(x / y) / z = x / (y \times z)`;
$`-\infty < y < \infty \land y \neq 0 \Rightarrow (x / y) \times y = x`;
$`-\infty < x < \infty \Rightarrow x / \infty = 0 = x / -\infty` (Annihilation);
$`-\infty < x < \infty \Rightarrow x^0 = 1`, $`x^1 = x`.
Distributivity is stated for finite $`x, y, z` and $`(x/z) \times y = x/(z/y)` for
finite $`y`: the book states them for all numbers, but they fail in Mathlib's
model at $`\infty + -\infty` and $`1/\infty`. Uses {uses "number_domain"}[].
:::

:::proof "number_laws_multiplicative"
`EReal` is a commutative monoid with zero and a `DivInvMonoid`; the finite
cases reduce to real arithmetic through the coercion.
:::

:::theorem "number_laws_order" (parent := "basic_theories_core") (tags := "basic, number, hehner-11.3.2") (effort := "small") (lean := "Aptop.BasicTheories.Number.direction, Aptop.BasicTheories.Number.lt_iff_neg_lt_neg, Aptop.BasicTheories.Number.add_lt_add_iff_left, Aptop.BasicTheories.Number.coe_mul_lt_coe_mul_iff, Aptop.BasicTheories.Number.mul_lt_mul_iff_left, Aptop.BasicTheories.Number.trichotomy, Aptop.BasicTheories.Number.extremes, Aptop.BasicTheories.Number.max_top, Aptop.BasicTheories.Number.min_bot")
Order laws (reference §11.3.2): $`-\infty < 0 < 1 < \infty` (Direction),
$`(x < y) = (-y < -x)` (Reflection),
$`-\infty < x < \infty \Rightarrow (x + y < x + z) = (y < z)` (Cancellation, Translation),
$`0 < x < \infty \Rightarrow (x \times y < x \times z) = (y < z)` (Cancellation, Scale),
$`x < y \lor x = y \lor x > y` (Trichotomy), $`-\infty \le x \le \infty` (Extremes),
$`x \uparrow \infty = \infty` and $`x \downarrow -\infty = -\infty` (Base), where
$`\uparrow`/$`\downarrow` are maximum/minimum. Uses {uses "number_domain"}[].
:::

:::proof "number_laws_order"
`EReal` is a complete linear order; Translation and Scale reduce a finite
$`x` to a positive real and case-split $`y, z` over $`-\infty`, real, $`\infty`.
:::

:::theorem "nat_add_zero" (parent := "basic_theories_core") (tags := "basic, arithmetic") (effort := "small") (lean := "Aptop.BasicTheories.Number.add_zero")
For every natural number $`n`, adding zero on the right leaves it unchanged:
$`n + 0 = n`.
A trivial arithmetic checkpoint before connecting to {uses "bunch_vs_set"}[].
:::

:::proof "nat_add_zero"
Induct on $`n`, or use the kernel simplifier.
:::

```lean "nat_add_zero"
theorem nat_add_zero (n : Nat) : n + 0 = n := by
  simp
```

:::definition "calculation_style" (parent := "basic_theories_core") (lean := "Aptop.BasicTheories.Calculation.continuing_equation, Aptop.BasicTheories.Calculation.portation_calc")
Proofs in Aptop are often written as *calculations*: chains of equalities or
implications annotated with the justifying law at each step. Formal Lean proofs
should preserve that readable structure where practical.

"A proof is a binary expression that is clearly a theorem. ... One form of
proof is a continuing equation with hints: $`\mathit{expression}_0 = \mathit{expression}_1 = \mathit{expression}_2 = \mathit{expression}_3`
with $`\mathit{hint}_0, \mathit{hint}_1, \mathit{hint}_2` on the right side of the page. This
continuing equation is a short way of writing the longer binary expression
$`\mathit{expression}_0 = \mathit{expression}_1 \land \mathit{expression}_1 = \mathit{expression}_2 \land \mathit{expression}_2 = \mathit{expression}_3`.
... The best kind of hint is the name of a law. ... By the transitivity of
$`=`, this proof proves the theorem $`\mathit{expression}_0 = \mathit{expression}_3`. A formal
proof is a proof in which every step fits the form of the law given as hint."
Lean's `calc` block is exactly this form — each step an equation justified by
the named law, the block proving the equation between first and last expression
by transitivity — and is used for the book's worked example in
{uses "portation_by_calculation"}[]. Uses {uses "boolean_domain"}[].
:::

:::theorem "portation_by_calculation" (parent := "basic_theories_core") (tags := "basic, calculation, hehner-1.0.1") (effort := "small") (lean := "Aptop.BasicTheories.Calculation.portation_calc, Aptop.BasicTheories.Calculation.portation_calc', Aptop.BasicTheories.Calculation.portation_of_calc', Aptop.BasicTheories.Calculation.portation_calc_eq_law")
The book's worked example: "suppose we want to prove the first Law of
Portation $`a \land b \Rightarrow c = a \Rightarrow (b \Rightarrow c)` using only previous laws":
$`a \land b \Rightarrow c`
$`= \neg(a \land b) \lor c`  (Material Implication),
$`= \neg a \lor \neg b \lor c`  (Duality),
$`= a \Rightarrow \neg b \lor c`  (Material Implication),
$`= a \Rightarrow (b \Rightarrow c)`  (Material Implication) —
"by not using brackets on that line, we silently use the Associative Law of
disjunction", made an explicit step here. "Here is the proof again, in a
different form":
$`(a \land b \Rightarrow c = a \Rightarrow (b \Rightarrow c)) = (\neg(a \land b) \lor c = \neg a \lor (\neg b \lor c)) = (\neg a \lor \neg b \lor c = \neg a \lor \neg b \lor c) = \top`
(Material Implication 3 times; Duality; Reflexivity). Both calculations are
Lean `calc` blocks whose steps are the laws of {uses "binary_laws_algebra"}[]
under the book's names, and the first is definitionally the law
$`(a \land b \Rightarrow c) = (a \Rightarrow (b \Rightarrow c))` of that node. Uses
{uses "calculation_style"}[].
:::

:::theorem "generic_laws" (parent := "basic_theories_core") (tags := "basic, generic, order, hehner-11.3.0") (effort := "small") (lean := "Aptop.BasicTheories.Generic.eq_refl', Aptop.BasicTheories.Generic.eq_symm_iff, Aptop.BasicTheories.Generic.eq_trans_of, Aptop.BasicTheories.Generic.transparency, Aptop.BasicTheories.Generic.ne_iff_not_eq, Aptop.BasicTheories.Generic.ite_true_base, Aptop.BasicTheories.Generic.ite_false_base, Aptop.BasicTheories.Generic.ite_idem, Aptop.BasicTheories.Generic.ite_reversal, Aptop.BasicTheories.Generic.le_iff_eq_min, Aptop.BasicTheories.Generic.min_le_self_le_max, Aptop.BasicTheories.Generic.le_iff_eq_max, Aptop.BasicTheories.Generic.le_refl', Aptop.BasicTheories.Generic.not_lt_self, Aptop.BasicTheories.Generic.not_lt_and_eq, Aptop.BasicTheories.Generic.not_gt_and_eq, Aptop.BasicTheories.Generic.not_lt_and_gt, Aptop.BasicTheories.Generic.le_iff_lt_or_eq', Aptop.BasicTheories.Generic.le_le_trans, Aptop.BasicTheories.Generic.lt_le_trans, Aptop.BasicTheories.Generic.lt_lt_trans, Aptop.BasicTheories.Generic.le_lt_trans, Aptop.BasicTheories.Generic.gt_iff_lt', Aptop.BasicTheories.Generic.ge_iff_le', Aptop.BasicTheories.Generic.not_lt_iff_ge, Aptop.BasicTheories.Generic.not_le_iff_gt, Aptop.BasicTheories.Generic.le_antisymm_iff', Aptop.BasicTheories.Generic.trichotomy', Aptop.BasicTheories.Generic.max_idem, Aptop.BasicTheories.Generic.min_idem, Aptop.BasicTheories.Generic.max_symm, Aptop.BasicTheories.Generic.min_symm, Aptop.BasicTheories.Generic.max_assoc', Aptop.BasicTheories.Generic.min_assoc', Aptop.BasicTheories.Generic.max_min_distrib, Aptop.BasicTheories.Generic.min_max_distrib, Aptop.BasicTheories.Generic.max_le_iff', Aptop.BasicTheories.Generic.min_le_iff', Aptop.BasicTheories.Generic.le_max_iff', Aptop.BasicTheories.Generic.le_min_iff', Aptop.BasicTheories.Generic.max_eq_ite, Aptop.BasicTheories.Generic.min_eq_ite, Aptop.DataStructures.Str.lt_iff_lex, Aptop.DataStructures.Str.le_iff_not_lt, Aptop.DataStructures.HList.lt_iff_contents_lt, Aptop.DataStructures.HList.le_iff_not_lt")
The Generic table of the Reference chapter (Section 11.3.0). "The operators
$`= \neq \mathbf{if}\ \mathbf{then}\ \mathbf{else}` apply to every type of expression (but the first
operand of $`\mathbf{if}\ \mathbf{then}\ \mathbf{else}` must be binary), with the laws" $`x = x`
Reflexivity, $`x = y = y = x` Symmetry, $`x = y \land y = z \Rightarrow x = z` Transitivity,
$`x = y \Rightarrow f\,x = f\,y` Transparency, $`x \neq y = \lnot(x = y)` Unequality,
$`\mathbf{if}\ \top\ \mathbf{then}\ x\ \mathbf{else}\ y = x` and $`\mathbf{if}\ \bot\ \mathbf{then}\ x\ \mathbf{else}\ y = y` Case
Base, $`\mathbf{if}\ a\ \mathbf{then}\ x\ \mathbf{else}\ x = x` Case Idempotent,
$`\mathbf{if}\ a\ \mathbf{then}\ x\ \mathbf{else}\ y = \mathbf{if}\ \lnot a\ \mathbf{then}\ y\ \mathbf{else}\ x` Case Reversal.
"The operators $`\uparrow \downarrow < \leq > \geq` apply to numbers, characters, strings, and
lists, with the laws" $`x \leq y = x = x \downarrow y`, $`x \downarrow y \leq x \leq x \uparrow y`,
$`x \leq y = y = x \uparrow y`, Reflexivity $`x \leq x`, Irreflexivity $`\lnot x < x`, Exclusivity
$`\lnot(x < y \land x = y)`, $`\lnot(x > y \land x = y)`, $`\lnot(x < y \land x > y)`, Inclusivity
$`x \leq y = x < y \lor x = y`, the four Transitivity laws, Mirror $`x > y = y < x`,
$`x \geq y = y \leq x`, Totality $`\lnot x < y = x \geq y`, $`\lnot x \leq y = x > y`, Antisymmetry
$`x \leq y \land y \leq x = x = y`, Trichotomy $`x < y \lor x = y \lor x > y`, Idempotence,
Symmetry and Associativity of $`\uparrow` and $`\downarrow`, Distributivity
$`x \uparrow (y \downarrow z) = (x \uparrow y) \downarrow (x \uparrow z)` and
$`x \downarrow (y \uparrow z) = (x \downarrow y) \uparrow (x \downarrow z)`, the four Connection laws
$`x \uparrow y \leq z = x \leq z \land y \leq z`, $`x \downarrow y \leq z = x \leq z \lor y \leq z`,
$`x \leq y \uparrow z = x \leq y \lor x \leq z`, $`x \leq y \downarrow z = x \leq y \land x \leq z`, and
$`x \uparrow y = \mathbf{if}\ x \geq y\ \mathbf{then}\ x\ \mathbf{else}\ y`,
$`x \downarrow y = \mathbf{if}\ x \leq y\ \mathbf{then}\ x\ \mathbf{else}\ y`.

Model notes. The equality and $`\mathbf{if}` laws are stated for an arbitrary type,
with a decidable condition for $`\mathbf{if}` (the binary laws of the same shape are
{uses "binary_laws_case"}[]). The order laws are stated once for an arbitrary
linear order, which instantiates to the numbers of this formalization — the
integers and extended integers of {uses "number_laws_order"}[], $`\mathit{nat}`,
$`\mathit{xnat}`, the rationals and reals — to characters, and, as the book says, to
strings and lists: the lexicographic order of `Str` is Mathlib's linear order on
lists (`Str.lt_iff_lex`), and `HList` carries the lifted linear order
(`HList.lt_iff_contents_lt`), both agreeing with the `<` of the string and list
axioms; `Str.le_iff_not_lt` and `HList.le_iff_not_lt` are the Totality law
instantiated.
$`\uparrow`, $`\downarrow` are `max`, `min`. Every law is one theorem, named after the
book's law name and operator.
:::
