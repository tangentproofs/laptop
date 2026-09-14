import Verso
import VersoManual
import VersoBlueprint
import LaPToP.BasicTheories.Bunch
import LaPToP.BasicTheories.Numbers

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Basic Theories" =>

:::group "basic_theories_core"
Basic theories: numbers, bunches, sets, and the calculation style that
underpins later program reasoning in LaPToP. The bunch and set material is
Hehner's Sections 2.0 and 2.1; the formal counterpart lives in the Lean module
`LaPToP.BasicTheories.Bunch` (axioms and laws) and
`LaPToP.BasicTheories.Numbers` (named bunches, the interval, distribution).
:::

:::definition "bunch_vs_set" (parent := "basic_theories_core") (lean := "LaPToP.BasicTheories.Bunch, LaPToP.BasicTheories.HSet")
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

:::definition "bunch_primitives" (parent := "basic_theories_core") (lean := "LaPToP.BasicTheories.Bunch.null, LaPToP.BasicTheories.Bunch.elem, LaPToP.BasicTheories.Bunch.size")
The empty bunch $`\mathit{null}`, the elementary bunch of a single element
$`x` (written just $`x` in the book, `{x}` in Lean), and the size
$`{\rm c\llap{/}}A` of a bunch. Size takes values in the extended naturals so that
$`{\rm c\llap{/}}\,\mathit{nat} = \infty` as in the book. These are the primitives used by
{uses "bunch_vs_set"}[].
:::

:::theorem "bunch_axioms_membership" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.elem_subset_elem, LaPToP.BasicTheories.Bunch.elem_subset_iff, LaPToP.BasicTheories.Bunch.mem_union, LaPToP.BasicTheories.Bunch.mem_inter, LaPToP.BasicTheories.Bunch.mem_remove")
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

:::theorem "bunch_axioms_algebra" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.union_self, LaPToP.BasicTheories.Bunch.union_comm, LaPToP.BasicTheories.Bunch.union_assoc, LaPToP.BasicTheories.Bunch.inter_self, LaPToP.BasicTheories.Bunch.inter_comm, LaPToP.BasicTheories.Bunch.inter_assoc, LaPToP.BasicTheories.Bunch.remove_union, LaPToP.BasicTheories.Bunch.remove_remove, LaPToP.BasicTheories.Bunch.inter_remove, LaPToP.BasicTheories.Bunch.inter_remove_comm, LaPToP.BasicTheories.Bunch.union_inter_distrib, LaPToP.BasicTheories.Bunch.inter_union_distrib")
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

:::theorem "bunch_axioms_inclusion" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.subset_inter_iff, LaPToP.BasicTheories.Bunch.union_subset_iff, LaPToP.BasicTheories.Bunch.subset_union, LaPToP.BasicTheories.Bunch.inter_subset, LaPToP.BasicTheories.Bunch.subset_refl, LaPToP.BasicTheories.Bunch.subset_antisymm_iff, LaPToP.BasicTheories.Bunch.subset_trans, LaPToP.BasicTheories.Bunch.superset_iff")
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

:::theorem "bunch_axioms_size" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.size_elem, LaPToP.BasicTheories.Bunch.size_union_add_size_inter, LaPToP.BasicTheories.Bunch.not_mem_iff_size_inter_elem, LaPToP.BasicTheories.Bunch.size_le_size")
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

:::theorem "bunch_null_laws" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.null_subset, LaPToP.BasicTheories.Bunch.size_eq_zero_iff, LaPToP.BasicTheories.Bunch.union_null, LaPToP.BasicTheories.Bunch.inter_null, LaPToP.BasicTheories.Bunch.size_null")
The empty bunch is defined in the book by $`\mathit{null} : A` and
$`{\rm c\llap{/}}A = 0 = (A = \mathit{null})`, giving $`A, \mathit{null} = A` (identity),
$`A \mathbin{\lq} \mathit{null} = \mathit{null}` (base), and $`{\rm c\llap{/}}\,\mathit{null} = 0` (size).
Uses {uses "bunch_primitives"}[] and {uses "bunch_axioms_size"}[].
:::

:::proof "bunch_null_laws"
$`\mathit{null}` is the empty set; all five are standard `Set` and `encard` facts.
:::

:::theorem "bunch_derived_laws" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.union_inter_self, LaPToP.BasicTheories.Bunch.inter_union_self, LaPToP.BasicTheories.Bunch.union_subset_union_right, LaPToP.BasicTheories.Bunch.inter_subset_inter_right, LaPToP.BasicTheories.Bunch.subset_iff_union_eq, LaPToP.BasicTheories.Bunch.union_eq_iff_inter_eq, LaPToP.BasicTheories.Bunch.union_union_distrib, LaPToP.BasicTheories.Bunch.inter_inter_distrib, LaPToP.BasicTheories.Bunch.union_subset_union, LaPToP.BasicTheories.Bunch.inter_subset_inter")
Laws Hehner lists as provable from the axioms:
$`A, (A \mathbin{\lq} B) = A` and $`A \mathbin{\lq} (A, B) = A` (absorption);
$`A : B \Rightarrow C, A : C, B` and $`A : B \Rightarrow C \mathbin{\lq} A : C \mathbin{\lq} B` (monotonicity);
$`A : B = (A, B = B) = (A = A \mathbin{\lq} B)` (inclusion);
$`A, (B, C) = (A, B), (A, C)` and $`A \mathbin{\lq} (B \mathbin{\lq} C) = (A \mathbin{\lq} B) \mathbin{\lq} (A \mathbin{\lq} C)` (distributivity);
$`A : B \land C : D \Rightarrow A, C : B, D` and
$`A : B \land C : D \Rightarrow A \mathbin{\lq} C : B \mathbin{\lq} D` (conflation).
Uses {uses "bunch_axioms_algebra"}[] and {uses "bunch_axioms_inclusion"}[].
:::

:::proof "bunch_derived_laws"
In Lean these are proved directly from Mathlib's lattice lemmas rather than by
calculation from the axiom nodes; the dependency edges record the book's
derivation.
:::

:::definition "bunch_named_bunches" (parent := "basic_theories_core") (lean := "LaPToP.BasicTheories.Bunch.bin, LaPToP.BasicTheories.Bunch.nat, LaPToP.BasicTheories.Bunch.int, LaPToP.BasicTheories.XInt, LaPToP.BasicTheories.Bunch.xnat, LaPToP.BasicTheories.Bunch.xint, LaPToP.BasicTheories.Bunch.toXInt")
Hehner's useful bunches: $`\mathit{bin} = \top, \bot`, $`\mathit{nat} = 0, 1, 2, \ldots`,
$`\mathit{int} = \ldots, -1, 0, 1, \ldots`, and the extended versions
$`\mathit{xnat} = \mathit{nat}, \infty` and $`\mathit{xint} = -\infty, \mathit{int}, \infty`.
In the typed model $`\mathit{nat}` and $`\mathit{int}` are bunches of Lean integers
($`\mathit{nat}` is $`\{n \mid 0 \le n\}`), and the extended integers are
`XInt := WithBot (WithTop ℤ)` with $`\bot = -\infty`, $`\top = \infty`, so
$`\mathit{xnat}` and $`\mathit{xint}` are bunches of `XInt`; `toXInt` embeds
$`\mathit{int}` into them. Builds on {uses "bunch_primitives"}[].
:::

:::theorem "bunch_named_bunch_laws" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.bin_eq, LaPToP.BasicTheories.Bunch.int_eq, LaPToP.BasicTheories.Bunch.xnat_eq, LaPToP.BasicTheories.Bunch.xint_eq")
The book's defining equations for the named bunches:
$`\mathit{bin} = \top, \bot`, $`\mathit{int} = \mathit{nat}, -\mathit{nat}`,
$`\mathit{xnat} = \mathit{nat}, \infty`, $`\mathit{xint} = -\infty, \mathit{int}, \infty`.
Here $`-\mathit{nat}` is pointwise negation (see {uses "bunch_operator_distribution"}[]),
and the extended equations go through the embedding of
{uses "bunch_named_bunches"}[].
:::

:::proof "bunch_named_bunch_laws"
Extensionality; the extended cases split on $`-\infty`, a finite integer, or
$`\infty` and reduce to the finite statement by cast lemmas.
:::

:::theorem "bunch_nat_axioms" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.nat_construction, LaPToP.BasicTheories.Bunch.nat_induction")
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

:::definition "bunch_interval" (parent := "basic_theories_core") (lean := "LaPToP.BasicTheories.Bunch.interval")
The interval $`x,..y` ("$`x` to $`y`", not "$`x` through $`y`") for
$`x \le y`, with axiom $`i : x,..y = i : \mathit{xint} \land x \le i < y`. The
asymmetric notation is a reminder that the left end is included and the right
end excluded. In Lean the bounds are integers and the interval is `Set.Ico x y`;
it is a bunch in the sense of {uses "bunch_vs_set"}[].
:::

:::theorem "bunch_interval_laws" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.mem_interval, LaPToP.BasicTheories.Bunch.interval_zero_three, LaPToP.BasicTheories.Bunch.interval_five_five, LaPToP.BasicTheories.Bunch.interval_self, LaPToP.BasicTheories.Bunch.interval_succ, LaPToP.BasicTheories.Bunch.size_interval, LaPToP.BasicTheories.Bunch.size_interval_of_le, LaPToP.BasicTheories.Bunch.nat_eq_iUnion_interval")
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

:::theorem "bunch_operator_distribution" (parent := "basic_theories_core") (tags := "basic, bunch, hehner-2.0") (effort := "small") (lean := "LaPToP.BasicTheories.Bunch.neg_null, LaPToP.BasicTheories.Bunch.neg_union, LaPToP.BasicTheories.Bunch.add_null, LaPToP.BasicTheories.Bunch.null_add, LaPToP.BasicTheories.Bunch.union_add_union, LaPToP.BasicTheories.Bunch.add_elem")
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
:::

:::proof "bunch_operator_distribution"
Pointwise-set lemmas from Mathlib (`Set.union_add`, `Set.add_union`,
`Set.add_empty`, `Set.add_singleton`) and extensionality for negation.
:::

:::definition "set_packaging" (parent := "basic_theories_core") (lean := "LaPToP.BasicTheories.Bunch.pack, LaPToP.BasicTheories.HSet.contents, LaPToP.BasicTheories.Bunch.power, LaPToP.BasicTheories.HSet.card")
Set formation $`\{A\}` packages a bunch into a set (`Bunch.pack`); contents
$`\sim S` unpackages it (`HSet.contents`); the power operator $`𝒫A` is the bunch
of all sets whose contents are included in $`A`; and $`\$S` is the size of a set.
The set operators $`\in`, $`\subseteq`, $`\cup`, $`\cap` are "promoted" from the
bunch operators by acting on contents. Builds on {uses "bunch_vs_set"}[].
:::

:::theorem "set_axioms" (parent := "basic_theories_core") (tags := "basic, set, hehner-2.1") (effort := "small") (lean := "LaPToP.BasicTheories.HSet.pack_contents, LaPToP.BasicTheories.HSet.contents_pack, LaPToP.BasicTheories.HSet.card_pack, LaPToP.BasicTheories.HSet.mem_pack, LaPToP.BasicTheories.HSet.pack_subset_pack, LaPToP.BasicTheories.HSet.pack_mem_power, LaPToP.BasicTheories.HSet.pack_union_pack, LaPToP.BasicTheories.HSet.pack_inter_pack, LaPToP.BasicTheories.HSet.pack_inj")
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
:::

:::proof "set_axioms"
Every law is definitional (`rfl` / `Iff.rfl`) once the set operators are defined
on contents; injectivity of packaging is structure eta.
:::

:::theorem "nat_add_zero" (parent := "basic_theories_core") (tags := "basic, arithmetic") (effort := "small")
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

:::definition "calculation_style" (parent := "basic_theories_core")
Proofs in LaPToP are often written as *calculations*: chains of equalities or
implications annotated with the justifying law at each step. Formal Lean proofs
should preserve that readable structure where practical.
:::
