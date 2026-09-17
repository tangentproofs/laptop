import Verso
import VersoManual
import VersoBlueprint
import LaPToP.DataStructures.Strings
import LaPToP.DataStructures.Lists
import LaPToP.FunctionTheory.HigherOrder

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Data Structures" =>

:::group "data_structures_core"
Data structures as they appear in LaPToP: lists/strings, functions as data,
and related theories used when specifying programs that manipulate structure.
The string and list material is Hehner's Sections 2.2 and 2.3; the formal
counterparts are the Lean modules `LaPToP.DataStructures.Strings` and
`LaPToP.DataStructures.Lists`.
:::

:::definition "list_as_string" (parent := "data_structures_core") (lean := "LaPToP.DataStructures.Str, LaPToP.DataStructures.Str.nil, LaPToP.DataStructures.Str.item, LaPToP.DataStructures.Str.len")
Hehner treats finite sequences uniformly (often called *strings* or *lists*).
Concatenation, length, and indexing are the primitive operations; many program
specifications are expressed directly in this theory.

"Bunches are uncontained collections and sets are contained collections.
Similarly, strings are uncontained sequences and lists are contained
sequences." A *string* of items of type $`\alpha` is modelled as a Lean
`List α` (`Str α`): $`\mathit{nil}` is `[]`, a one-item string $`i` is `[i]`,
join $`S; T` is `S ++ T`, and the length $`\leftrightarrow S` is
`Str.len S`, valued in the extended naturals like the book's. Only finite
strings are modelled, so the book's provisos $`\leftrightarrow S < \infty`
hold automatically.
:::

:::theorem "list_append_nil" (parent := "data_structures_core") (tags := "data, lists") (effort := "small") (lean := "LaPToP.DataStructures.Str.append_nil")
Appending the empty list on the right is an identity:
$`xs \mathbin{+\hspace{-0.4em}+} [\,] = xs`.
This is the first identity for {uses "list_as_string"}[].
:::

:::proof "list_append_nil"
By the definition of list append / `List.concat`.
:::

```lean "list_append_nil"
theorem list_append_nil (xs : List α) :
    xs ++ ([] : List α) = xs := by
  simp
```

:::definition "string_syntax" (parent := "data_structures_core") (lean := "LaPToP.DataStructures.Str.at, LaPToP.DataStructures.Str.sub, LaPToP.DataStructures.Str.copies, LaPToP.DataStructures.Str.star, LaPToP.DataStructures.Str.update, LaPToP.DataStructures.Str.interval")
The syntax of strings beyond join and length: $`S\,n` is item $`n` of $`S`
(indexing from $`0`: "the index of an item is the number of items that precede
it"); $`S\,T` for a string of indexes $`T` selects a whole string of items, as in
$`(3; 5; 7; 9)\,(2; 1; 2) = 7; 5; 7`; $`n*S` is $`n` copies of $`S` joined
together; $`*S` is the bunch of all such copies; $`S \triangleleft n \triangleright i`
("$`S` but at $`n` is $`i`") replaces the item at index $`n`; and $`x;..y` is the
string $`x; x+1; \ldots; y-1`. The book leaves $`S\,n` unspecified for an index
out of range; the Lean model returns `default` there. Extends
{uses "list_as_string"}[].
:::

:::theorem "string_axioms_join_length" (parent := "data_structures_core") (tags := "data, strings, hehner-2.2") (effort := "small") (lean := "LaPToP.DataStructures.Str.append_nil, LaPToP.DataStructures.Str.nil_append, LaPToP.DataStructures.Str.append_assoc, LaPToP.DataStructures.Str.len_nil, LaPToP.DataStructures.Str.len_item, LaPToP.DataStructures.Str.len_append, LaPToP.DataStructures.Str.append_item_append_inj")
The join and length axioms of String Theory:
$`S; \mathit{nil} = S = \mathit{nil}; S` (identity),
$`S; (T; U) = (S; T); U` (associativity),
$`\leftrightarrow\mathit{nil} = 0` and $`\leftrightarrow i = 1` (base),
$`\leftrightarrow(S; T) = \leftrightarrow S + \leftrightarrow T`, and
$`(i = j) = (S; i; T = S; j; T)`.
Uses {uses "list_as_string"}[]; the first identity is {uses "list_append_nil"}[].
:::

:::proof "string_axioms_join_length"
`List.append_nil`, `List.nil_append`, `List.append_assoc`, `List.length_append`,
and cancellation of a common prefix and suffix.
:::

:::theorem "string_axioms_indexing" (parent := "data_structures_core") (tags := "data, strings, hehner-2.2") (effort := "small") (lean := "LaPToP.DataStructures.Str.sub_nil, LaPToP.DataStructures.Str.at_append_item_append, LaPToP.DataStructures.Str.sub_append, LaPToP.DataStructures.Str.sub_sub, LaPToP.DataStructures.Str.at_map_of_lt")
The indexing axioms:
$`S\,\mathit{nil} = \mathit{nil}`,
$`(S; i; T)\,(\leftrightarrow S) = i`,
$`S\,(T; U) = S\,T; S\,U`, and
$`S\,(T\,U) = (S\,T)\,U`.
The last law is stated for $`U` a string of indexes of $`T`, since out-of-range
indexes are unspecified in the book. Uses {uses "string_syntax"}[].
:::

:::proof "string_axioms_indexing"
Indexing is `List.getD`; the laws are `List.map_append`, `List.map_map`, and
the `getElem?` lemmas for appending and mapping.
:::

:::theorem "string_axioms_copies_update" (parent := "data_structures_core") (tags := "data, strings, hehner-2.2") (effort := "small") (lean := "LaPToP.DataStructures.Str.copies_zero, LaPToP.DataStructures.Str.copies_succ, LaPToP.DataStructures.Str.copies_three_example, LaPToP.DataStructures.Str.mem_star, LaPToP.DataStructures.Str.update_append_item_append, LaPToP.DataStructures.Str.update_example, LaPToP.DataStructures.Str.at_update, LaPToP.DataStructures.Str.copies_add, LaPToP.DataStructures.Str.copies_copies, LaPToP.DataStructures.Str.copies_mem_star")
Copies and update:
$`0*S = \mathit{nil}`, $`(n+1)*S = n*S; S`, and
$`(S; i; T) \triangleleft \leftrightarrow S \triangleright j = S; j; T`,
together with the book's examples $`3*(0; 1) = 0; 1; 0; 1; 0; 1` and
$`3; 5; 9 \triangleleft 2 \triangleright 8 = 3; 5; 8`, and the membership
condition for $`*S`. The copy count is a natural number here (the book allows
$`\infty`). Uses {uses "string_syntax"}[].
The Reference chapter's $`(S \triangleleft n \triangleright i)\,m = \mathbf{if}\ n = m\ \mathbf{then}\ i\ \mathbf{else}\ S\,m` (§11.3.5) is
`at_update` (for an index $`n` of $`S`), and $`{*}{*}S = {*}S` is `copies_mem_star` with
`copies_copies` ($`n{*}(k{*}S) = (n \times k){*}S`): the bunch-level statement is not modelled, since
$`{*}S` is a bunch of strings and $`{*}` is defined here on strings, not on bunches of strings.
Not modelled (strings of bunches): $`{\rm c\llap{/}}\mathit{nil} = 1`, $`{\rm c\llap{/}}(A;B) \leq {\rm c\llap{/}}A \times {\rm c\llap{/}}B`,
$`S; A; T : S; B; T = A : B`, and $`S\{A\}` (a string applied to a set of indices).
:::

:::proof "string_axioms_copies_update"
`List.replicate_succ'` with `List.flatten_append`; `List.set_append_right` for
the update law; the examples are by evaluation.
:::

:::theorem "string_axioms_order" (parent := "data_structures_core") (tags := "data, strings, hehner-2.2") (effort := "small") (lean := "LaPToP.DataStructures.Str.nil_le, LaPToP.DataStructures.Str.lt_append_item_append, LaPToP.DataStructures.Str.append_lt_append_of_lt")
"The order of two strings is determined by the items at the first index where
they differ. ... If there is no index where they differ, the shorter string
comes before the longer one." The axioms:
$`\mathit{nil} \le S < S; i; T` and
$`i < j \Rightarrow S; i; T < S; j; U`.
Lean's lexicographic order on lists is exactly this ordering. Uses
{uses "list_as_string"}[].
:::

:::proof "string_axioms_order"
Induction on the common prefix $`S`, using `List.nil_lt_cons` and
`List.cons_lt_cons_iff`.
:::

:::theorem "string_interval_laws" (parent := "data_structures_core") (tags := "data, strings, hehner-2.2") (effort := "small") (lean := "LaPToP.DataStructures.Str.len_interval, LaPToP.DataStructures.Str.interval_self, LaPToP.DataStructures.Str.interval_succ, LaPToP.DataStructures.Str.interval_append_interval, LaPToP.DataStructures.Str.mem_interval")
The string interval $`x;..y` ("$`x` to $`y`", same pronunciation as the bunch
$`x,..y`; $`x` included, $`y` excluded):
$`\leftrightarrow(x;..y) = y - x`,
$`x;..x = \mathit{nil}`, $`x;..x+1 = x`, and
$`(x;..y); (y;..z) = x;..z` for $`x \le y \le z`;
its items are exactly the integers $`i` with $`x \le i < y`. As for the bunch
interval, the length law uses the difference truncated at $`0`. Uses
{uses "string_syntax"}[] and {uses "bunch_interval"}[].
:::

:::proof "string_interval_laws"
The interval is `List.range` shifted by $`x`; the join law is `List.range_add`
after splitting $`z - x = (y - x) + (z - y)`.
:::

:::definition "list_packaging" (parent := "data_structures_core") (lean := "LaPToP.DataStructures.HList, LaPToP.DataStructures.Str.pack, LaPToP.DataStructures.HList.contents, LaPToP.DataStructures.HList.length, LaPToP.DataStructures.HList.domain, LaPToP.DataStructures.HList.at, LaPToP.DataStructures.HList.comp, LaPToP.DataStructures.HList.join, LaPToP.DataStructures.HList.modify")
"A list is a contained string." Although the string $`0; 1; 2` is not a single
item, the list $`[0; 1; 2]` is. List formation $`[S]` packages a string
(`Str.pack`); contents $`\sim L` unpackages it (`HList.contents`); $`\# L` is the
length, $`\square L = 0,..\# L` the domain (a bunch of naturals), $`L\,n` the item
at index $`n`, $`L\,M` composition ("$`L` composed with $`M`": the items of $`L`
at the indexes listed in $`M`), $`L ;; M` join, and $`n \to i \mid L` ("$`n` maps
to $`i` otherwise $`L`") the list like $`L` except that item $`n` is $`i`. Lists
are ordered lexicographically, like strings. In Lean `HList α` is a one-field
structure around a `Str α`, exactly as `HSet` packages a bunch in
{uses "bunch_vs_set"}[]; the operations act on contents via
{uses "string_syntax"}[].
:::

:::theorem "list_axioms" (parent := "data_structures_core") (tags := "data, lists, hehner-2.3") (effort := "small") (lean := "LaPToP.DataStructures.HList.pack_contents, LaPToP.DataStructures.HList.contents_pack, LaPToP.DataStructures.HList.length_pack, LaPToP.DataStructures.HList.domain_eq, LaPToP.DataStructures.HList.image_domain, LaPToP.DataStructures.HList.pack_join_pack, LaPToP.DataStructures.HList.at_pack, LaPToP.DataStructures.HList.pack_comp_pack, LaPToP.DataStructures.HList.modify_pack, LaPToP.DataStructures.HList.pack_inj, LaPToP.DataStructures.HList.pack_lt_pack, LaPToP.DataStructures.HList.image_pack_subset_image_pack, LaPToP.DataStructures.Str.pack_injective, LaPToP.DataStructures.HList.contents_example, LaPToP.DataStructures.HList.length_example, LaPToP.DataStructures.HList.at_example, LaPToP.DataStructures.HList.comp_example, LaPToP.DataStructures.HList.join_example, LaPToP.DataStructures.HList.modify_example, LaPToP.DataStructures.HList.modify_modify_example, LaPToP.DataStructures.HList.modify_swap_example, LaPToP.DataStructures.HList.length_eq_size_domain")
Hehner's List Theory axioms, for lists $`L`, strings $`S, T`, an index $`n` of
$`S`, an item $`i`, and bunches of strings $`A, B`:
$`[\sim L] = L` (list formation), $`\sim[S] = S` (contents),
$`\#[S] = \leftrightarrow S` (length), $`\square L = 0,..\# L` (domain),
$`[S] ;; [T] = [S; T]` (join), $`[S]\,n = S\,n` (indexing),
$`[S]\,[T] = [S\,T]` (composition), $`n \to i \mid [S] = [S \triangleleft n \triangleright i]`
(modification), $`[S] = [T] = (S = T)` (equation), $`[S] < [T] = (S < T)` (order),
and $`[A] : [B] = A : B` (inclusion, with $`[A]` the bunch of lists $`[S]` for
$`S : A`). The domain law is stated on the naturals, with a companion reading it
in the integers as the bunch interval {uses "bunch_interval"}[]. The remaining
axiom $`[S] \neq S` (structure) is not an equation in the typed model: a list and
its contents have different Lean types, which is exactly the distinction it
records. The book's worked examples ($`\sim[3;5;7;4]`, $`\#[3;5;7;4]`,
$`[3;5;7;4]\,2`, $`[3;5;7;4]\,[2;1;2]`, $`[3;5;7;4];;[2;1;2]`,
$`2 \to 22 \mid [10;..15]`, and the item swap) are checked by evaluation.
Uses {uses "list_packaging"}[] and {uses "string_axioms_indexing"}[].
The Reference chapter's $`\#L = {\rm c\llap{/}}\square L` (§11.3.6) is `length_eq_size_domain`.
Not modelled (multi-dimensional lists): the string-indexed modification $`(S;T) \to i \mid L` and the
indexing $`L @ \mathit{nil}`, $`L @ i`, $`L @ (S;T)` of §11.3.6; `HList` is one-dimensional.
:::

:::proof "list_axioms"
Every law is definitional (`rfl` / `Iff.rfl`) once the list operators are
defined on contents; equation and inclusion follow from injectivity of
packaging (`Set.image_subset_image_iff`).
:::

:::theorem "list_derived_laws" (parent := "data_structures_core") (tags := "data, lists, hehner-2.3") (effort := "small") (lean := "LaPToP.DataStructures.HList.comp_at, LaPToP.DataStructures.HList.comp_assoc, LaPToP.DataStructures.HList.comp_join")
Theorems Hehner derives from the axioms, for lists $`L, M, N` and natural $`n`:
$`(L\,M)\,n = L\,(M\,n)` (composition), $`(L\,M)\,N = L\,(M\,N)` (associativity),
and $`L\,(M ;; N) = L\,M ;; L\,N` (distributivity). The first two are stated for
$`n` an index of $`M`, respectively $`N` a list of indexes of $`M`, because the
book leaves out-of-range indexing unspecified. Uses {uses "list_axioms"}[] and
{uses "string_axioms_indexing"}[].
:::

:::proof "list_derived_laws"
Unpack to contents and apply the string indexing laws
(`Str.at_map_of_lt`, `Str.sub_sub`, `Str.sub_append`).
:::

:::definition "function_as_data" (parent := "data_structures_core") (lean := "LaPToP.FunctionTheory.Fn.comp, LaPToP.FunctionTheory.Fn.comp_domain, LaPToP.FunctionTheory.Fn.comp_apply, LaPToP.FunctionTheory.Fn.map, LaPToP.FunctionTheory.Fn.map_domain, LaPToP.FunctionTheory.Fn.map_apply, LaPToP.FunctionTheory.Fn.values_map, LaPToP.FunctionTheory.Fn.compFns, LaPToP.FunctionTheory.Fn.compFns_union, LaPToP.FunctionTheory.Fn.fnsComp, LaPToP.FunctionTheory.Fn.fnsComp_union, LaPToP.FunctionTheory.Fn.applyList, LaPToP.FunctionTheory.Fn.applyList_example")
Functions are ordinary data in LaPToP. Higher-order specifications and
implementations are therefore first-class, building on {uses "list_as_string"}[]
when the domain is finite or inductive.

Since a function is a value of the type `Fn α β` of {uses "function_notation"}[],
functions are elements in the sense of Section 2: bunches of functions
(as in {uses "function_on_bunches"}[] and {uses "function_inclusion"}[]), sets
of functions, and lists of functions (a list of functions applied pointwise to
an argument: $`[\mathit{suc}; \mathit{double}]\ 3 = 4; 6`) are all available. Function
composition (Section 3.2.2): "let $`f` and $`g` be functions such that $`g` is
not in the domain of $`f`. Then $`f\ g` is the composition of $`f` and $`g`,
defined by the Function Composition Axioms $`\square(f\ g) = \S x : \square g \cdot g\,x : \square f`
and $`(f\ g)\,x = f\,(g\,x)`" — `Fn.comp`, with an operator composed with a function
(`Fn.map`, as in $`-\mathit{suc}` and $`\neg\mathit{even} = \mathit{odd}`), and "like
application, composition distributes over bunch union": $`f\,(g, h) = f\,g, f\,h`,
$`(f, g)\,h = f\,h, g\,h`. The proviso "$`g` is not in the domain of $`f`" is
automatic in the typed model. Higher-order functions and the examples are in
{uses "higher_order_functions"}[].
:::

:::theorem "higher_order_functions" (parent := "data_structures_core") (tags := "functions, higher-order, hehner-3.2.1") (effort := "small") (lean := "LaPToP.FunctionTheory.Fn.check, LaPToP.FunctionTheory.Fn.suc_mem_check_domain, LaPToP.FunctionTheory.Fn.check_suc, LaPToP.FunctionTheory.Fn.domain_even_comp_suc, LaPToP.FunctionTheory.Fn.even_comp_suc_three, LaPToP.FunctionTheory.Fn.neg_suc_three, LaPToP.FunctionTheory.Fn.not_comp_even, LaPToP.FunctionTheory.Fn.not_all_iff_ex_not, LaPToP.FunctionTheory.Fn.not_ex_iff_all_not, LaPToP.FunctionTheory.Fn.neg_sup_eq_inf_neg, LaPToP.FunctionTheory.Fn.neg_inf_eq_sup_neg")
"A higher-order function is a function whose parameter is function-valued, and
whose argument must therefore be a function. For example, define predicate
$`\mathit{check} = \langle f : (0,..10) \to \mathit{int} \cdot \forall n : 0,..10 \cdot \mathit{even}\,(f\,n) \rangle`.
So $`\mathit{check}` applies to any function whose domain includes $`0,..10` ... and
when applied to any element in $`0,..10` has a result in $`\mathit{int}` ... Since
$`\mathit{suc} : \mathit{nat} \to \mathit{nat} : (0,..10) \to \mathit{int}` we can apply $`\mathit{check}` to
$`\mathit{suc}` and the result is $`\bot`." The domain of $`\mathit{check}` is the bunch of
functions $`(0,..10) \to \mathit{int}` of {uses "function_inclusion"}[]; $`\mathit{suc}` is in
it and $`\mathit{check}\ \mathit{suc} = \bot` since $`\mathit{suc}\ 0 = 1` is odd. The composition
examples of Section 3.2.2: $`\square(\mathit{even}\ \mathit{suc}) = \S x : \mathit{nat} \cdot x+1 : \mathit{int} = \mathit{nat}`,
$`(\mathit{even}\ \mathit{suc})\ 3 = \mathit{even}\ 4 = \top`, $`(-\mathit{suc})\ 3 = -4`, $`\neg\mathit{even} = \mathit{odd}`,
and "we can write the Duality Laws this way": $`\neg\forall f = \exists\neg f`,
$`\neg\exists f = \forall\neg f`, $`-\Downarrow f = \Uparrow -f`, $`-\Uparrow f = \Downarrow -f`. Uses
{uses "function_as_data"}[], {uses "predicates_relations"}[] and
{uses "quantifier_laws_numeric"}[].
:::
