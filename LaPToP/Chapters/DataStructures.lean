import Verso
import VersoManual
import VersoBlueprint
import LaPToP.DataStructures.Strings

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Data Structures" =>

:::group "data_structures_core"
Data structures as they appear in LaPToP: lists/strings, functions as data,
and related theories used when specifying programs that manipulate structure.
The string material is Hehner's Section 2.2; its formal counterpart is the Lean
module `LaPToP.DataStructures.Strings`.
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

:::theorem "string_axioms_copies_update" (parent := "data_structures_core") (tags := "data, strings, hehner-2.2") (effort := "small") (lean := "LaPToP.DataStructures.Str.copies_zero, LaPToP.DataStructures.Str.copies_succ, LaPToP.DataStructures.Str.copies_three_example, LaPToP.DataStructures.Str.mem_star, LaPToP.DataStructures.Str.update_append_item_append, LaPToP.DataStructures.Str.update_example")
Copies and update:
$`0*S = \mathit{nil}`, $`(n+1)*S = n*S; S`, and
$`(S; i; T) \triangleleft \leftrightarrow S \triangleright j = S; j; T`,
together with the book's examples $`3*(0; 1) = 0; 1; 0; 1; 0; 1` and
$`3; 5; 9 \triangleleft 2 \triangleright 8 = 3; 5; 8`, and the membership
condition for $`*S`. The copy count is a natural number here (the book allows
$`\infty`). Uses {uses "string_syntax"}[].
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

:::definition "function_as_data" (parent := "data_structures_core")
Functions are ordinary data in LaPToP. Higher-order specifications and
implementations are therefore first-class, building on {uses "list_as_string"}[]
when the domain is finite or inductive.
:::
