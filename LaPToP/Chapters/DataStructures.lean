import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Data Structures" =>

:::group "data_structures_core"
Data structures as they appear in LaPToP: lists/strings, functions as data,
and related theories used when specifying programs that manipulate structure.
:::

:::definition "list_as_string" (parent := "data_structures_core")
Hehner treats finite sequences uniformly (often called *strings* or *lists*).
Concatenation, length, and indexing are the primitive operations; many program
specifications are expressed directly in this theory.
:::

:::theorem "list_append_nil" (parent := "data_structures_core") (tags := "data, lists") (effort := "small")
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

:::definition "function_as_data" (parent := "data_structures_core")
Functions are ordinary data in LaPToP. Higher-order specifications and
implementations are therefore first-class, building on {uses "list_as_string"}[]
when the domain is finite or inductive.
:::
