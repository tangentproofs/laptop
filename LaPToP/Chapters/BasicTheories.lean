import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Basic Theories" =>

:::group "basic_theories_core"
Basic theories: numbers, bunches, sets, and the calculation style that
underpins later program reasoning in LaPToP.
:::

:::definition "bunch_vs_set" (parent := "basic_theories_core")
Hehner distinguishes *bunches* (unordered collections that may be used as
types/domains) from *sets* (values that can appear as elements of other
collections). This Blueprint node records that distinction for later formalization.
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
