import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Prelude" =>

:::group "prelude_core"
Notational conventions and elementary Boolean / predicate scaffolding used
throughout Hehner's *A Practical Theory of Programming*.
:::

:::author "hehner" (name := "Eric Hehner")
:::

:::definition "boolean_domain" (parent := "prelude_core")
Expressions in LaPToP evaluate in a Boolean domain. We write $`\top` for true
and $`\bot` for false, and treat predicates as Boolean-valued expressions over
a state.
:::

:::theorem "boolean_excluded_middle" (parent := "prelude_core") (owner := "hehner") (tags := "prelude, boolean") (effort := "small") (priority := "high")
For every Boolean $`b`, either $`b` or $`\neg b` holds:
$`b \lor \neg b`.
This is the classical excluded-middle sanity check for {uses "boolean_domain"}[].
:::

:::proof "boolean_excluded_middle"
Case-split on $`b`. Each case is immediate.
:::

```lean "boolean_excluded_middle"
theorem boolean_excluded_middle (b : Bool) :
    b = true ∨ b = false := by
  cases b <;> simp
```

:::definition "state_as_variables" (parent := "prelude_core")
A *state* assigns values to program variables. Informal specifications and
programs are expressions over those variables; refining one specification into
another is the central activity of the book.
:::
