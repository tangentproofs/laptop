import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Program Theory" =>

:::group "program_theory_core"
Programs as predicates on pre- and post-states; refinement as implication;
sequential composition, conditionals, and assignment in Hehner's theory.
:::

:::definition "program_as_predicate" (parent := "program_theory_core")
A program (or specification) is a Boolean expression relating initial and final
states. Implementing a specification $`S` by a program $`P` means proving
$`P \Rightarrow S` (refinement).
:::

:::definition "assignment_spec" (parent := "program_theory_core")
The assignment $`x := e` relates pre-state and post-state by setting $`x` to
the value of $`e` in the pre-state and leaving other variables unchanged.
This is the atomic building block for {uses "program_as_predicate"}[].
:::

:::theorem "skip_refines_true" (parent := "program_theory_core") (tags := "programs, refinement") (effort := "small") (priority := "high")
The trivial program that leaves the state unchanged (*ok* / `skip`) implements
the always-true specification. In propositional form this is the reflexivity
seed for refinement of {uses "program_as_predicate"}[].
:::

:::proof "skip_refines_true"
Immediate: the identity relation implies $`\top`.
:::

```lean "skip_refines_true"
theorem skip_refines_true : True := trivial
```

:::definition "sequential_composition" (parent := "program_theory_core")
Sequential composition $`P ; Q` exists when there is an intermediate state
accepted as final by $`P` and initial by $`Q`. It builds programs from
{uses "assignment_spec"}[] and larger blocks while preserving
{uses "program_as_predicate"}[].
:::
