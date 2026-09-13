import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Recursion and Concurrency" =>

:::group "recursion_concurrency_core"
Recursive programs, time bounds, and concurrent composition as developed in
later chapters of *A Practical Theory of Programming*.
:::

:::definition "recursive_program" (parent := "recursion_concurrency_core")
A recursive program is the least fixed point of a monotonic transformer on
specifications. Termination and partial-correctness arguments are expressed in
the same predicate calculus as straight-line code.
:::

:::theorem "nat_repeat_zero" (parent := "recursion_concurrency_core") (tags := "recursion, nat") (effort := "small")
Repeating a step zero times is the identity on states represented as natural
numbers: $`\mathsf{repeat}\, f\, 0\, n = n`.
A kernel-level stand-in for the base case of {uses "recursive_program"}[].
:::

:::proof "nat_repeat_zero"
By the definition of `Nat.repeat`.
:::

```lean "nat_repeat_zero"
theorem nat_repeat_zero (f : Nat → Nat) (n : Nat) :
    Nat.repeat f 0 n = n := rfl
```

:::definition "concurrent_composition" (parent := "recursion_concurrency_core")
Concurrent composition combines independent (or weakly dependent) processes.
LaPToP treats concurrency in the same refinement framework as sequential
programs, once communication and timing are modeled. This node depends on
{uses "recursive_program"}[] for looping clients of concurrent servers.
:::
