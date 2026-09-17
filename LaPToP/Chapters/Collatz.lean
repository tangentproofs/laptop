import Verso
import VersoManual
import VersoBlueprint
import LaPToP.ProgramTheory.CollatzTime

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Collatz Time (Exercise 255)" =>

# Source Entries

:::group "collatz_core"
Exercise 255 of Hehner's *A Practical Theory of Programming* closes
Section 4.2.7: the Collatz program is "a famous program whose execution
time is considered to be unknown." The definitions and refinements below
are proved in `LaPToP.ProgramTheory.CollatzTime`. The open Collatz
conjecture itself is not a Blueprint node; see `MISSING.md` and the
Chapter 10 stub `LaPToP.Exercises.Ch4.exercise_255`.
:::

:::definition "collatz_step" (parent := "collatz_core")
The Collatz step sends an even natural number $`n` to $`n / 2` and an odd one
to $`3 * n + 1`.
:::

```lean "collatz_step"
def collatzStep (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1
```

:::theorem "collatz_time" (parent := "collatz_core") (tags := "programs, time, hehner-4.2.7, exercise-255") (effort := "small") (lean := "LaPToP.ProgramTheory.CollatzTime.CS, LaPToP.ProgramTheory.CollatzTime.assignN, LaPToP.ProgramTheory.CollatzTime.tick, LaPToP.ProgramTheory.CollatzTime.assignN_seq, LaPToP.ProgramTheory.CollatzTime.tick_seq, LaPToP.ProgramTheory.CollatzTime.step, LaPToP.ProgramTheory.CollatzTime.body, LaPToP.ProgramTheory.CollatzTime.Goal, LaPToP.ProgramTheory.CollatzTime.goal_refines, LaPToP.ProgramTheory.CollatzTime.IsCollatzTime, LaPToP.ProgramTheory.CollatzTime.TimeSpec, LaPToP.ProgramTheory.CollatzTime.time_refines")
"Finding the execution time of any program can always be done by
transforming the program into a function that expresses the execution time.
To illustrate how, we do Exercise 255 (Collatz), which is a famous program
whose execution time is considered to be unknown. Let $`n` be a natural
variable. Then, including recursive time,
$`n' = 1 \Leftarrow \mathbf{if}\ n = 1\ \mathbf{then}\ \mathit{ok}\ \mathbf{else\ if}\ \mathit{even}\ n\ \mathbf{then}\ n := n/2\ \mathbf{else}\ n := 3 \times n + 1.\ t := t+1.\ n' = 1`.
We can express the execution time as $`f\,n`, where function $`f` must satisfy
$`t' = t + f\,n \Leftarrow \mathbf{if}\ n = 1\ \mathbf{then}\ \mathit{ok}\ \mathbf{else\ if}\ \mathit{even}\ n\ \mathbf{then}\ n := n/2\ \mathbf{else}\ n := 3 \times n + 1.\ t := t+1.\ t' = t + f\,n`
which can be simplified to $`f\,1 = 0`, $`\mathit{even}\ n \land n > 1 \Rightarrow f\,n = 1 + f\,(n/2)`,
$`\mathit{odd}\ n \land n > 1 \Rightarrow f\,n = 1 + f\,(3 \times n + 1)`. ... If the execution time of some
program is $`n^2`, we consider that the execution time of that program is
known. Why is $`n^2` accepted as a time bound, and $`f\,n` as defined above not
accepted? ... The reason seems to be that function $`f` is unfamiliar; it has
not been well studied and we don't know much about it. It is not even known
whether $`f` is finite for all $`n > 0`. If it were as well studied and familiar as
square, we would accept it as a time bound." Proved: the refinement $`n' = 1 \Leftarrow \ldots`
with the recursive call as the specification (which says nothing about
termination), and, for any $`f : \mathit{nat} \to \mathit{xnat}` satisfying the three equations,
the timing refinement $`t' = t + f\,n \Leftarrow \ldots`. Nothing is claimed about the
finiteness of $`f` — that is the open Collatz conjecture, which is not a
Blueprint node (see `MISSING.md`). The step is that of {uses "collatz_step"}[]; uses
{uses "recursive_time"}[].
:::
