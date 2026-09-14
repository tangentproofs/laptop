import Verso
import VersoManual
import VersoBlueprint
import LaPToP.ProgramTheory.WhileLoop

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Programming Language" =>

:::group "programming_language_core"
Hehner's Chapter 5: the programming notations of "several languages" —
control structures, scope, data structures, subprograms — explained as
refinement notations or as specifications in the theory of Chapter 4. The
while-loop of Section 5.2.0 is formalized in `LaPToP.ProgramTheory.WhileLoop`.
:::

:::definition "while_loop" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Spec.WhileRefines, LaPToP.ProgramTheory.Spec.whileRefines_iff, LaPToP.ProgramTheory.Spec.whileRefines_iff_cases, LaPToP.ProgramTheory.Spec.WhileRefines.mono, LaPToP.ProgramTheory.Spec.whileRefines_false")
"The while-loop of several languages has a syntax similar to
$`\mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od}`. ... We do not define the while-loop
as a specification the way we have defined previous programming notations.
Instead, if $`W` is an implementable specification, we consider the refinement
$`W \Leftarrow \mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od}` to be an alternative notation
for the refinement $`W \Leftarrow \mathbf{if}\ b\ \mathbf{then}\ P.\ W\ \mathbf{else}\ \mathit{ok}`."
Accordingly `Spec.WhileRefines W b P` is *defined* as that refinement — a
refinement notation, not a specification. By Refinement by Cases it is
$`W \Leftarrow b \land (P.\ W)` together with $`W \Leftarrow \neg b \land \mathit{ok}`; the body may
be refined in place; and a loop whose condition never holds is $`\mathit{ok}`. The
least-fixed-point account of loops and the reference-section law
$`\mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od} = t' \ge t \land \mathbf{if}\ b\ \mathbf{then}\ P.\ t := t+1.\ \mathbf{while} \ldots\ \mathbf{else}\ \mathit{ok}`
belong to Section 6.1.1 and are not formalized here. Uses
{uses "specification_notations"}[] and {uses "refinement_by_steps_parts_cases"}[].
:::

:::theorem "while_list_summation" (parent := "programming_language_core") (tags := "programs, loops, hehner-5.2.0") (effort := "small") (lean := "LaPToP.ProgramTheory.TimedListSummation.TLS, LaPToP.ProgramTheory.TimedListSummation.assignS, LaPToP.ProgramTheory.TimedListSummation.assignN, LaPToP.ProgramTheory.TimedListSummation.tick, LaPToP.ProgramTheory.TimedListSummation.assignS_seq, LaPToP.ProgramTheory.TimedListSummation.assignN_seq, LaPToP.ProgramTheory.TimedListSummation.tick_seq, LaPToP.ProgramTheory.TimedListSummation.Bt, LaPToP.ProgramTheory.TimedListSummation.cast_sub_succ_add_one, LaPToP.ProgramTheory.TimedListSummation.whileRefines_Bt")
The book's example: "to prove
$`s' = s + \Sigma L[n;..\# L] \land t' = t + \# L - n \Leftarrow \mathbf{while}\ n \neq \# L\ \mathbf{do}\ s := s + L\,n.\ n := n+1.\ t := t+1\ \mathbf{od}`
prove instead
$`\ldots \Leftarrow \mathbf{if}\ n \neq \# L\ \mathbf{then}\ s := s + L\,n.\ n := n+1.\ t := t+1.\ (s' = s + \Sigma L[n;..\# L] \land t' = t + \# L - n)\ \mathbf{else}\ \mathit{ok}`."
The state carries the time $`t`, the sum $`s` and the index $`n`, with the
bound $`0 \le n \le \# L` explicit as in {uses "list_summation"}[]. Uses
{uses "while_loop"}[], {uses "time_variable"}[] and {uses "substitution_law"}[].
:::

:::proof "while_list_summation"
Three applications of the Substitution Law, then
$`\Sigma L[n;..\# L] = L\,n + \Sigma L[n+1;..\# L]` and $`(\# L - (n+1)) + 1 = \# L - n`
for $`n < \# L`; the exit case is $`\Sigma L[\# L;..\# L] = 0`.
:::

:::theorem "unbounded_bound" (parent := "programming_language_core") (tags := "programs, loops, time, hehner-5.2.0") (effort := "medium") (lean := "LaPToP.ProgramTheory.UnboundedBound.XY, LaPToP.ProgramTheory.UnboundedBound.assignX, LaPToP.ProgramTheory.UnboundedBound.assignY, LaPToP.ProgramTheory.UnboundedBound.tick, LaPToP.ProgramTheory.UnboundedBound.assignX_seq, LaPToP.ProgramTheory.UnboundedBound.assignY_seq, LaPToP.ProgramTheory.UnboundedBound.tick_seq, LaPToP.ProgramTheory.UnboundedBound.sumF, LaPToP.ProgramTheory.UnboundedBound.sumF_succ, LaPToP.ProgramTheory.UnboundedBound.E, LaPToP.ProgramTheory.UnboundedBound.body, LaPToP.ProgramTheory.UnboundedBound.refine_E, LaPToP.ProgramTheory.UnboundedBound.whileRefines_E")
Exercise 320 (unbounded bound): in natural variables $`x`, $`y`,
$`\mathbf{while}\ \neg(x = y = 0)\ \mathbf{do}\ \mathbf{if}\ y > 0\ \mathbf{then}\ y := y - 1\ \mathbf{else}\ x := x - 1.\ \mathbf{new}\ n : \mathit{nat} \cdot y := n\ \mathbf{od}`
"decreases $`y` until it is 0; then it decreases $`x` by 1 and assigns an
arbitrary natural number to $`y`; ... and so on until both $`x` and $`y` are 0.
The problem is to find a time bound." Following the book, the arbitrary values
are the values of an arbitrary function $`f : \mathit{nat} \to \mathit{nat}` of $`x`, and
with $`s = \Sigma f[0;..x]` the refinement
$`t' = t + x + y + s \Leftarrow \mathbf{if}\ x = y = 0\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ \mathbf{if}\ y > 0\ \mathbf{then}\ y := y-1.\ t := t+1.\ t' = t+x+y+s\ \mathbf{else}\ x := x-1.\ y := f\,x.\ t := t+1.\ t' = t+x+y+s`
is proved "in three cases", and restated in while-loop notation: "the execution
time of the program is $`x + y + (\text{the sum of } x \text{ arbitrary natural numbers})`".
Uses {uses "while_loop"}[], {uses "time_variable"}[], {uses "substitution_law"}[]
and {uses "quantifier_numeric"}[].
:::

:::proof "unbounded_bound"
Case $`x = y = 0`: $`\mathit{ok}` gives $`t' = t` and $`s = 0`. Case $`y > 0`: the
Substitution Law twice, then $`t + 1 + x + (y-1) + s = t + x + y + s`. Case
$`x > 0 \land y = 0`: the Substitution Law three times, then
$`t + 1 + (x-1) + f(x-1) + \Sigma f[0;..x-1] = t + x + \Sigma f[0;..x]`.
:::
