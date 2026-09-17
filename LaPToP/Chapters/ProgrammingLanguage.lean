import Verso
import VersoManual
import VersoBlueprint
import LaPToP.ProgramTheory.WhileLoop
import LaPToP.ProgramTheory.ForLoop
import LaPToP.ProgramTheory.Scope
import LaPToP.ProgramTheory.Assertions
import LaPToP.ProgramTheory.Subprograms
import LaPToP.ProgramTheory.ExitLoop
import LaPToP.ProgramTheory.TwoDimSearch
import LaPToP.ProgramTheory.TimeDependence
import LaPToP.ProgramTheory.Arrays
import LaPToP.ProgramTheory.GoTo
import LaPToP.ProgramTheory.Functional

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Programming Language" =>

:::group "programming_language_core"
Hehner's Chapter 5: the programming notations of "several languages" —
control structures, scope, data structures, subprograms — explained as
refinement notations or as specifications in the theory of Chapter 4. In book
order: variable declaration and suspension (Section 5.0) are formalized in
`LaPToP.ProgramTheory.Scope`; arrays and records (Section 5.1) in
`LaPToP.ProgramTheory.Arrays`; the while-loop (Section 5.2.0) in
`LaPToP.ProgramTheory.WhileLoop`, the exit-loop (Section 5.2.1) in
`LaPToP.ProgramTheory.ExitLoop`, the two-dimensional search (Section 5.2.2) in
`LaPToP.ProgramTheory.TwoDimSearch`, the for-loop (Section 5.2.3) in
`LaPToP.ProgramTheory.ForLoop`; time and space dependence (Section 5.3) in
`LaPToP.ProgramTheory.TimeDependence`; assertions and backtracking
(Section 5.4) in `LaPToP.ProgramTheory.Assertions`; the value expression,
functions and procedures (Section 5.5) in `LaPToP.ProgramTheory.Subprograms`;
and functional programming with function refinement (Sections 5.8 and 5.8.0)
in `LaPToP.ProgramTheory.Functional`.
:::

:::definition "data_structures" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Arrays.AS, LaPToP.ProgramTheory.Arrays.assignElem, LaPToP.ProgramTheory.Arrays.assignA, LaPToP.ProgramTheory.Arrays.assignI, LaPToP.ProgramTheory.Arrays.assignA_seq, LaPToP.ProgramTheory.Arrays.assignI_seq, LaPToP.ProgramTheory.Arrays.assignElem_eq_assignA, LaPToP.ProgramTheory.Arrays.orElse_arrow_apply, LaPToP.ProgramTheory.Arrays.example₁, LaPToP.ProgramTheory.Arrays.example₁_naive, LaPToP.ProgramTheory.Arrays.example₂, LaPToP.ProgramTheory.Arrays.example₂_naive, LaPToP.ProgramTheory.Arrays.AS2, LaPToP.ProgramTheory.Arrays.assignElem2, LaPToP.ProgramTheory.Arrays.assignElem2_eq, LaPToP.ProgramTheory.Arrays.Person, LaPToP.ProgramTheory.Arrays.RS, LaPToP.ProgramTheory.Arrays.assignAge, LaPToP.ProgramTheory.Arrays.assignAge_eq")
"In most popular programming languages there is the notion of indexed
variable, usually called an “array” ... Let $`A` be an array name, let $`i` be
any expression of the index type, and let $`e` be any expression of the element
type. Then $`A\,i := e = A'\,i = e \land (\forall j \cdot j \neq i \Rightarrow A'\,j = A\,j) \land x' = x \land y' = y \land \ldots`
This says that after the assignment, element $`i` of $`A` equals $`e`, all other
elements of $`A` are unchanged, and all other variables are unchanged. ... The
Substitution Law $`x := e.\ P = (\text{for } x \text{ substitute } e \text{ in } P)` is very useful,
but unfortunately it does not work for array element assignment. For example,
$`A\,2 := 3.\ i := 2.\ A\,i := 4.\ A\,i = A\,2` should equal $`\top`, because $`i = 2` just before
the final binary expression, and $`A\,2 = A\,2` certainly equals $`\top`. If we try
to apply the Substitution Law, we get ... $`= A\,2 := 3.\ 4 = A\,2`. Here is a second
example of the failure of the Substitution Law for array elements.
$`A\,2 := 2.\ A\,(A\,2) := 3.\ A\,2 = 2`. This should equal $`\bot` because $`A\,2 = 3` just before
the final binary expression. But the Substitution Law says ... $`= A\,2 := 2.\ A\,2 = 2`.
The Substitution Law works only when the assignment has a simple name to the
left of $`:=`. Fortunately we can always rewrite an array element assignment in
that form. $`A\,i := e = A' = i \to e \mid A \land x' = x \land y' = y \land \ldots = A := i \to e \mid A`. ...
The only thing to remember about array element assignment is this: change
$`A\,i := e` to $`A := i \to e \mid A` before applying any programming theory. A
two-dimensional array element assignment $`A\,i\,j := e` must be changed to
$`A := (i; j) \to e \mid A`, and similarly for more dimensions. In program theory, an
array is a list variable, and array element assignment assigns the list
variable to a new list that is like the old list but differs in one item."
Records: "$`\mathit{person} = \text{“name”} \to \mathit{text} \mid \text{“age”} \to \mathit{nat}` ... a component (or
field) is assigned the same way we make an array element assignment. ... Just
as for array element assignment, the Substitution Law does not work for record
components. And the solution is also the same; just rewrite it like this:
$`p := \text{“age”} \to 18 \mid p`. No new theory is needed for records." An array is a
function $`\mathbb{N} \to \mathbb{Z}` ({uses "list_as_function"}[]); element assignment is
defined literally as the book's binary expression and proved equal to the
whole-array assignment $`A := i \to e \mid A` with $`i \to e \mid A` the function updated at
$`i`, which agrees with the {uses "selective_union"}[] of Function Theory. The
two examples are made precise: the first program equals its three assignments
(the final test holds) while the naive substitution gives $`\bot`; the second
program is $`\bot` while the naive substitution is $`A\,2 := 2`. The corrected
calculations go through the {uses "substitution_law"}[] for the whole-array
form ({uses "assignment_spec"}[]). Two-dimensional arrays and record
components are the same construction (one definitional lemma each).
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

:::definition "exit_loop" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Spec.ExitLoopRefines, LaPToP.ProgramTheory.Spec.exitLoopRefines_iff, LaPToP.ProgramTheory.Spec.exitLoopRefines_iff_cases, LaPToP.ProgramTheory.Spec.exitLoopRefines_ok_iff, LaPToP.ProgramTheory.Spec.ExitLoopRefines.mono, LaPToP.ProgramTheory.Spec.ExitLoopRefines.unroll, LaPToP.ProgramTheory.Spec.DeepExitRefines, LaPToP.ProgramTheory.Spec.deepExitRefines_iff, LaPToP.ProgramTheory.Spec.DeepExitRefines.unroll, LaPToP.ProgramTheory.Spec.DeepShallowRefines, LaPToP.ProgramTheory.Spec.DeepShallowRefines.outer, LaPToP.ProgramTheory.Spec.flagLoop, LaPToP.ProgramTheory.Spec.setDone, LaPToP.ProgramTheory.Spec.ExitLoopRefines.flag, LaPToP.ProgramTheory.Spec.newVarInit_flagLoop, LaPToP.ProgramTheory.Spec.ExitLoopExample.count_up")
"Some languages provide a command to jump out of the middle of a loop.
Suppose the loop $`\mathbf{do}\ P\ \mathbf{od}` with the additional syntax
$`\mathbf{exit\ when}\ b` allowed within $`P`, where $`b` is binary. ... As in
Subsection 5.2.0, we consider refinement by a loop with exits to be an
alternative notation. For example, if $`L` is an implementable specification,
then $`L \Leftarrow \mathbf{do}\ A.\ \mathbf{exit\ when}\ b.\ C\ \mathbf{od}` is an alternative
notation for $`L \Leftarrow A.\ \mathbf{if}\ b\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ C.\ L`. ...
$`\mathbf{exit}\ n\ \mathbf{when}\ b` ... means exit $`n` loops when $`b` is satisfied. For
example, $`P \Leftarrow \mathbf{do}\ A.\ \mathbf{do}\ B.\ \mathbf{exit}\ 2\ \mathbf{when}\ c.\ D\ \mathbf{od}.\ E\ \mathbf{od}`.
The refinement structure corresponding to this loop is $`P \Leftarrow A.\ Q`,
$`Q \Leftarrow B.\ \mathbf{if}\ c\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ D.\ Q` for some appropriately
defined $`Q`. ... The preceding example had a deep exit but no shallow exit,
leaving $`E` stranded in a dead area. Here is an example with both deep and
shallow exits. $`P \Leftarrow \mathbf{do}\ A.\ \mathbf{exit}\ 1\ \mathbf{when}\ b.\ C.\ \mathbf{do}\ D.\ \mathbf{exit}\ 2\ \mathbf{when}\ e.\ F.\ \mathbf{exit}\ 1\ \mathbf{when}\ g.\ H\ \mathbf{od}.\ I\ \mathbf{od}`.
The refinement structure corresponding to this loop is
$`P \Leftarrow A.\ \mathbf{if}\ b\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ C.\ Q`,
$`Q \Leftarrow D.\ \mathbf{if}\ e\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ F.\ \mathbf{if}\ g\ \mathbf{then}\ I.\ P\ \mathbf{else}\ H.\ Q`
for some appropriately defined $`Q`. Loops with exits can always be translated
easily to a refinement structure. But the reverse is not true; some refinement
structures require the introduction of new variables and even whole data
structures to encode them as loops with exits." Exactly as for the
{uses "while_loop"}[], the exit-loop is defined to be its refinement
structure, and $`\mathbf{exit}\ n` is handled by naming the inner loop, as the book
does; the two examples are the corresponding pairs of refinements. Proved: an
exit at the top of the body is $`\mathbf{while}\ \lnot b\ \mathbf{do}\ C\ \mathbf{od}`; the parts may
be refined in place; unrolling; and the book's remark that "a binary variable
can be introduced for the purpose of recording whether the goal has been
reached" — the exit-loop is translated to
$`\mathbf{new}\ \mathit{done} := \bot \cdot \mathbf{while}\ \lnot\mathit{done}\ \mathbf{do}\ A.\ \mathbf{if}\ b\ \mathbf{then}\ \mathit{done} := \top\ \mathbf{else}\ C\ \mathbf{od}`,
justified by the while-loop rule with {uses "variable_declaration"}[], and
declaring the flag recovers $`L` exactly. A small example,
$`x' = x \uparrow n \Leftarrow \mathbf{do}\ \mathbf{exit\ when}\ x \ge n.\ x := x+1\ \mathbf{od}`, is proved. The last
remark (refinement structures not expressible as exit-loops) is not
formalized. Uses {uses "refinement_by_steps_parts_cases"}[] and
{uses "specification_laws"}[].
:::

:::theorem "two_dimensional_search" (parent := "programming_language_core") (tags := "programs, search, time, hehner-5.2.2") (effort := "medium") (lean := "LaPToP.ProgramTheory.TwoDimSearch.S2, LaPToP.ProgramTheory.TwoDimSearch.assignI, LaPToP.ProgramTheory.TwoDimSearch.assignJ, LaPToP.ProgramTheory.TwoDimSearch.tick, LaPToP.ProgramTheory.TwoDimSearch.assignI_seq, LaPToP.ProgramTheory.TwoDimSearch.assignJ_seq, LaPToP.ProgramTheory.TwoDimSearch.tick_seq, LaPToP.ProgramTheory.TwoDimSearch.guard, LaPToP.ProgramTheory.TwoDimSearch.memRows, LaPToP.ProgramTheory.TwoDimSearch.memFrom, LaPToP.ProgramTheory.TwoDimSearch.found, LaPToP.ProgramTheory.TwoDimSearch.notFound, LaPToP.ProgramTheory.TwoDimSearch.P, LaPToP.ProgramTheory.TwoDimSearch.Q, LaPToP.ProgramTheory.TwoDimSearch.R, LaPToP.ProgramTheory.TwoDimSearch.not_memRows_self, LaPToP.ProgramTheory.TwoDimSearch.memFrom_zero, LaPToP.ProgramTheory.TwoDimSearch.memFrom_m, LaPToP.ProgramTheory.TwoDimSearch.memFrom_succ, LaPToP.ProgramTheory.TwoDimSearch.refine₁, LaPToP.ProgramTheory.TwoDimSearch.refine₂, LaPToP.ProgramTheory.TwoDimSearch.refine₃, LaPToP.ProgramTheory.TwoDimSearch.refine₄, LaPToP.ProgramTheory.TwoDimSearch.refine₅, LaPToP.ProgramTheory.TwoDimSearch.L0, LaPToP.ProgramTheory.TwoDimSearch.L1, LaPToP.ProgramTheory.TwoDimSearch.compiled₀, LaPToP.ProgramTheory.TwoDimSearch.compiled₁, LaPToP.ProgramTheory.TwoDimSearch.compiled₂, LaPToP.ProgramTheory.TwoDimSearch.within, LaPToP.ProgramTheory.TwoDimSearch.within_mono, LaPToP.ProgramTheory.TwoDimSearch.bookTR, LaPToP.ProgramTheory.TwoDimSearch.bookTQ, LaPToP.ProgramTheory.TwoDimSearch.book_timed_R_fails, LaPToP.ProgramTheory.TwoDimSearch.TR, LaPToP.ProgramTheory.TwoDimSearch.TR', LaPToP.ProgramTheory.TwoDimSearch.TQ, LaPToP.ProgramTheory.TwoDimSearch.TQ', LaPToP.ProgramTheory.TwoDimSearch.timed₁, LaPToP.ProgramTheory.TwoDimSearch.timed₂, LaPToP.ProgramTheory.TwoDimSearch.timed₃, LaPToP.ProgramTheory.TwoDimSearch.add_one_add_cast, LaPToP.ProgramTheory.TwoDimSearch.timed₄, LaPToP.ProgramTheory.TwoDimSearch.timed₅")
"To illustrate the preceding subsection, we can do Exercise 191: Write a
program to find a given item in a given 2-dimensional array. The execution
time must be linear in the product of the dimensions. Let the array be $`A`,
let its dimensions be $`n` by $`m`, and let the item we seek be $`x`. We will
indicate the position of $`x` in $`A` by the final values of natural variables
$`i` and $`j`. If $`x` occurs more than once, any of its positions will do. If it
does not occur, we will indicate that by $`i' = n`. The problem, except for
time, is $`P`: $`P = \mathbf{if}\ x : A\,(0,..n)\,(0,..m)\ \mathbf{then}\ x = A\,i'\,j'\ \mathbf{else}\ i' = n`
... $`Q = \mathbf{if}\ x : A\,(i,..n)\,(0,..m)\ \mathbf{then}\ x = A\,i'\,j'\ \mathbf{else}\ i' = n`
... $`R = \mathbf{if}\ x : A\,i\,(j,..m), A\,(i+1,..n)\,(0,..m)\ \mathbf{then}\ x = A\,i'\,j'\ \mathbf{else}\ i' = n`.
We now solve the problem in five easy pieces.
$`P \Leftarrow i := 0.\ i \le n \Rightarrow Q`;
$`i \le n \Rightarrow Q \Leftarrow \mathbf{if}\ i = n\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ i < n \Rightarrow Q`;
$`i < n \Rightarrow Q \Leftarrow j := 0.\ i < n \land j \le m \Rightarrow R`;
$`i < n \land j \le m \Rightarrow R \Leftarrow \mathbf{if}\ j = m\ \mathbf{then}\ i := i+1.\ i \le n \Rightarrow Q\ \mathbf{else}\ i < n \land j < m \Rightarrow R`;
$`i < n \land j < m \Rightarrow R \Leftarrow \mathbf{if}\ A\,i\,j = x\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ j := j+1.\ i < n \land j \le m \Rightarrow R`.
... To a compiler, after two uses of Refinement by Steps, the program appears
as $`P \Leftarrow i := 0.\ L0`, $`L0 \Leftarrow \mathbf{if}\ i = n\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ j := 0.\ L1`,
$`L1 \Leftarrow \mathbf{if}\ j = m\ \mathbf{then}\ i := i+1.\ L0\ \mathbf{else}\ \mathbf{if}\ A\,i\,j = x\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ j := j+1.\ L1`.
To add recursive time, ... we can get away with a single time increment placed
just before the test $`j = m`. ... The time remaining is at most the area
remaining to be searched." The array is a function, and the bunch membership
$`x : A\,(i,..n)\,(0,..m)` is the predicate that some $`A\,a\,b = x` with
$`i \le a < n`, $`b < m`. The five refinements are proved as stated and the
compiler's three pieces derived by {uses "refinement_by_steps_parts_cases"}[].
A correction, recorded: the book's timed refinements use the bounds
$`t' \le t + n \times m`, $`i \le n \Rightarrow t' \le t + (n-i) \times m` and
$`i < n \land j \le m \Rightarrow t' \le t + (n-i) \times m - j` both before and after the
increment. With one increment per iteration of $`L1` each row costs $`m+1`
increments (the tests $`j = 0, \ldots, m`), so the book's fourth timed refinement
is false in both branches — for $`n = 1`, $`m = 0` the program takes one time unit
where the bound allows none (`book_timed_R_fails`). The corrected bounds
$`t' \le t + n \times (m+1)`, $`i \le n \Rightarrow t' \le t + (n-i) \times (m+1)`,
$`i < n \land j \le m \Rightarrow t' \le t + (n-i) \times (m+1) - j` before the increment and
$`\ldots - j - 1` after it are proved in the same five pieces, with the time in
$`\mathit{xnat}` as in {uses "time_variable"}[]; the execution time is still linear
in the product of the dimensions. This example "illustrates the preceding
subsection", {uses "exit_loop"}[]. Uses {uses "specification_laws"}[].
:::

:::definition "for_loop" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Spec.ForRefines, LaPToP.ProgramTheory.Spec.ForRefines.step, LaPToP.ProgramTheory.Spec.ForRefines.exit, LaPToP.ProgramTheory.Spec.forRefines_self, LaPToP.ProgramTheory.Spec.iterSeq, LaPToP.ProgramTheory.Spec.iterSeq_mono, LaPToP.ProgramTheory.Spec.ForRefines.unroll, LaPToP.ProgramTheory.Spec.forRefines_invariant")
"Let us use the syntax $`\mathbf{for}\ i := m;..n\ \mathbf{do}\ P\ \mathbf{od}` where $`i` is
a fresh name called the for-loop index, $`m` and $`n` are integer expressions such
that $`m \le n`, and $`P` is a specification ... iteration continues up to but
excluding $`i = n` ... $`i` is not a state variable (so it cannot be assigned
within $`P`), and the initial values of $`m` and $`n` control the iteration. ...
Specification $`F\,i` describes the computation from index $`i` to the end. ...
To prove $`F\,m \Leftarrow \mathbf{for}\ i := m;..n\ \mathbf{do}\ P\ \mathbf{od}` prove
$`F\,i \Leftarrow i : m,..n \land (P.\ F(i+1))` and $`F\,n \Leftarrow \mathit{ok}`." As with
{uses "while_loop"}[], `Spec.ForRefines F m n P` is *defined* as these two proof
obligations; the index is a parameter of the body and of the indexed
specification, and the bounds are natural numbers. The rule has the honest
consequence that $`F\,m` is refined by the $`n - m`-fold unrolling
$`P\,m.\ P(m+1).\ \ldots\ P(n-1).\ \mathit{ok}`. The invariant special case
"$`A\,m \Rightarrow A'\,n \Leftarrow \mathbf{for}\ i := m;..n\ \mathbf{do}\ i : m,..n \land A\,i \Rightarrow A'(i+1)\ \mathbf{od}`",
for which "there is nothing to prove", is proved once and for all. Uses
{uses "refinement_by_steps_parts_cases"}[].
:::

:::theorem "binary_exponentiation" (parent := "programming_language_core") (tags := "programs, loops, hehner-5.2.3") (effort := "small") (lean := "LaPToP.ProgramTheory.BinaryExponentiation.XS, LaPToP.ProgramTheory.BinaryExponentiation.assignX, LaPToP.ProgramTheory.BinaryExponentiation.assignX_seq, LaPToP.ProgramTheory.BinaryExponentiation.F, LaPToP.ProgramTheory.BinaryExponentiation.forRefines_F, LaPToP.ProgramTheory.BinaryExponentiation.refine_pow, LaPToP.ProgramTheory.BinaryExponentiation.refine_pow_unrolled")
Exercise 179: "let $`x` be a natural variable and $`n` be a natural constant. The
binary exponentiation problem can be solved by some initialization and then a
for-loop: $`x' = 2^n \Leftarrow x := 1.\ \mathbf{for}\ i := 0;..n\ \mathbf{do}\ x := 2 \times x\ \mathbf{od}`.
To prove it, we need to find an indexed specification $`F\,i` such that
$`x' = 2^n \Leftarrow x := 1.\ F\,0`, $`F\,i \Leftarrow i : 0,..n \land (x := 2 \times x.\ F(i+1))`,
$`F\,n \Leftarrow \mathit{ok}`. The specification we want is $`F\,i = (x' = x \times 2^{n-i})`,
which says that the final product is the product so far times the remaining
factors. The three proofs are easy." Also the unrolled form. Uses
{uses "for_loop"}[] and {uses "substitution_law"}[].
:::

:::theorem "for_loop_timing" (parent := "programming_language_core") (tags := "programs, loops, time, hehner-5.2.3") (effort := "small") (lean := "LaPToP.ProgramTheory.ForLoopTiming.TS, LaPToP.ProgramTheory.ForLoopTiming.addT, LaPToP.ProgramTheory.ForLoopTiming.addT_seq, LaPToP.ProgramTheory.ForLoopTiming.F, LaPToP.ProgramTheory.ForLoopTiming.forRefines_F, LaPToP.ProgramTheory.ForLoopTiming.refine_time, LaPToP.ProgramTheory.ForLoopTiming.forRefines_const")
"The time taken by the body of a for-loop may be a function $`f` of the
iteration $`i`. To prove $`t' = t + \Sigma i : m,..n \cdot f\,i \Leftarrow \mathbf{for}\ i := m;..n\ \mathbf{do}\ t' = t + f\,i\ \mathbf{od}`
define $`F\,i = (t' = t + \Sigma j : i,..n \cdot f\,j)` and prove
$`t' = t + \Sigma i : m,..n \cdot f\,i \Leftarrow F\,m`, $`F\,i \Leftarrow i : m,..n \land (t' = t + f\,i.\ F(i+1))`,
$`F\,n \Leftarrow \mathit{ok}`, all of which are easy. When the body takes constant time
$`c`, this simplifies to $`t' = t + (n-m) \times c \Leftarrow \mathbf{for}\ i := m;..n\ \mathbf{do}\ t' = t + c\ \mathbf{od}`."
Uses {uses "for_loop"}[], {uses "time_variable"}[] and {uses "quantifier_numeric"}[].
:::

:::theorem "add_one_to_each" (parent := "programming_language_core") (tags := "programs, loops, lists, hehner-5.2.3") (effort := "medium") (lean := "LaPToP.ProgramTheory.AddOneToEach.LS, LaPToP.ProgramTheory.AddOneToEach.assignL, LaPToP.ProgramTheory.AddOneToEach.assignL_seq, LaPToP.ProgramTheory.AddOneToEach.S, LaPToP.ProgramTheory.AddOneToEach.F, LaPToP.ProgramTheory.AddOneToEach.refine_S, LaPToP.ProgramTheory.AddOneToEach.forRefines_F, LaPToP.DataStructures.HList.length_contents_modify, LaPToP.DataStructures.HList.at_modify_self, LaPToP.DataStructures.HList.at_modify_ne")
Exercise 326: "add 1 to each item in a list. The specification $`S` is defined as
$`S = (\# L' = \# L \land \forall n : \square L \cdot L'\,n = L\,n + 1)`. Now we need a
specification $`F\,i` that describes the iterations from $`i` to the end: adding
1 to each item from index $`i` to (not including) $`\# L`:
$`F\,i = (\# L' = \# L \land (\forall n : 0,..i \cdot L'\,n = L\,n) \land (\forall n : i,..\# L \cdot L'\,n = L\,n + 1))`.
Then $`S = F\,0`. To prove $`F\,0 \Leftarrow \mathbf{for}\ i := 0;..\# L\ \mathbf{do}\ L := i \to L\,i + 1 \mid L\ \mathbf{od}`
we must prove two theorems: $`F\,i \Leftarrow i : 0,..\# L \land (L := i \to L\,i + 1 \mid L.\ F(i+1))`
and $`F(\# L) \Leftarrow \mathit{ok}`." The loop bound is the length of the list in the
initial state; since the body preserves the length, the specifications carry the
antecedent $`\# L = N` for a constant $`N`. The body is the list modification of
{uses "list_packaging"}[]. Uses {uses "for_loop"}[] and {uses "substitution_law"}[].
:::

:::proof "add_one_to_each"
The book's calculation: after the Substitution Law, $`\#(i \to L\,i + 1 \mid L) = \# L`;
divide the domain $`0,..i+1` into $`0,..i` and $`i`; for $`n : 0,..i` and for
$`n : i+1,..\# L` the modified list agrees with $`L`, and at $`i` it is $`L\,i + 1`.
:::

:::definition "go_to" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.GoTo.A, LaPToP.ProgramTheory.GoTo.B, LaPToP.ProgramTheory.GoTo.C, LaPToP.ProgramTheory.GoTo.D, LaPToP.ProgramTheory.GoTo.E, LaPToP.ProgramTheory.GoTo.A_refines, LaPToP.ProgramTheory.GoTo.B_refines, LaPToP.ProgramTheory.GoTo.C_refines, LaPToP.ProgramTheory.GoTo.D_refines")
"Suppose the fast exponentiation program $`z' = x^y` of Subsection 4.2.6
Exercise 180 were written as follows, using “⦂” for labeling the target of a
$`\mathbf{go\ to}` (written $`{:}` below):
$`A{:}\ z := 1.\ \mathbf{if}\ \mathit{even}\ y\ \mathbf{then}\ \mathbf{go\ to}\ C\ \mathbf{else}\ B{:}\ z := z \times x.\ y := y-1.\ C{:}\ \mathbf{if}\ y = 0\ \mathbf{then}\ \mathbf{go\ to}\ E\ \mathbf{else}\ D{:}\ x := x \times x.\ y := y/2.\ \mathbf{if}\ \mathit{even}\ y\ \mathbf{then}\ \mathbf{go\ to}\ D\ \mathbf{else}\ \mathbf{go\ to}\ B`.
Straight from the program, what needs to be proved is the following:
$`A \Leftarrow z := 1.\ \mathbf{if}\ \mathit{even}\ y\ \mathbf{then}\ C\ \mathbf{else}\ B`; $`B \Leftarrow z := z \times x.\ y := y-1.\ C`;
$`C \Leftarrow \mathbf{if}\ y = 0\ \mathbf{then}\ E\ \mathbf{else}\ D`;
$`D \Leftarrow x := x \times x.\ y := y/2.\ \mathbf{if}\ \mathit{even}\ y\ \mathbf{then}\ D\ \mathbf{else}\ B` for appropriately
defined $`A`, $`B`, $`C`, $`D`, and $`E`. The difficulty with $`\mathbf{go\ to}`, as with loop
constructs, is inventing specifications that were not recorded during program
construction. In this example, the appropriate specifications are:
$`B = \mathit{odd}\ y \Rightarrow z' = z \times x^y`, $`C = \mathit{even}\ y \Rightarrow z' = z \times x^y`,
$`D = \mathit{even}\ y \land y > 0 \Rightarrow z' = z \times x^y`." A label is a specification and a
$`\mathbf{go\ to}` is a call of it; the four refinements are proved on the state of
{uses "fast_exponentiation"}[] (mostly from its refinements), with $`A = z' = x^y`
and $`E = \mathit{ok}` — the book leaves those two to the reader. Cf. {uses "exit_loop"}[].
:::

:::definition "variable_declaration" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Spec.newVar, LaPToP.ProgramTheory.Spec.newVarInit, LaPToP.ProgramTheory.Spec.assignLocal, LaPToP.ProgramTheory.Spec.liftNonlocal, LaPToP.ProgramTheory.Spec.assignLocal_seq, LaPToP.ProgramTheory.Spec.implementable_newVar, LaPToP.ProgramTheory.Spec.not_implementable_newVar, LaPToP.ProgramTheory.Spec.newVar_liftNonlocal, LaPToP.ProgramTheory.Spec.newVarInit_eq, LaPToP.ProgramTheory.Spec.newVar_newVar, LaPToP.ProgramTheory.Spec.newVar_mono, LaPToP.ProgramTheory.Spec.assignNonlocal, LaPToP.ProgramTheory.Spec.assignNonlocal_seq, LaPToP.ProgramTheory.ScopeExamples.YZ, LaPToP.ProgramTheory.ScopeExamples.St, LaPToP.ProgramTheory.ScopeExamples.example₁, LaPToP.ProgramTheory.ScopeExamples.example₂, LaPToP.ProgramTheory.ScopeExamples.example₃")
"We can express a variable declaration together with the specification to
which it applies as a binary expression in the initial and final state:
$`\mathbf{new}\ x : T \cdot P = \exists x, x' : T \cdot P`. Specification $`P` is an
expression in the initial and final values of all nonlocal (already declared)
variables plus the newly declared local variable. Specification
$`\mathbf{new}\ x : T \cdot P` is an expression in the nonlocal variables only. For a
variable declaration to be implementable, its type must be nonempty." In Lean
the state inside the scope is the product $`\sigma \times T` of the nonlocal state
and the local variable, and `Spec.newVar P` is literally $`\exists x, x' : T \cdot P`;
a nonlocal specification is lifted into the scope leaving the local variable
unchanged, and assignments inside the scope are to the local or to a nonlocal
variable. Proved: implementability for nonempty $`T` (and unimplementability
for empty $`T`), that declaring an unused variable changes nothing, the
initializing declaration $`\mathbf{new}\ x : T := e \cdot P = \exists x : e \cdot \exists x' : T \cdot P`
as a declaration followed by a local assignment, nesting
$`\mathbf{new}\ x, y : T \cdot P = \exists x, x', y, y' : T \cdot P`, monotonicity, and the book's
examples in nonlocal integer variables $`y, z`:
$`\mathbf{new}\ x : \mathit{int} \cdot x := 2.\ y := x + z = (y' = 2 + z \land z' = z)`,
$`\mathbf{new}\ x : \mathit{int} \cdot y := x = (z' = z)` ("the initial value of the local
variable is an arbitrary value of its type"), and
$`\mathbf{new}\ x : \mathit{int} \cdot y := x - x = (y' = 0 \land z' = z)`. Uses
{uses "specification_notations"}[], {uses "quantifier_forall_exists"}[] and
{uses "substitution_law"}[].
:::

:::definition "variable_suspension" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Spec.frame, LaPToP.ProgramTheory.Spec.frame_empty_top, LaPToP.ProgramTheory.Spec.frame_singleton_eq, LaPToP.ProgramTheory.Spec.frame_univ, LaPToP.ProgramTheory.Spec.frame_ok, LaPToP.ProgramTheory.Spec.frame_frame, LaPToP.ProgramTheory.Spec.refines_frame, LaPToP.ProgramTheory.Spec.frame_mono, LaPToP.ProgramTheory.Spec.frame_cond, LaPToP.ProgramTheory.Spec.frame_seq, LaPToP.ProgramTheory.Spec.frame_assign, LaPToP.ProgramTheory.ScopeExamples.assign_sum_eq_frame_newVar")
"We may wish, temporarily, to narrow our focus to a part of the state space.
... The frame notation is the formal way of saying “and all other variables
(even the ones we cannot say because they are covered by local declarations) are
unchanged”. If the state variables not included in the frame are $`w` and $`z`,
then $`\mathbf{frame}\ x, y \cdot P = P \land w' = w \land z' = z`." On states of
{uses "state_as_variables"}[], `Spec.frame xs P` conjoins $`P` with $`v' = v` for
every variable $`v` outside the frame. The book's remark that "if we had defined
$`\mathbf{frame}` first, we could have defined $`\mathit{ok}` and assignment formally
at the high level" — $`\mathit{ok} = \mathbf{frame} \cdot \top`, $`x := e = \mathbf{frame}\ x \cdot x' = e` —
is proved, together with: the full frame is no restriction, $`\mathbf{frame}\ xs \cdot \mathit{ok} = \mathit{ok}`,
nested frames intersect, a frame strengthens and is monotonic, a frame
distributes over $`\mathbf{if}`, a sequence of framed specifications refines the
framed sequence, and a framed variable may be assigned freely. The book's
example $`s := \Sigma L = \mathbf{frame}\ s \cdot \mathbf{new}\ n : \mathit{nat} \cdot s' = \Sigma L`
("first we reduce the state space to $`s`; ... next we introduce local variable
$`n`") is checked on the state of {uses "list_summation"}[]. Uses
{uses "variable_declaration"}[] and {uses "assignment_spec"}[].
:::

:::definition "time_dependence" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.TimeDependence.TD, LaPToP.ProgramTheory.TimeDependence.assignT, LaPToP.ProgramTheory.TimeDependence.assignDeadline, LaPToP.ProgramTheory.TimeDependence.tick, LaPToP.ProgramTheory.TimeDependence.assignT_seq, LaPToP.ProgramTheory.TimeDependence.RespectsClock, LaPToP.ProgramTheory.TimeDependence.respectsClock_assignDeadline, LaPToP.ProgramTheory.TimeDependence.respectsClock_tick, LaPToP.ProgramTheory.TimeDependence.respectsClock_cond, LaPToP.ProgramTheory.TimeDependence.respectsClock_seq, LaPToP.ProgramTheory.TimeDependence.not_respectsClock_assignT_const, LaPToP.ProgramTheory.TimeDependence.waitUntil, LaPToP.ProgramTheory.TimeDependence.respectsClock_waitUntil, LaPToP.ProgramTheory.TimeDependence.waitUntil_case_ge, LaPToP.ProgramTheory.TimeDependence.waitUntil_case_lt, LaPToP.ProgramTheory.TimeDependence.waitUntil_refines, LaPToP.ProgramTheory.TimeDependence.waitUntil_whileRefines")
"Some programming languages provide a clock, or a delay, or other
time-dependent features. Our examples have used the time variable $`t` as a
ghost, or auxiliary variable, never affecting the course of a computation. ...
But if there is a readable clock available as a time source during a
computation, it can be used to affect the computation. The assignment
$`\mathit{deadline} := t+5` is allowed, as is $`\mathbf{if}\ t \le \mathit{deadline}\ \mathbf{then} \ldots \mathbf{else} \ldots`.
But the assignment $`t := 5` is not allowed. We can look at the clock, but not
reset it arbitrarily; all assignments to $`t` must correspond to the passage of
time (according to some measure); otherwise $`t` would not represent the time.
... We may occasionally want to specify the passage of time. For example, we
may want the computation to “wait until time $`w`”. Let us invent a notation
for it, and define it formally as $`\mathbf{wait\ until}\ w = t := t \uparrow w`. Because we
are not allowed to reset the clock, $`t := t \uparrow w` is not acceptable as a
program until we refine it by a program. Letting time be an extended natural
and using recursive time,
$`\mathbf{wait\ until}\ w \Leftarrow \mathbf{if}\ t \ge w\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ t := t+1.\ \mathbf{wait\ until}\ w`
and we obtain a busy-wait loop. We can prove this refinement by cases. First,
$`t \ge w \land \mathit{ok} = t \ge w \land (t := t) \Rightarrow t := t \uparrow w`. Second,
$`t < w \land (t := t+1.\ t := t \uparrow w) = t+1 \le w \land (t := (t+1) \uparrow w) = t+1 \le w \land (t := w) = t < w \land (t := t \uparrow w) \Rightarrow t := t \uparrow w`.
... Our space variable $`s`, like the time variable $`t`, has so far been used to
prove things about space usage, not to affect the computation. ... Like $`t`,
$`s` can be read but not written arbitrarily." The clock discipline is the
predicate "the specification never decreases $`t`": $`\mathit{deadline} := t+5`,
$`t := t+1`, the clock-dependent conditional, sequential composition and
$`\mathbf{wait\ until}\ w` respect it, and $`t := 5` does not (from $`t = 7` it turns the
clock back). The busy-wait refinement is proved by the two cases exactly as
the book calculates them — the second uses $`t < w \Rightarrow t+1 \le w` in $`\mathit{xnat}`
and the {uses "substitution_law"}[] — and combined by
{uses "refinement_by_steps_parts_cases"}[]; it is also stated as the
{uses "while_loop"}[] $`\mathbf{while}\ t < w\ \mathbf{do}\ t := t+1\ \mathbf{od}`. Not formalized:
the real-time variant (Exercise 333(b)), and the space variable, since space
(Section 4.3) is not modelled in this development. Uses {uses "time_variable"}[]
and {uses "recursive_time"}[].
:::

:::definition "assertions" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Assertions.AT, LaPToP.ProgramTheory.Assertions.assignX, LaPToP.ProgramTheory.Assertions.assignY, LaPToP.ProgramTheory.Assertions.assignX_seq, LaPToP.ProgramTheory.Assertions.assert, LaPToP.ProgramTheory.Assertions.assert_of_holds, LaPToP.ProgramTheory.Assertions.assert_of_not, LaPToP.ProgramTheory.Assertions.assert_true, LaPToP.ProgramTheory.Assertions.assert_refines_ensure, LaPToP.ProgramTheory.Assertions.implementable_assert, LaPToP.ProgramTheory.Assertions.implementable_assert', LaPToP.ProgramTheory.Assertions.assert_seq_of_not, LaPToP.ProgramTheory.Assertions.assert_seq_of_holds")
"As a safety check, some programming languages include the notation
$`\mathbf{assert}\ b` where $`b` is binary, to mean “$`b` is true”. ... It is
executed by checking that $`b` is true; if it is, execution continues normally,
but if not, an error message is printed and execution is suspended. ...
$`\mathbf{assert}\ b = \mathbf{if}\ b\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ \mathbf{screen}!\ \text{“error”}.\ \mathbf{wait\ until}\ \infty`.
If $`b` is true, $`\mathbf{assert}\ b` is the same as $`\mathit{ok}`. If $`b` is false, an
error message is printed, and execution cannot proceed in finite time to any
following actions." Output ($`\mathbf{screen}!`) is a Chapter 9 notation with no
counterpart here, and $`\mathbf{wait\ until}\ \infty` is $`t := \infty`; so the
else-branch is formalized as what the theory of Chapter 4 observes — the final
time is $`\infty` — on a state with a time variable, and the printed message is
not modelled. Proved: $`\mathbf{assert}\ b = \mathit{ok}` when $`b` holds and $`t' = \infty`
otherwise, $`\mathbf{assert}\ \top = \mathit{ok}` ("all assertions are redundant" in a
correct program), implementability with nondecreasing time, and that a false
assertion followed by $`P` starts $`P` at time $`\infty`. Uses
{uses "specification_notations"}[] and {uses "time_variable"}[].
:::

:::theorem "backtracking" (parent := "programming_language_core") (tags := "programs, backtracking, hehner-5.4.0") (effort := "small") (lean := "LaPToP.ProgramTheory.Spec.ensure, LaPToP.ProgramTheory.Spec.ensure_eq_cond, LaPToP.ProgramTheory.Spec.ensure_of_holds, LaPToP.ProgramTheory.Spec.ensure_true, LaPToP.ProgramTheory.Spec.implementable_ensure_iff, LaPToP.ProgramTheory.Spec.seq_ensure, LaPToP.ProgramTheory.Spec.or_seq_ensure, LaPToP.ProgramTheory.Spec.or_refines_left, LaPToP.ProgramTheory.Spec.or_refines_right, LaPToP.ProgramTheory.Assertions.choice, LaPToP.ProgramTheory.Assertions.choice_ensure, LaPToP.ProgramTheory.Assertions.implementable_choice")
"If $`P` and $`Q` are implementable specifications, so is $`P \lor Q`. ... We
could save this programming step by making disjunction a programming connective,
perhaps using the notation $`\mathbf{or}`. ... We introduce the notation
$`\mathbf{ensure}\ b` where $`b` is binary, to mean “make $`b` true without changing
anything”: $`\mathbf{ensure}\ b = \mathbf{if}\ b\ \mathbf{then}\ \mathit{ok}\ \mathbf{else}\ b \land \mathit{ok} = b \land \mathit{ok}`.
... When $`b` is false ... this is unimplementable (unless $`b` is identically
$`\top`). However, in combination with other constructs, the whole may be
implementable":
$`x := 0\ \mathbf{or}\ x := 1.\ \mathbf{ensure}\ x = 1 = (x' = 1 \land y' = y) = x := 1`.
Proved: both forms of $`\mathbf{ensure}`, $`\mathbf{ensure}\ \top = \mathit{ok}`,
$`\mathbf{ensure}\ b` is implementable iff $`b` holds in every state, $`\mathbf{ensure}`
refines $`\mathbf{assert}`, $`P.\ \mathbf{ensure}\ b` filters the results of $`P` by $`b`,
$`(P\ \mathbf{or}\ Q).\ \mathbf{ensure}\ b = (P.\ \mathbf{ensure}\ b)\ \mathbf{or}\ (Q.\ \mathbf{ensure}\ b)`
(the choice is made to satisfy the later $`\mathbf{ensure}`), $`P \lor Q \Leftarrow P`,
$`P \lor Q \Leftarrow Q`, and the book's example. Uses {uses "assertions"}[],
{uses "specification_implementability"}[] and {uses "substitution_law"}[].
:::

:::proof "backtracking"
The example: $`P.\ \mathbf{ensure}\ b` is $`P \land b'`; the disjunct $`x := 0` is
excluded by $`x' = 1`, leaving $`x := 1`.
:::

:::definition "value_expression" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Spec.value, LaPToP.ProgramTheory.Spec.ValueDetermined, LaPToP.ProgramTheory.Spec.valueDetermined_of_deterministic, LaPToP.ProgramTheory.Spec.value_spec, LaPToP.ProgramTheory.Spec.value_axiom, LaPToP.ProgramTheory.Spec.value_assign, LaPToP.ProgramTheory.Spec.value_impl, LaPToP.ProgramTheory.Spec.ValueExamples.xinc, LaPToP.ProgramTheory.Spec.ValueExamples.value_xinc, LaPToP.ProgramTheory.Spec.ValueExamples.assignY_value, LaPToP.ProgramTheory.Spec.ValueExamples.side_effect_ne")
"Let $`P` be a specification and $`e` be an expression in unprimed variables.
Then $`P\ \mathbf{value}\ e` expresses the value that would be obtained by executing
$`P` and then evaluating $`e`. But $`P` is not executed, and all variables are
unchanged. ... The value expression axiom is $`P.\ (P\ \mathbf{value}\ e) = e` except
that $`(P\ \mathbf{value}\ e)` is not subject to double-priming in sequential
composition, nor to substitution when using the Substitution Law. For example,
$`\top = x := x+1.\ (x := x+1\ \mathbf{value}\ x) = x = ((x := x+1\ \mathbf{value}\ x) = x+1)`.
... $`y := (x := x+1\ \mathbf{value}\ x) = y := x+1`. The expression $`P\ \mathbf{value}\ e` can be
implemented as follows. Replace each nonlocal variable within $`P` and $`e` that
is assigned within $`P` by a fresh local variable initialized to the value of the
nonlocal variable. Then execute the modified $`P` and evaluate the modified
$`e`. ... State changes resulting from the evaluation of an expression are called
“side-effects”. With side-effects, mathematical reasoning is not possible. ...
If a programming language allows side-effects, we have to turn them into main
effects before using any theory. For example, $`x := (P\ \mathbf{value}\ e)` becomes
$`(P.\ x := e)`." Model: $`P\ \mathbf{value}\ e` is a value $`e\,s'` for a final state $`s'` of
$`P` from the initial state (chosen with Hilbert's $`\varepsilon`); the axiom holds
under the explicit hypothesis that $`e` is determined on the outcomes of $`P` —
which the book's axiom assumes silently and which holds for every
deterministic program. Under it $`e' = (P\ \mathbf{value}\ e) \Leftarrow P`, a total
deterministic program's value is $`e` of its new state, and the implementation
by a local copy of the state is proved with {uses "variable_declaration"}[].
The two examples are computed; "becomes" is a translation of a language with
side effects, not an equality — $`y := (x := x+1\ \mathbf{value}\ x)` and
$`x := x+1.\ y := x` are shown to be different specifications. Uses
{uses "substitution_law"}[] and {uses "specification_laws"}[].
:::

:::definition "function_and_procedure" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Function.iterSeq_implementable, LaPToP.ProgramTheory.Function.bexpBody, LaPToP.ProgramTheory.Function.bexp, LaPToP.ProgramTheory.Function.bexpBody_implementable, LaPToP.ProgramTheory.Function.bexp_eq, LaPToP.ProgramTheory.Procedure.AB, LaPToP.ProgramTheory.Procedure.P, LaPToP.ProgramTheory.Procedure.P_apply, LaPToP.ProgramTheory.Procedure.body, LaPToP.ProgramTheory.Procedure.P_refines, LaPToP.ProgramTheory.Procedure.paramAsLocal, LaPToP.ProgramTheory.Procedure.procedure_eq_newVarInit, LaPToP.ProgramTheory.Procedure.Var, LaPToP.ProgramTheory.Procedure.body₁, LaPToP.ProgramTheory.Procedure.body₂, LaPToP.ProgramTheory.Procedure.body₁_a, LaPToP.ProgramTheory.Procedure.body₂_a, LaPToP.ProgramTheory.Procedure.body₁_x_eq_body₂_x, LaPToP.ProgramTheory.Procedure.body₁_a_ne_body₂_a")
"In many popular programming languages, a function is a combination of
assertion about the result, name of the function, parameters, scope control,
and value expression. It's a “package deal”. ... In our notations,
$`\mathit{bexp} = \langle n : \mathit{int} \cdot \mathbf{new}\ r : \mathit{int} := 1 \cdot \mathbf{for}\ i := 0;..n\ \mathbf{do}\ r := r \times 2\ \mathbf{od}.\ \mathbf{assert}\ r : \mathit{int}\ \mathbf{value}\ r \rangle`.
We present these programming features separately so that they can be
understood separately." The function is assembled from the separate parts —
parameter, initialized local variable, the unrolled {uses "for_loop"}[] of
{uses "binary_exponentiation"}[], and {uses "value_expression"}[] — and
$`\mathit{bexp}\ n = 2^n` is proved (the assertion $`r : \mathit{int}` holds by typing
and is omitted). "The procedure (or void function, or method) ... combines name
declaration, parameterization, and local scope. ... we may want a procedure
$`P` with parameter $`x` defined as $`P = \langle x : \mathit{int} \cdot a' < x < b' \rangle` ... We
can use procedure $`P` before we refine its body: $`P\,(a+1) = a' < a+1 < b'`. The
body is easily refined as $`a' < x < b' \Leftarrow a := x-1.\ b := x+1`. ... A procedure
and argument can be translated to a local variable and initial value.
$`\langle p : D \cdot B \rangle\ a = (\mathbf{new}\ p : D := a \cdot B)` if $`B` doesn't use $`p'` or
$`p :=`. ... Another kind of parameter, called a variable parameter ... stands
for a nonlocal variable to be supplied as argument.
$`\langle \mathbf{new}\ x : \mathit{int} \cdot a := 3.\ b := 4.\ x := 5 \rangle\ a = a := 3.\ b := 4.\ a := 5 = a' = 5 \land b' = 4`
... $`\langle \mathbf{new}\ x : \mathit{int} \cdot x := 5.\ b := 4.\ a := 3 \rangle\ a = a := 5.\ b := 4.\ a := 3 = a' = 3 \land b' = 4`
but the result is different. Variable parameters prevent the use of
specification, and they prevent any reasoning about the procedure by itself."
All of these are proved: the application $`P\,(a+1)`, the refinement, the
translation law (the parameter read as a constant inside the scope of the
local variable), and, with a variable parameter modelled as a body that is a
function of the variable name, the two results $`a' = 5 \land b' = 4` and
$`a' = 3 \land b' = 4`, equal for a fresh argument $`x` but different for the argument
$`a`. Uses {uses "function_notation"}[], {uses "variable_declaration"}[] and
{uses "assertions"}[].
:::

:::theorem "functional_programming" (parent := "programming_language_core") (tags := "functional, refinement, hehner-5.8") (effort := "medium") (lean := "LaPToP.ProgramTheory.Functional.dom, LaPToP.ProgramTheory.Functional.sumFn, LaPToP.ProgramTheory.Functional.zero_mem_sumFn_dom, LaPToP.ProgramTheory.Functional.sum_eq, LaPToP.ProgramTheory.Functional.domain_split, LaPToP.ProgramTheory.Functional.orElse_lam_lam, LaPToP.ProgramTheory.Functional.sumFn_orElse, LaPToP.ProgramTheory.Functional.left_part, LaPToP.ProgramTheory.Functional.right_part, LaPToP.ProgramTheory.Functional.recursion, LaPToP.ProgramTheory.Functional.timeFn, LaPToP.ProgramTheory.Functional.len_eq, LaPToP.ProgramTheory.Functional.timeFn_orElse, LaPToP.ProgramTheory.Functional.time_left, LaPToP.ProgramTheory.Functional.time_right, LaPToP.ProgramTheory.Functional.time_recursion, LaPToP.ProgramTheory.Functional.time_recursive_measure, LaPToP.ProgramTheory.Functional.FSpec, LaPToP.ProgramTheory.Functional.Unsat, LaPToP.ProgramTheory.Functional.Sat, LaPToP.ProgramTheory.Functional.Det, LaPToP.ProgramTheory.Functional.Nondet, LaPToP.ProgramTheory.Functional.sat_iff, LaPToP.ProgramTheory.Functional.Implementable, LaPToP.ProgramTheory.Functional.implementable_iff_ne_null, LaPToP.ProgramTheory.Functional.Refines, LaPToP.ProgramTheory.Functional.occursIn, LaPToP.ProgramTheory.Functional.search₀, LaPToP.ProgramTheory.Functional.not_implementable_search₀, LaPToP.ProgramTheory.Functional.beyond, LaPToP.ProgramTheory.Functional.search, LaPToP.ProgramTheory.Functional.implementable_search, LaPToP.ProgramTheory.Functional.occursFrom, LaPToP.ProgramTheory.Functional.sfBody, LaPToP.ProgramTheory.Functional.searchFrom, LaPToP.ProgramTheory.Functional.search_apply_eq, LaPToP.ProgramTheory.Functional.search_step_refines, LaPToP.ProgramTheory.Functional.timeBound, LaPToP.ProgramTheory.Functional.onePlus, LaPToP.ProgramTheory.Functional.time_top, LaPToP.ProgramTheory.Functional.time_step")
"This section presents an alternative: a program is a function from its input
to its output. More generally, a specification is a function from possible
inputs to desired outputs, and programs (as always) are implemented
specifications. We take away $`ok`, assignment, and sequential composition from
our programming notations, and we add functions. To illustrate, we look once
again at the list summation problem (Exercise 174). This time, the
specification is $`\langle L : [*\mathit{rat}] \cdot \Sigma L \rangle`. ... We introduce
variable $`n` to indicate how much of the list has been summed; initially $`n` is
$`0`. $`\Sigma L = \langle n : 0,..\#L{+}1 \cdot \Sigma L\,[n;..\#L] \rangle\ 0` ... the
domain is really composed of two parts that must be treated differently.
$`0,..\#L{+}1 = \square L,\ \#L`. We divide the function into a selective union
$`\langle n : 0,..\#L{+}1 \cdot \Sigma L\,[n;..\#L] \rangle = \langle n : \square L \cdot \Sigma L\,[n;..\#L] \rangle \mid \langle n : \#L \cdot \Sigma L\,[n;..\#L] \rangle`
... $`\langle n : \square L \cdot \Sigma L\,[n;..\#L] \rangle = \langle n : \square L \cdot L\,n + \Sigma L\,[n{+}1;..\#L] \rangle`,
$`\langle n : \#L \cdot \Sigma L\,[n;..\#L] \rangle = \langle n : \#L \cdot 0 \rangle`. The one
remaining problem is solved by recursion.
$`\Sigma L\,[n{+}1;..\#L] = \langle n : 0,..\#L{+}1 \cdot \Sigma L\,[n;..\#L] \rangle\ (n{+}1)`.
In place of the selective union we could have used $`\mathbf{if}\ \mathbf{then}\ \mathbf{else}`;
they are related by the law
$`\langle v : A \cdot x \rangle \mid \langle v : B \cdot y \rangle = \langle v : A, B \cdot \mathbf{if}\ v : A\ \mathbf{then}\ x\ \mathbf{else}\ y \rangle`.
When we are interested in the execution time rather than the result, we replace
the result of each function with its time according to some measure." Both
measures are formalized: charging $`1` for each addition,
$`\#L = \langle n : 0,..\#L{+}1 \cdot \#L{-}n \rangle\ 0`,
$`\langle n : \square L \cdot \#L{-}n \rangle = \langle n : \square L \cdot 1 + \#L{-}n{-}1 \rangle`,
$`\#L{-}n{-}1 = \langle n : 0,..\#L{+}1 \cdot \#L{-}n \rangle\ (n{+}1)`; and the recursive
measure $`\#L{-}n = 1 + \langle n : 0,..\#L{+}1 \cdot \#L{-}n \rangle\ (n{+}1)`.

Section 5.8.0, Function Refinement: "In functional programming, a
nondeterministic specification is a bunch consisting of more than one element.
... Functional specification $`S` is unsatisfiable for domain element $`x`:
$`{\rm c\llap{/}} S\,x < 1`; satisfiable: $`{\rm c\llap{/}} S\,x \geq 1`; deterministic:
$`{\rm c\llap{/}} S\,x \leq 1`; nondeterministic: $`{\rm c\llap{/}} S\,x > 1`; ...
implementable: $`\forall x \cdot \exists y \cdot y : S\,x`. Implementability can be
restated as $`\forall x \cdot S\,x \neq \mathit{null}`. Consider the problem of
searching for an item in a list of integers. Our first attempt at specification
might be $`\langle L : [*\mathit{int}] \cdot \langle x : \mathit{int} \cdot \S n : \square L \cdot L\,n = x \rangle \rangle`
... if $`x` does not occur in $`L`, we are left without any possible result, so
this specification is unimplementable. ...
$`\langle L : [*\mathit{int}] \cdot \langle x : \mathit{int} \cdot \mathbf{if}\ x : L\,(\square L)\ \mathbf{then}\ \S n : \square L \cdot L\,n = x\ \mathbf{else}\ \#L,..\infty \rangle \rangle`
This specification is implementable, and often nondeterministic. ... Functional
specification $`P` (the problem) is refined by functional specification $`S`
(the solution) if and only if $`S : P`. ... “$`P` is refined by $`S`” is written
$`P{::}\,S`." Both linear-search refinements are proved as function inclusions
{uses "function_inclusion"}[]: the first,
$`\ldots {::}\ \langle i : \mathit{nat} \cdot \mathbf{if}\ x : L\,(i,..\#L)\ \mathbf{then}\ \S n : i,..\#L \cdot L\,n = x\ \mathbf{else}\ \#L,..\infty \rangle\ 0`,
as the equality of the two sides the book notes, and the second, the step
$`\mathbf{if}\ i = \#L\ \mathbf{then}\ \#L\ \mathbf{else}\ \mathbf{if}\ x = L\,i\ \mathbf{then}\ i\ \mathbf{else}\ \ldots (i{+}1)`.
The timing, recursive measure: $`0,..\#L{+}1\ {::}\ \langle i \cdot 0,..\#L{-}i{+}1 \rangle\ 0`
and $`0,..\#L{-}i{+}1\ {::}\ \mathbf{if}\ i = \#L\ \mathbf{then}\ 0\ \mathbf{else}\ \mathbf{if}\ x = L\,i\ \mathbf{then}\ 0\ \mathbf{else}\ 1 + \langle i \cdot 0,..\#L{-}i{+}1 \rangle\ (i{+}1)`.

Model notes. Lists are the integer lists of {uses "list_summation"}[] with
integer indices, so the book's rationals are integers, and the intervals are
the bunches $`x,..y` of {uses "bunch_primitives"}[]; $`\#L,..\infty` is the bunch of
integers $`\geq \#L`. The domain split and the selective-union law are proved
for `Fn.orElse` ({uses "selective_union"}[]) with `Fn.ext`; the solution
quantifier $`\S n : \square L \cdot L\,n = x` is the set of such $`n`
({uses "solution_quantifier"}[]). The unimplementability of the first search
specification is witnessed by the empty list, for which no $`x` has a result;
implementability of functional specifications is the analogue of
{uses "specification_implementability"}[]. In the second refinement and the
timing the book writes $`i : \mathit{nat}` and remarks that it "could have been more
precise about the domain of $`i`"; the step refinement is proved on $`\mathit{nat}` and
the timing step on the domain $`0,..\#L{+}1` that the bound $`0,..\#L{-}i{+}1` needs
(for $`i > \#L` the bunch is $`\mathit{null}`). The bunch sum $`1 + B` is the image of
$`B` under $`1 + {\cdot}`. The imperative counterpart is {uses "linear_search"}[].
:::
