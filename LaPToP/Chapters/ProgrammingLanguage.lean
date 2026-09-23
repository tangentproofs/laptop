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
import LaPToP.ProgramTheory.Alias
import LaPToP.ProgramTheory.Probabilistic
import LaPToP.ProgramTheory.ProbabilisticSums
import LaPToP.ProgramTheory.RandomNumbers
import LaPToP.ProgramTheory.Blackjack
import LaPToP.ProgramTheory.Information
import LaPToP.ProgramTheory.Functional
import LaPToP.ProgramTheory.Interpreter
import LaPToP.ProgramTheory.InterpreterSyntax

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
aliasing (Section 5.6) in `LaPToP.ProgramTheory.Alias`; probabilistic
programming (Section 5.7) in `LaPToP.ProgramTheory.Probabilistic` (its infinite
sums in `LaPToP.ProgramTheory.ProbabilisticSums`), random
number generators (Section 5.7.0) in `LaPToP.ProgramTheory.RandomNumbers` (with
the blackjack Exercise 344 in `LaPToP.ProgramTheory.Blackjack`) and
information (Section 5.7.1) in `LaPToP.ProgramTheory.Information`;
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
belong to Section 6.1.1 and are formalized in the `loop_definition` node of the
Recursion and Concurrency chapter (which builds on this one), where the two
accounts are also compared. Uses
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

:::definition "variable_declaration" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Spec.newVar, LaPToP.ProgramTheory.Spec.newVarInit, LaPToP.ProgramTheory.Spec.assignLocal, LaPToP.ProgramTheory.Spec.liftNonlocal, LaPToP.ProgramTheory.Spec.assignLocal_seq, LaPToP.ProgramTheory.Spec.implementable_newVar, LaPToP.ProgramTheory.Spec.not_implementable_newVar, LaPToP.ProgramTheory.Spec.newVar_liftNonlocal, LaPToP.ProgramTheory.Spec.newVarInit_eq, LaPToP.ProgramTheory.Spec.newVar_newVar, LaPToP.ProgramTheory.Spec.newVar_mono, LaPToP.ProgramTheory.Spec.newVar_refines_newVarInit, LaPToP.ProgramTheory.Spec.newVarInit_mono, LaPToP.ProgramTheory.Spec.assignNonlocal, LaPToP.ProgramTheory.Spec.assignNonlocal_seq, LaPToP.ProgramTheory.ScopeExamples.YZ, LaPToP.ProgramTheory.ScopeExamples.St, LaPToP.ProgramTheory.ScopeExamples.example₁, LaPToP.ProgramTheory.ScopeExamples.example₂, LaPToP.ProgramTheory.ScopeExamples.example₃")
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
$`\mathbf{new}\ x, y : T \cdot P = \exists x, x', y, y' : T \cdot P`, monotonicity of both forms,
that an initializing declaration refines the declaration it initializes
($`\mathbf{new}\ x : T \cdot P \Leftarrow \mathbf{new}\ x : T := e \cdot P`, since fixing an
arbitrary initial value is a refinement), and the book's
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

:::definition "time_dependence" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.TimeDependence.TD, LaPToP.ProgramTheory.TimeDependence.assignT, LaPToP.ProgramTheory.TimeDependence.assignDeadline, LaPToP.ProgramTheory.TimeDependence.tick, LaPToP.ProgramTheory.TimeDependence.assignT_seq, LaPToP.ProgramTheory.TimeDependence.RespectsClock, LaPToP.ProgramTheory.TimeDependence.respectsClock_assignDeadline, LaPToP.ProgramTheory.TimeDependence.respectsClock_tick, LaPToP.ProgramTheory.TimeDependence.respectsClock_cond, LaPToP.ProgramTheory.TimeDependence.respectsClock_seq, LaPToP.ProgramTheory.TimeDependence.not_respectsClock_assignT_const, LaPToP.ProgramTheory.TimeDependence.waitUntil, LaPToP.ProgramTheory.TimeDependence.respectsClock_waitUntil, LaPToP.ProgramTheory.TimeDependence.waitUntil_case_ge, LaPToP.ProgramTheory.TimeDependence.waitUntil_case_lt, LaPToP.ProgramTheory.TimeDependence.waitUntil_refines, LaPToP.ProgramTheory.TimeDependence.waitUntil_whileRefines, LaPToP.ProgramTheory.TimeDependence.RealTime.RS, LaPToP.ProgramTheory.TimeDependence.RealTime.assignT, LaPToP.ProgramTheory.TimeDependence.RealTime.assignT_seq, LaPToP.ProgramTheory.TimeDependence.RealTime.tick, LaPToP.ProgramTheory.TimeDependence.RealTime.waitUntil, LaPToP.ProgramTheory.TimeDependence.RealTime.waitUntil_le, LaPToP.ProgramTheory.TimeDependence.RealTime.waitUntil_of_max, LaPToP.ProgramTheory.TimeDependence.RealTime.waitUntil_refines, LaPToP.ProgramTheory.TimeDependence.RealTime.not_exact_refines, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.SD, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.assignS, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.assignX, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.grow, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.shrink, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.RespectsSpace, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.respectsSpace_assignX, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.respectsSpace_ok, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.respectsSpace_read_example, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.respectsSpace_grow_shrink, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.RespectsSpace.bounded, LaPToP.ProgramTheory.TimeDependence.SpaceDependence.not_respectsSpace_const")
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
{uses "while_loop"}[] $`\mathbf{while}\ t < w\ \mathbf{do}\ t := t+1\ \mathbf{od}`. "In programs
that depend on time, we should use the real time measure ... And we need a
slightly different definition of $`\mathbf{wait}\ \mathbf{until}\ w`, but we leave that as
Exercise 333(b)": "Now suppose that $`t` is a nonnegative extended real time
variable, and $`w` is a nonnegative extended real expression. Redefine
$`\mathbf{wait}\ \mathbf{until}\ w` appropriately, and refine it using the real time measure
(assume any positive operation time you need)." With the clock in $`\mathbb{R}_{\geq 0} \cup \{\infty\}`
and an operation time $`\delta` per iteration, the redefinition is: nothing
happens if $`t \geq w`, and otherwise the computation ends at the first test after
$`w`, $`w \leq t' \leq w + \delta` (`RealTime.waitUntil`); the exact $`t' = t \uparrow w` satisfies
it (`waitUntil_of_max`) but is not refined by a loop with positive operation
time (`not_exact_refines`, which overshoots), while the redefined specification
is: $`\mathbf{wait}\ \mathbf{until}\ w \Leftarrow \mathbf{if}\ t \geq w\ \mathbf{then}\ ok\ \mathbf{else}\ t := t + \delta.\ \mathbf{wait}\ \mathbf{until}\ w`
(`RealTime.waitUntil_refines`, for any $`\delta`; positivity only matters for
termination, which the recursive-call reading does not claim). "Our space
variable $`s`, like the time variable $`t`, has so far been used to prove things
about space usage, not to affect the computation. But if a program has space
usage information available to it, there is no harm in using that information.
Like $`t`, $`s` can be read but not written arbitrarily. All changes to $`s` must
correspond to changes in space usage." Space, unlike time, goes up and down, so
the discipline is a closure property rather than a monotonicity property:
`SpaceDependence.RespectsSpace` holds of specifications that leave $`s`
unchanged (reading it freely, `respectsSpace_assignX`,
`respectsSpace_read_example`), of the space-measure steps $`s := s + k` and
$`s := s - k` for a constant $`k` (`grow`, `shrink`), and is closed under
$`\mathbf{if}` and sequential composition. Its semantic content, the analogue of
$`t \leq t'`, is `RespectsSpace.bounded`: the change of $`s` is bounded
independently of the initial state — which an arbitrary $`s := 5` violates
(`not_respectsSpace_const`, the counterpart of `not_respectsClock_assignT_const`).
The space variable itself is modelled in the `space` node of the Program
Theory chapter (Section 4.3); recursion is not part of this closure. Uses
{uses "time_variable"}[] and {uses "recursive_time"}[].
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

:::definition "alias" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Alias.Memory, LaPToP.ProgramTheory.Alias.Memory.read, LaPToP.ProgramTheory.Alias.Memory.assign, LaPToP.ProgramTheory.Alias.Memory.retarget, LaPToP.ProgramTheory.Alias.Memory.Aliased, LaPToP.ProgramTheory.Alias.Memory.read_assign_self, LaPToP.ProgramTheory.Alias.Memory.read_assign_of_addr_ne, LaPToP.ProgramTheory.Alias.Memory.read_assign_alias, LaPToP.ProgramTheory.Alias.Memory.aliased_retarget, LaPToP.ProgramTheory.Alias.Memory.no_alias_iff_injective, LaPToP.ProgramTheory.Alias.Memory.read_assign_of_injective, LaPToP.ProgramTheory.Alias.assignSpec, LaPToP.ProgramTheory.Alias.readEq, LaPToP.ProgramTheory.Alias.twoNames, LaPToP.ProgramTheory.Alias.twoNames_aliased, LaPToP.ProgramTheory.Alias.assign_law_fails, LaPToP.ProgramTheory.Alias.substitution_law_fails, LaPToP.ProgramTheory.Alias.toMemory, LaPToP.ProgramTheory.Alias.toMemory_read, LaPToP.ProgramTheory.Alias.toMemory_assign, LaPToP.ProgramTheory.Alias.toMemory_not_aliased, LaPToP.ProgramTheory.Alias.alias_free_assign_law, LaPToP.ProgramTheory.Alias.alias_free_substitution_law")
"Many popular programming languages present us with a model of computation in
which there is a memory consisting of a large number of individual storage
cells. Each cell contains a value. Via the programming language, cells have
names. ... In the picture, $`p` is a pointer variable that currently points to
array element $`A\,1`, and $`{*}p` is $`p` dereferenced; so $`{*}p` and $`A\,1` refer to the
same memory cell. Since variable $`i` currently has value $`2`, $`A\,i` and $`A\,2` refer
to the same cell. And $`r` is a variable parameter for which variable $`i` has been
supplied as argument, so $`r` and $`i` refer to the same cell. We see that a cell
may have zero, one, two, or more names. When a cell has two or more names that
are visible at the same time, the names are said to be “aliases”. As we have
seen with arrays, with value expressions, and with variable parameters,
aliasing prevents us from applying our theory of programming; neither the
definition of assignment nor the substitution law work. Chapter 4 introduced
our computing model with the deterministic function $`\mathit{address}` that maps
different names to different addresses, saying where each state variable is.
But aliasing maps more than one name to an address, breaking the model. ... If
we redraw our picture slightly, we see that there are two mappings: one from
names to cells, and one from cells to values. An assignment such as
$`p := (\mathit{address\ of}\ A\,3)` or $`i := 4` can change both mappings at once. An
assignment to one name can change the value indirectly referred to by another
name. To simplify the picture and eliminate the possibility of aliasing, we
eliminate the cells and allow a richer space of values. ... Pointer variables
can be replaced by index variables dedicated to one structure so that they can
be implemented as addresses. Variable parameters are unnecessary if functions
can return structured values. The simpler picture is perfectly adequate, and
the problem of aliasing disappears."

The two-mapping picture is `Memory Name Cell Val` (`addr`, `store`), with
reading and assignment through a name, pointer assignment `retarget` (which
creates an alias: after $`p := (\mathit{address\ of}\ a)`, $`{*}p` and $`a` are aliases),
and `Aliased`. Proved: an assignment to one alias changes the value read
through the other, so on a concrete memory with two names and one cell both
the definition of assignment $`x := e = x' = e \land y' = y` of
{uses "assignment_spec"}[] and the {uses "substitution_law"}[] fail
(`assign_law_fails`, `substitution_law_fails`: $`x := 1.\ (y = 1)` is $`\top` there,
not $`y = 1`). "Different names to different addresses" is `addr` injective,
equivalent to the absence of aliases, and then the assignment law holds. The
alias-free picture — "eliminate the cells", every name its own cell — is
exactly the state of {uses "state_as_variables"}[] (`toMemory`), on which the
Chapter 4 laws hold (`alias_free_assign_law`, `alias_free_substitution_law`).
The "richer space of values" — a list variable with an index variable in place
of a pointer, $`A\,i := e` as $`A := i \to e \mid A` — is the array model of
{uses "data_structures"}[] and is not repeated.
:::

:::theorem "probabilistic_programming" (parent := "programming_language_core") (tags := "probability, distribution, hehner-5.7") (effort := "medium") (lean := "LaPToP.ProgramTheory.Probabilistic.Prob, LaPToP.ProgramTheory.Probabilistic.ind, LaPToP.ProgramTheory.Probabilistic.ind_true, LaPToP.ProgramTheory.Probabilistic.ind_false, LaPToP.ProgramTheory.Probabilistic.prob_ind, LaPToP.ProgramTheory.Probabilistic.ind_not, LaPToP.ProgramTheory.Probabilistic.ind_and, LaPToP.ProgramTheory.Probabilistic.ind_or, LaPToP.ProgramTheory.Probabilistic.PSpec, LaPToP.ProgramTheory.Probabilistic.ofSpec, LaPToP.ProgramTheory.Probabilistic.IsDistribution, LaPToP.ProgramTheory.Probabilistic.pcond, LaPToP.ProgramTheory.Probabilistic.pseq, LaPToP.ProgramTheory.Probabilistic.avg, LaPToP.ProgramTheory.Probabilistic.pseq_const_eq_avg, LaPToP.ProgramTheory.Probabilistic.isDistribution_ofSpec_ok, LaPToP.ProgramTheory.Probabilistic.isDistribution_ofSpec_det, LaPToP.ProgramTheory.Probabilistic.tsum_succ_eq_one, LaPToP.ProgramTheory.Probabilistic.not_summable_succ, LaPToP.ProgramTheory.Probabilistic.geometric_distribution, LaPToP.ProgramTheory.Probabilistic.isDistribution_pcond, LaPToP.ProgramTheory.Probabilistic.pseq_eq_sum, LaPToP.ProgramTheory.Probabilistic.isDistribution_pseq, LaPToP.ProgramTheory.Probabilistic.pok, LaPToP.ProgramTheory.Probabilistic.passign, LaPToP.ProgramTheory.Probabilistic.assignX, LaPToP.ProgramTheory.Probabilistic.ofSpec_ok, LaPToP.ProgramTheory.Probabilistic.ofSpec_assign, LaPToP.ProgramTheory.Probabilistic.ofSpec_cond, LaPToP.ProgramTheory.Probabilistic.passign_pseq, LaPToP.ProgramTheory.Probabilistic.ofSpec_assign_seq, LaPToP.ProgramTheory.Probabilistic.isDistribution_passign, LaPToP.ProgramTheory.Probabilistic.support_passign, LaPToP.ProgramTheory.Probabilistic.ex₁, LaPToP.ProgramTheory.Probabilistic.ex₁_eq, LaPToP.ProgramTheory.Probabilistic.ex₁_zero, LaPToP.ProgramTheory.Probabilistic.ex₁_one, LaPToP.ProgramTheory.Probabilistic.ex₁_two, LaPToP.ProgramTheory.Probabilistic.isDistribution_ex₁, LaPToP.ProgramTheory.Probabilistic.support_ex₁, LaPToP.ProgramTheory.Probabilistic.ex₂body, LaPToP.ProgramTheory.Probabilistic.ex₂, LaPToP.ProgramTheory.Probabilistic.ex₂_eq, LaPToP.ProgramTheory.Probabilistic.isDistribution_ex₂, LaPToP.ProgramTheory.Probabilistic.support_ex₂, LaPToP.ProgramTheory.Probabilistic.avg_ex₂_eq, LaPToP.ProgramTheory.Probabilistic.avg_ex₂_x, LaPToP.ProgramTheory.Probabilistic.prob_ex₂_gt_three, LaPToP.ProgramTheory.Probabilistic.isDistribution_pseq', LaPToP.ProgramTheory.Probabilistic.geomDist, LaPToP.ProgramTheory.Probabilistic.geomDist_succ, LaPToP.ProgramTheory.Probabilistic.isDistribution_geomDist, LaPToP.ProgramTheory.Probabilistic.hasSum_sq_geometric, LaPToP.ProgramTheory.Probabilistic.avg_geomDist_sq")
"Probability Theory has been developed using the arbitrary convention that a
probability is a real number between $`0` and $`1` inclusive
$`\mathit{prob} = \S r : \mathit{real} \cdot 0 \leq r \leq 1` ... Accordingly, for this section only,
we add the axioms $`\top = 1`, $`\bot = 0`. With these axioms, binary operators can be
expressed arithmetically: $`\lnot x = 1 - x`, $`x \land y = x \times y`, and
$`x \lor y = x - x \times y + y`. A distribution is an expression whose value (for all
assignments of values to its variables) is a probability, and whose sum (over
all assignments of values to its variables) is $`1`. ... if $`n : \mathit{nat}{+}1`, then
$`2^{-n}` is a distribution because
$`(\forall n : \mathit{nat}{+}1 \cdot 2^{-n} : \mathit{prob}) \land (\Sigma n : \mathit{nat}{+}1 \cdot 2^{-n}) = 1`
... The specification $`n' = n{+}1` is not a distribution of $`n` and $`n'` because
there are infinitely many pairs of values that give $`n' = n{+}1` the value $`\top` or
$`1`, and so $`\Sigma n, n' \cdot n' = n{+}1 = \infty`. But for any fixed value of $`n`,
there is a single value of $`n'` that gives $`n' = n{+}1` the value $`\top` or $`1`, and so
$`\Sigma n' \cdot n' = n{+}1 = 1`. For any fixed value of $`n`, $`n' = n{+}1` is a one-point
distribution of $`n'`. Similarly, any implementable deterministic specification
is a one-point distribution of the final state. We generalize our programming
notations to allow probabilistic operands as follows.
$`ok = (x' = x) \times (y' = y) \times \ldots`, $`x := e = (x' = e) \times (y' = y) \times \ldots`,
$`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ Q = b \times P + (1 - b) \times Q`,
$`P.\ Q = \Sigma x'', y'', \ldots \cdot (\text{for } x', y', \ldots \text{ substitute } x'', y'', \ldots \text{ in } P) \times (\text{for } x, y, \ldots \text{ substitute } x'', y'', \ldots \text{ in } Q)`.
Since $`\bot = 0` and $`\top = 1`, the definitions of $`ok` and assignment have not
changed; they have just been expressed arithmetically. If $`b`, $`P`, and $`Q` are
binary, the definitions of $`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ Q` and $`P.Q` have not
changed. ... If $`b` is a probability of the initial state, and $`P` and $`Q` are
distributions of the final state, then $`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ Q` is a
distribution of the final state. If $`P` and $`Q` are distributions of the final
state, then $`P.Q` is a distribution of the final state. For example,
$`\mathbf{if}\ 1/3\ \mathbf{then}\ x := 0\ \mathbf{else}\ x := 1` means that with probability $`1/3` we
assign $`x` the value $`0`, and with the remaining probability $`2/3` we assign $`x` the
value $`1`. In one variable $`x`,
$`\mathbf{if}\ 1/3\ \mathbf{then}\ x := 0\ \mathbf{else}\ x := 1 = 1/3 \times (x' = 0) + (1 - 1/3) \times (x' = 1)`"
— evaluated at $`x' = 0, 1, 2` this is $`1/3`, $`2/3`, $`0`. "Here is a slightly more
elaborate example in one variable $`x`.
$`\mathbf{if}\ 1/3\ \mathbf{then}\ x := 0\ \mathbf{else}\ x := 1.\ \mathbf{if}\ x = 0\ \mathbf{then}\ \mathbf{if}\ 1/2\ \mathbf{then}\ x := x{+}2\ \mathbf{else}\ x := x{+}3\ \mathbf{else}\ \mathbf{if}\ 1/4\ \mathbf{then}\ x := x{+}4\ \mathbf{else}\ x := x{+}5`
$`= (x' = 2)/6 + (x' = 3)/6 + (x' = 5)/6 + (x' = 6)/2` ... Let $`P` be any distribution
of final states, and let $`e` be any number expression over initial states.
After execution of $`P`, the average value of $`e` is $`(P.\ e)`. ... After execution of
the previous example, the average value of $`x` is ...
$`= 1/6 \times 2 + 1/6 \times 3 + 1/6 \times 5 + 1/2 \times 6 = 4 + 2/3`. Let $`P` be any distribution
of final states, and let $`b` be any binary expression over initial states. After
execution of $`P`, the probability that $`b` is true is $`(P.\ b)`. Probability is just
the average value of a binary expression. For example, after execution of the
previous example, the probability that $`x` is greater than $`3` is ... $`= 2/3`. Most
of the laws, including all distribution laws and the Substitution Law, apply
without change to probabilistic specifications and programs."

Model notes. A probabilistic specification is `PSpec σ := σ → σ → ℝ`; the
axioms $`\top = 1`, $`\bot = 0` are the indicator `ind`, which embeds the binary
specifications of {uses "specification_notations"}[] (`ofSpec`), and the three
arithmetic laws for $`\lnot`, $`\land`, $`\lor` are proved for it. Sums over the
state space are `tsum` ($`\Sigma'`), the numeric quantifier of
{uses "quantifier_numeric"}[] over an infinite domain. "Distribution of the final
state" is `IsDistribution`: for each initial state the values are probabilities
with sum $`1`. Proved: `ok` and every deterministic specification are one-point
distributions; $`\Sigma n' \cdot n' = n{+}1 = 1`, and "$`\Sigma n, n' \cdot n' = n{+}1 = \infty`" as
non-summability over the pairs; the geometric distribution $`2^{-n}` on
$`\mathit{nat}{+}1`; `pcond` preserves distributions when $`b` is a probability; `pseq`
preserves distributions — first for $`P` with finitely many possible final states
(`isDistribution_pseq`, the case of all the examples), then in general
(`isDistribution_pseq'`, by interchanging the nonnegative double sum
$`\Sigma x'', x' \cdot P \times Q`); "the definitions have not changed" for `ok`,
assignment and `if` (`ofSpec_cond`), and for $`P.Q` with an assignment as $`P`, via
the probabilistic Substitution Law `passign_pseq` ({uses "substitution_law"}[],
{uses "specification_laws"}[]). The state is the book's "one variable $`x`", an
integer. Both worked examples are computed: the three values of the first, the
closed form of the second (a finite sum over the final values $`0, 1` of the
first), its distribution property, the average $`4 + 2/3` and the probability
$`2/3`, where the average $`(P.\ e)` is `avg` with `pseq_const_eq_avg` relating it to
$`P.\ e`. The average of $`n^2` under $`2^{-n}` is $`6` (`avg_geomDist_sq`, from Mathlib's
$`\Sigma n \cdot \binom{n+k}{k} r^n = 1/(1-r)^{k+1}` for $`k = 1, 2` and
$`(n{+}1)^2 = 2\binom{n+2}{2} - (n{+}1)`), with $`2^{-n}` on $`\mathit{nat}{+}1` as the
distribution `geomDist`.
:::

:::theorem "random_number_generators" (parent := "programming_language_core") (tags := "probability, random, time, hehner-5.7.0") (effort := "medium") (lean := "LaPToP.ProgramTheory.Probabilistic.pdet, LaPToP.ProgramTheory.Probabilistic.pdet_pseq, LaPToP.ProgramTheory.Probabilistic.pdet_id_eq_ofSpec_ok, LaPToP.ProgramTheory.Probabilistic.urand, LaPToP.ProgramTheory.Probabilistic.randAssign, LaPToP.ProgramTheory.Probabilistic.hasSum_urand, LaPToP.ProgramTheory.Probabilistic.prob_urand, LaPToP.ProgramTheory.Probabilistic.randAssign_id, LaPToP.ProgramTheory.Probabilistic.sumDist, LaPToP.ProgramTheory.Probabilistic.freshForm, LaPToP.ProgramTheory.Probabilistic.freshForm_eq, LaPToP.ProgramTheory.Probabilistic.twoRand, LaPToP.ProgramTheory.Probabilistic.support_randAssign_two, LaPToP.ProgramTheory.Probabilistic.twoRand_eq, LaPToP.ProgramTheory.Probabilistic.pcond_rand_two, LaPToP.ProgramTheory.Probabilistic.randLt, LaPToP.ProgramTheory.Probabilistic.randLt_eq, LaPToP.ProgramTheory.Probabilistic.randLt_eq', LaPToP.ProgramTheory.Probabilistic.prob_dice_eq, LaPToP.ProgramTheory.Probabilistic.prob_dice_ne, LaPToP.ProgramTheory.Probabilistic.diceBody, LaPToP.ProgramTheory.Probabilistic.tdist, LaPToP.ProgramTheory.Probabilistic.diceBody_tdist, LaPToP.ProgramTheory.Probabilistic.tdist_add, LaPToP.ProgramTheory.Probabilistic.isDistribution_tdist, LaPToP.ProgramTheory.Probabilistic.avg_tdist")
"Many programming languages provide a random number generator (sometimes
called a “pseudo-random number generator”). The usual notation is functional,
and the usual result is a value whose distribution is uniform (constant) over a
nonempty finite range. If $`n : \mathit{nat}{+}1`, we use the notation $`\mathit{rand}\ n` for a
generator that produces natural numbers uniformly distributed over the range
$`0,..n`. So $`\mathit{rand}\ n` has value $`r` with probability $`(r : 0,..n) / n`.
Functional notation for a random number generator is inconsistent. Since $`x = x`
is a law, we should be able to simplify $`\mathit{rand}\ n = \mathit{rand}\ n` to $`\top`, but we
cannot because the two occurrences of $`\mathit{rand}\ n` might generate different
numbers. ... To restore consistency, we replace each use of $`\mathit{rand}` with a
fresh variable before we do anything else. We can replace $`\mathit{rand}\ n` with
integer variable $`r` whose value has probability $`(r : 0,..n) / n`. ... For
example, in one state variable $`x`,
$`x := \mathit{rand}\ 2.\ x := x + \mathit{rand}\ 3 = \Sigma r : 0,..2 \cdot \Sigma s : 0,..3 \cdot (x := r)/2.\ (x := x + s)/3`
$`= (\Sigma r : 0,..2 \cdot \Sigma s : 0,..3 \cdot (x' = r{+}s)) / 6 = (x' = 0)/6 + (x' = 1)/3 + (x' = 2)/3 + (x' = 3)/6`
which says that $`x'` is $`0` with probability $`1/6`, $`1` with probability $`1/3`, $`2`
with probability $`1/3`, $`3` with probability $`1/6`, and any other value with
probability $`0`. Whenever $`\mathit{rand}` occurs in the context of a simple equation,
such as $`r = \mathit{rand}\ n`, we don't need to introduce a variable for it, since one is
supplied. We just replace the deceptive equation with $`(r : 0,..n) / n`. For
example, $`x := \mathit{rand}\ 2.\ x := x + \mathit{rand}\ 3 = (x' : 0,..2)/2.\ (x' : x + (0,..3))/3`
$`= \Sigma x'' \cdot (x'' : 0,..2)/2 \times (x' : x'' + (0,..3))/3 = \ldots = (x' = 0)/6 + (x' = 1)/3 + (x' = 2)/3 + (x' = 3)/6`
as before. And $`\mathbf{if}\ \mathit{rand}\ 2\ \mathbf{then}\ A\ \mathbf{else}\ B` can be replaced by
$`\mathbf{if}\ 1/2\ \mathbf{then}\ A\ \mathbf{else}\ B`. ... $`\mathit{rand}\ 8 < 3` has binary value $`b` with
distribution $`\Sigma r : 0,..8 \cdot (b = (r < 3)) / 8 = (b = \top) \times 3/8 + (b = \bot) \times 5/8 = 5/8 - b/4`
which says that $`b` is $`\top` with probability $`3/8`, and $`\bot` with probability
$`5/8`. ... Exercise 351 asks: If you repeatedly throw a pair of six-sided dice,
how long does it take until the dice are equal? Using $`u` and $`v` for the dice
and $`t` for recursive time, the program is
$`u' = v' \Leftarrow u := (\mathit{rand}\ 6) + 1.\ v := (\mathit{rand}\ 6) + 1.\ \mathbf{if}\ u = v\ \mathbf{then}\ ok\ \mathbf{else}\ t := t{+}1.\ u' = v'`.
Each iteration, with probability $`5/6` we keep going, and with probability $`1/6`
we stop. So we offer the hypothesis that (for finite $`t`) the execution time has
the distribution $`(t' \geq t) \times (5/6)^{t'-t} \times 1/6`. To prove it, let's start with
the implementation. ... $`= 6 \times (t' = t)/36 + 30 \times (t' \geq t{+}1) \times (5/6)^{t'-t-1} / 6 / 36`
$`= (t' = t)/6 + (t' \geq t{+}1) \times (5/6)^{t'-t} / 6 = (t' \geq t) \times (5/6)^{t'-t} \times 1/6`
which is the distribution we hypothesized, and that completes the proof. The
average value of $`t'` is $`(t' \geq t) \times (5/6)^{t'-t} \times 1/6.\ t = t + 5`, so on
average it takes $`5` additional throws of the dice (after the first) to get an
equal pair."

Model notes, on top of {uses "probabilistic_programming"}[]. $`\mathit{rand}\ n` by
itself is the uniform distribution `urand` on $`0,..n` ({uses "bunch_interval"}[]),
a distribution for $`n \geq 1`; $`x := e\,(\mathit{rand}\ n)` is the book's replacement by a
fresh variable summed over $`0,..n` (`randAssign`), and `randAssign_id` is the
"deceptive equation" reading $`(x' : 0,..n)/n`. Both computations of
$`x := \mathit{rand}\ 2.\ x := x + \mathit{rand}\ 3` are proved to give the stated distribution: the
fresh-variable double sum (`freshForm_eq`) and the sequential composition of
the two replaced assignments (`twoRand_eq`, a finite sum over the final
values $`0, 1` of the first); the $`\mathbf{if}\ \mathit{rand}\ 2` replacement and the
$`\mathit{rand}\ 8 < 3` distribution in both forms are proved with $`b` a proposition. For
the dice, the book's calculation sums out the dice $`u'', v''` and then reads the
result as a distribution of $`t'` alone, dropping the final values of $`u`, $`v`; this
is formalized in two layers. The dice layer: a throw of two dice has $`36`
equiprobable outcomes in $`1,..7 \times 1,..7`, and the probabilities of $`u = v` and
$`u \neq v` are $`1/6` and $`5/6`. The time layer, on the finite recursive-time variable
$`t : \mathit{nat}` ({uses "recursive_time"}[]; the book says "for finite $`t`"): the loop
body with the dice summed out is $`\mathbf{if}\ 1/6\ \mathbf{then}\ ok\ \mathbf{else}\ t := t{+}1.\ H`
(`diceBody`, using the Substitution Law `pdet_pseq`, {uses "substitution_law"}[]),
and the hypothesis `tdist` is proved to be its fixed point (`diceBody_tdist`,
the book's last three lines), a distribution of $`t'` (a shifted geometric
series), with average $`t + 5` (`avg_tdist`, from $`\Sigma n \cdot n\,(5/6)^n = 30`). The
blackjack Exercise 344 (pp. 88–89) is the next node.
:::

:::theorem "blackjack" (parent := "programming_language_core") (tags := "probability, random, exercise-344, hehner-5.7.0") (effort := "medium") (lean := "LaPToP.ProgramTheory.Probabilistic.card, LaPToP.ProgramTheory.Probabilistic.card_card, LaPToP.ProgramTheory.Probabilistic.hasSum_uniform, LaPToP.ProgramTheory.Probabilistic.prob_uniform, LaPToP.ProgramTheory.Probabilistic.deal, LaPToP.ProgramTheory.Probabilistic.secondCard, LaPToP.ProgramTheory.Probabilistic.sum_ind_eq_interval, LaPToP.ProgramTheory.Probabilistic.randAssign_deal, LaPToP.ProgramTheory.Probabilistic.randAssign_secondCard, LaPToP.ProgramTheory.Probabilistic.isDistribution_deal, LaPToP.ProgramTheory.Probabilistic.isDistribution_secondCard, LaPToP.ProgramTheory.Probabilistic.support_deal, LaPToP.ProgramTheory.Probabilistic.under7Body, LaPToP.ProgramTheory.Probabilistic.game7, LaPToP.ProgramTheory.Probabilistic.isDistribution_game7, LaPToP.ProgramTheory.Probabilistic.dist7, LaPToP.ProgramTheory.Probabilistic.game7_eq_sum, LaPToP.ProgramTheory.Probabilistic.game7_eq, LaPToP.ProgramTheory.Probabilistic.xHand, LaPToP.ProgramTheory.Probabilistic.yHand, LaPToP.ProgramTheory.Probabilistic.xWins, LaPToP.ProgramTheory.Probabilistic.yWins, LaPToP.ProgramTheory.Probabilistic.xWins_iff, LaPToP.ProgramTheory.Probabilistic.yWins_iff, LaPToP.ProgramTheory.Probabilistic.tie, LaPToP.ProgramTheory.Probabilistic.tie_iff, LaPToP.ProgramTheory.Probabilistic.sum_ind, LaPToP.ProgramTheory.Probabilistic.probXWins, LaPToP.ProgramTheory.Probabilistic.probYWins, LaPToP.ProgramTheory.Probabilistic.probTie, LaPToP.ProgramTheory.Probabilistic.probXWins_eq, LaPToP.ProgramTheory.Probabilistic.probYWins_eq, LaPToP.ProgramTheory.Probabilistic.probTie_eq, LaPToP.ProgramTheory.Probabilistic.probs_sum, LaPToP.ProgramTheory.Probabilistic.under_succ_beats, LaPToP.ProgramTheory.Probabilistic.under_beats_succ, LaPToP.ProgramTheory.Probabilistic.under_eight_best, LaPToP.ProgramTheory.Probabilistic.BJ, LaPToP.ProgramTheory.Probabilistic.randDeal, LaPToP.ProgramTheory.Probabilistic.pseq_randDeal, LaPToP.ProgramTheory.Probabilistic.dealC, LaPToP.ProgramTheory.Probabilistic.dealD, LaPToP.ProgramTheory.Probabilistic.setX, LaPToP.ProgramTheory.Probabilistic.setY, LaPToP.ProgramTheory.Probabilistic.game, LaPToP.ProgramTheory.Probabilistic.final, LaPToP.ProgramTheory.Probabilistic.game_eq, LaPToP.ProgramTheory.Probabilistic.xWinsState, LaPToP.ProgramTheory.Probabilistic.avg_game, LaPToP.ProgramTheory.Probabilistic.prob_xWins_game")
"Exercise 344 is a simplified version of blackjack. You are dealt a card from a
deck; its value is in the range $`1` through $`13` inclusive. You may stop with just
one card, or have a second card if you want. Your object is to get a total as
near as possible to $`14`, but not over $`14`. Your strategy is to take a second
card if the first is under $`7`. Assuming each card value has equal probability
(actually, the second card drawn has a diminished probability of having the
same value as the first card drawn, but let's ignore that complication), we
represent a card as $`(\mathit{rand}\ 13) + 1`. In one variable $`x`, the game is
$`x := (\mathit{rand}\ 13) + 1.\ \mathbf{if}\ x < 7\ \mathbf{then}\ x := x + (\mathit{rand}\ 13) + 1\ \mathbf{else}\ ok`
$`= (x' : (0,..13){+}1)/13.\ \mathbf{if}\ x < 7\ \mathbf{then}\ (x' : x + (0,..13){+}1)/13\ \mathbf{else}\ x' = x`
$`= \Sigma x'' \cdot (x'' : 1,..14)/13 \times ((x'' < 7) \times (x' : x''{+}1,..x''{+}14)/13 + (x'' \geq 7) \times (x' = x''))`
by several omitted steps
$`= ((2 \leq x' < 7) \times (x' - 1) + (7 \leq x' < 14) \times 19 + (14 \leq x' < 20) \times (20 - x')) / 169`.
That is the distribution of $`x'` if we use the “under 7” strategy. We can
similarly find the distribution of $`x'` if we use the “under 8” strategy, or any
other strategy. But which strategy is best? To compare two strategies, we play
both of them at once. Player $`x` will play “under $`n`” and player $`y` will play
“under $`n{+}1`” using exactly the same cards $`c` and $`d` (the result would be no
different if they used different cards, but it would require more variables).
Here is the new game, followed by the assertion that $`x` wins:
$`c := (\mathit{rand}\ 13) + 1.\ d := (\mathit{rand}\ 13) + 1.\ \mathbf{if}\ c < n\ \mathbf{then}\ x := c{+}d\ \mathbf{else}\ x := c.\ \mathbf{if}\ c < n{+}1\ \mathbf{then}\ y := c{+}d\ \mathbf{else}\ y := c.\ y' < x' \leq 14 \lor x' \leq 14 < y'`
Replace $`\mathit{rand}` and use the Functional-Imperative Law twice. ... Use the
Substitution Law twice. ...
$`= (c' : (0,..13){+}1 \land d' : (0,..13){+}1 \land x' = x \land y' = y) / 169.\ c = n \land d > 14 - n`
$`= \Sigma d : 1,..14 \cdot (d > 14 - n)/169 = (n - 1) / 169`. The probability that $`x` wins
is $`(n - 1) / 169`. By similar calculations we can find that the probability
that $`y` wins is $`(14 - n) / 169`, and the probability of a tie is $`12/13`. For
$`n < 8`, “under $`n{+}1`” beats “under $`n`”. For $`n \geq 8`, “under $`n`” beats “under
$`n{+}1`”. So “under 8” beats both “under 7” and “under 9”."

Model notes, on top of {uses "random_number_generators"}[] and
{uses "probabilistic_programming"}[]. A dealt card $`x := (\mathit{rand}\ 13) + 1` is the
uniform distribution `deal` on $`1,..14`, proved equal to the fresh-variable
replacement `randAssign 13`, and likewise the second card; both are
distributions. The “under 7” game `game7` is the probabilistic program
$`\mathit{deal}.\ \mathbf{if}\ x < 7\ \mathbf{then}\ \mathit{secondCard}\ \mathbf{else}\ ok`; it is a distribution, its
sum form is the book's $`\Sigma x''` line (`game7_eq_sum`), and the "several
omitted steps" are carried out (`game7_eq`): a finite sum over the $`13` first
cards, evaluated for each $`x'` in $`2,..20` and shown to vanish elsewhere,
giving exactly the book's closed form `dist7`. For the two-player game the
book's reduction of the winning assertion is proved for cards $`c, d : 1,..14`
and $`1 \leq n \leq 13` — `xWins_iff` ($`c = n \land d > 14 - n`), `yWins_iff`
($`c = n \land d \leq 14 - n`) and `tie_iff` ($`c \neq n`) — and the probabilities are the
counts over the $`169` equiprobable card pairs (the book's own last line
$`\Sigma d : 1,..14 \cdot (d > 14 - n)/169`): `probXWins_eq` $`= (n-1)/169`, `probYWins_eq`
$`= (14-n)/169`, `probTie_eq` $`= 12/13`, summing to $`1`; then `under_succ_beats`
($`n < 8`), `under_beats_succ` ($`n \geq 8`) and `under_eight_best` (“under 8” beats
“under 7” as player $`y` with $`n = 7`, and “under 9” as player $`x` with $`n = 8`). The
four-variable probabilistic program of the two-player game is also built
(`game`, on the state $`c, d, x, y`): the two deals are fresh-variable sums
(`randDeal`, the book's replacement of $`\mathit{rand}`), the two conditional
assignments are folded by the Functional-Imperative Law into deterministic
steps (`setX`, `setY`), and the probabilistic Substitution Law for a random
assignment (`pseq_randDeal`, the analogue of {uses "substitution_law"}[])
evaluates the program to the sum over the $`169` card pairs (`game_eq`,
`avg_game`); `prob_xWins_game` is then the book's $`(P.\ b)` reading of "the
probability that $`x` wins", $`(n-1)/169`, for the program itself. The
equal-probability idealization is the book's.
:::

:::theorem "information" (parent := "programming_language_core") (tags := "probability, information, entropy, hehner-5.7.1") (effort := "small") (lean := "LaPToP.ProgramTheory.Probabilistic.info, LaPToP.ProgramTheory.Probabilistic.entro, LaPToP.ProgramTheory.Probabilistic.prob_even_rand_eight, LaPToP.ProgramTheory.Probabilistic.prob_rand_eight_eq_five, LaPToP.ProgramTheory.Probabilistic.prob_rand_eight_lt_eight, LaPToP.ProgramTheory.Probabilistic.info_half, LaPToP.ProgramTheory.Probabilistic.info_eighth, LaPToP.ProgramTheory.Probabilistic.info_one, LaPToP.ProgramTheory.Probabilistic.info_seven_eighths, LaPToP.ProgramTheory.Probabilistic.info_seven_eighths_bounds, LaPToP.ProgramTheory.Probabilistic.entro_eq_binEntropy_div, LaPToP.ProgramTheory.Probabilistic.entro_half, LaPToP.ProgramTheory.Probabilistic.entro_symm, LaPToP.ProgramTheory.Probabilistic.entro_eighth_eq, LaPToP.ProgramTheory.Probabilistic.entro_eighth_bounds, LaPToP.ProgramTheory.Probabilistic.entro_le_one, LaPToP.ProgramTheory.Probabilistic.entro_eq_one_iff")
"There is a close connection between information and probability. If a binary
expression has probability $`p` of being true, and you evaluate it, and it turns
out to be true, then the amount of information in bits that you have just
learned is $`\mathit{info}\ p`, defined as $`\mathit{info}\ p = -\log p` where $`\log` is the binary
(base $`2`) logarithm. For example, $`\mathit{even}\ (\mathit{rand}\ 8)` has probability $`1/2` of
being true. If we evaluate it and find that it is true, we have just learned
$`\mathit{info}\ (1/2) = -\log (1/2) = \log 2 = 1` bit of information; we have learned that
the rightmost bit of the random number we were given is $`0`. ... If we test
$`\mathit{rand}\ 8 = 5`, which has probability $`1/8` of being true, and we find that it is
true, we learn $`\mathit{info}\ (1/8) = -\log (1/8) = \log 8 = 3` bits, which is the entire
random number in binary. If we find that $`\mathit{rand}\ 8 = 5` is false, we learn
$`\mathit{info}\ (7/8) = -\log (7/8) = \log 8 - \log 7 = 3 - 2.80736 = 0.19264` approximately
bits; we learn that the random number isn't $`5`, but it could be any of $`7`
others. Suppose we test $`\mathit{rand}\ 8 < 8`. Since it is certain to be true, there is
really no point in making this test; we learn $`\mathit{info}\ 1 = -\log 1 = -0 = 0`. In
$`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ Q`, suppose $`b` has probability $`p` of being true.
When it is true, we learn $`\mathit{info}\ p` bits, and this happens with probability $`p`.
When it is false, we learn $`\mathit{info}\ (1-p)` bits, and this happens with probability
$`(1-p)`. The average amount of information gained, called the entropy, is
$`\mathit{entro}\ p = p \times \mathit{info}\ p + (1-p) \times \mathit{info}\ (1-p)`. For examples,
$`\mathit{entro}\ (1/2) = 1`, and $`\mathit{entro}\ (1/8) = \mathit{entro}\ (7/8) = 0.54356` approximately.
Since $`\mathit{entro}\ p` is at its maximum when $`p = 1/2`, we learn most on average, and
make the most efficient use of the test, if its probability is near $`1/2`. For
example, in the binary search problem of Subsection 4.2.5, we could have divided
the remaining search interval anywhere, but for the best average execution
time, we split it into two parts having equal probabilities of finding the item
we seek. And in the fast exponentiation problem of Subsection 4.1.2, it is
better on average to test $`\mathit{even}\ y` rather than $`y = 0` if we have a choice."

Model notes. `info` is $`-\log_2` (`Real.logb 2`) and `entro` is its average as
defined; `entro_eq_binEntropy_div` identifies it with Mathlib's binary entropy
in nats divided by $`\log 2`. The three test probabilities are computed from the
uniform distribution of {uses "random_number_generators"}[] on
{uses "probabilistic_programming"}[]; $`\mathit{info}\ (1/2) = 1`, $`\mathit{info}\ (1/8) = 3`,
$`\mathit{info}\ 1 = 0` and $`\mathit{info}\ (7/8) = \log 8 - \log 7` are exact, and the
approximate values are proved as bounds $`0.19 < \mathit{info}\ (7/8) < 0.2` (from
$`2^{19} < (8/7)^{100}` and $`(8/7)^5 < 2`) and $`0.54 < \mathit{entro}\ (1/8) < 0.55`;
$`\mathit{entro}\ (1/2) = 1`, $`\mathit{entro}\ p = \mathit{entro}\ (1-p)`, and the maximum:
$`\mathit{entro}\ p \leq 1` for every $`p`, with equality exactly at $`p = 1/2`
(`Real.binEntropy_le_log_two`, `Real.binEntropy_eq_log_two`). The remarks on
{uses "binary_search"}[] and {uses "fast_exponentiation"}[] are not
formalized.
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

:::definition "interpreter" (parent := "programming_language_core") (lean := "LaPToP.ProgramTheory.Spec.whileRel, LaPToP.ProgramTheory.Spec.whileRel_unfold, LaPToP.ProgramTheory.Spec.whileRefines_whileRel, LaPToP.ProgramTheory.Spec.refines_whileRel, LaPToP.ProgramTheory.Spec.whileRel_of_not, LaPToP.ProgramTheory.Interpreter.Prog, LaPToP.ProgramTheory.Interpreter.LoopFree, LaPToP.ProgramTheory.Interpreter.run, LaPToP.ProgramTheory.Interpreter.run_zero, LaPToP.ProgramTheory.Interpreter.run_ok, LaPToP.ProgramTheory.Interpreter.run_assign, LaPToP.ProgramTheory.Interpreter.run_seq, LaPToP.ProgramTheory.Interpreter.run_cond, LaPToP.ProgramTheory.Interpreter.run_whileDo, LaPToP.ProgramTheory.Interpreter.run_le, LaPToP.ProgramTheory.Interpreter.denote, LaPToP.ProgramTheory.Interpreter.denote_ok, LaPToP.ProgramTheory.Interpreter.denote_assign, LaPToP.ProgramTheory.Interpreter.denote_seq, LaPToP.ProgramTheory.Interpreter.denote_cond, LaPToP.ProgramTheory.Interpreter.denote_whileDo, LaPToP.ProgramTheory.Interpreter.isProgram_denote")
An interpreter for the programming notations. Chapters 4 and 5 give those
notations as specifications — relations between prestate and poststate — and
the while-loop as a refinement notation; nothing in them runs. This node adds
the executable layer: `Interpreter.Prog` is the abstract syntax of $`\mathit{ok}`,
$`x := e`, $`P.\ Q`, $`\mathbf{if}\ b\ \mathbf{then}\ P\ \mathbf{else}\ Q` and
$`\mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od}`; `Interpreter.run` executes a
program from a state, returning the final state or, when the fuel is exhausted,
nothing; and `Interpreter.denote` maps the syntax onto exactly the
specifications of {uses "specification_notations"}[] and {uses "assignment_spec"}[],
so that the interpreter interprets this theory and no other. One unit of fuel
is spent per level of the execution tree, which makes `run` structurally
recursive and therefore reducible by the kernel; more fuel never spoils a
successful run (`run_le`).

For the loop a specification is needed where the book has only the refinement
notation of {uses "while_loop"}[]. `Spec.whileRel b R` is the inductively
defined relation of the terminating executions: either $`b` fails and the state
is unchanged, or $`b` holds, $`R` takes one step, and the loop relates the
result to the final state. It is a fixed point of the book's unfolding,
$`\mathbf{while}\ b\ \mathbf{do}\ R\ \mathbf{od} = \mathbf{if}\ b\ \mathbf{then}\ R.\ \mathbf{while}\ b\ \mathbf{do}\ R\ \mathbf{od}\ \mathbf{else}\ \mathit{ok}`,
hence satisfies the while-refinement it is meant to satisfy; and it is the
strongest such solution, so any $`W` proved by the book's while-refinement rule
is refined by it. That last theorem is what makes an execution trustworthy. A
loop-free program denotes a program in the sense of
{uses "program_definition"}[].

Honest deviations. Expressions are semantic — a Lean function of the prestate,
as in {uses "assignment_spec"}[], where the book restricts them to implemented
expressions — so `Prog` is data only up to its embedded expression functions;
the demonstrations below close that gap with a first-order expression syntax of
their own. The loop is the only unbounded construct; the fuel-free account of
running it is the next node. Out of scope this round, and claimed nowhere:
concurrency, the time variable, channels and interaction, variable declaration
and framing, assertions, the full surface syntax of the book, and a
command-line binary outside Lean.
:::

:::theorem "interpreter_soundness" (parent := "programming_language_core") (tags := "programs, interpreter, execution") (effort := "medium") (lean := "LaPToP.ProgramTheory.Interpreter.denote_of_run, LaPToP.ProgramTheory.Interpreter.exists_run_of_denote, LaPToP.ProgramTheory.Interpreter.deterministic_denote, LaPToP.ProgramTheory.Interpreter.run_sound, LaPToP.ProgramTheory.Interpreter.run_while_sound, LaPToP.ProgramTheory.Interpreter.Demo.Vr, LaPToP.ProgramTheory.Interpreter.Demo.St, LaPToP.ProgramTheory.Interpreter.Demo.Exp, LaPToP.ProgramTheory.Interpreter.Demo.Exp.eval, LaPToP.ProgramTheory.Interpreter.Demo.Bexp, LaPToP.ProgramTheory.Interpreter.Demo.Bexp.eval, LaPToP.ProgramTheory.Interpreter.Demo.P, LaPToP.ProgramTheory.Interpreter.Demo.set, LaPToP.ProgramTheory.Interpreter.Demo.ifThen, LaPToP.ProgramTheory.Interpreter.Demo.loop, LaPToP.ProgramTheory.Interpreter.Demo.start, LaPToP.ProgramTheory.Interpreter.Demo.sumTo, LaPToP.ProgramTheory.Interpreter.Demo.sumTo_ten, LaPToP.ProgramTheory.Interpreter.Demo.sumTo_twenty, LaPToP.ProgramTheory.Interpreter.Demo.sumTo_no_fuel, LaPToP.ProgramTheory.Interpreter.Demo.countBody, LaPToP.ProgramTheory.Interpreter.Demo.countCond, LaPToP.ProgramTheory.Interpreter.Demo.count, LaPToP.ProgramTheory.Interpreter.Demo.W, LaPToP.ProgramTheory.Interpreter.Demo.countCond_eval, LaPToP.ProgramTheory.Interpreter.Demo.whileRefines_W, LaPToP.ProgramTheory.Interpreter.Demo.count_sound, LaPToP.ProgramTheory.Interpreter.Demo.count_seven")
The interpreter agrees with the theory. Soundness: if a run succeeds, its
result satisfies the denoted specification. Completeness: every behaviour the
denotation allows is achieved by a run with enough fuel. Together they give
determinism of every denoted program — as an executed program must be. The
last two are stated for the deterministic fragment `Interpreter.Det`, every
notation but the choice — the one construct a deterministic interpreter cannot
be complete for, added later in the node on assertions and backtracking. Then
comes the bridge from a development to an execution: if $`W \Leftarrow` the denotation of
$`p` has been proved, then every successful run of $`p` satisfies $`W`
({uses "refinement_laws"}[]), and for a loop developed the book's way
({uses "while_loop"}[]) every terminating run satisfies the specification
proved for it.

The demonstrations run three integer variables $`n`, $`i`, $`s` with a
first-order expression syntax and its evaluator, so the example programs are
data. $`i := 0.\ s := 0.\ \mathbf{while}\ i \neq n\ \mathbf{do}\ i := i+1.\ s := s+i\ \mathbf{od}`
computes $`1 + \ldots + 10 = 55` and $`1 + \ldots + 20 = 210`; with too little
fuel the run reports failure rather than a wrong answer. The counting loop
$`\mathbf{while}\ i \neq n\ \mathbf{do}\ i := i+1.\ s := s+1\ \mathbf{od}` is given
the specification $`i \leq n \Rightarrow s' = s + (n - i)`, proved as a
while-refinement in the book's two cases, and every terminating run of it then
satisfies that specification. The three numerical results are proved by
reduction in the kernel, not merely observed.
:::

:::proof "interpreter_soundness"
Soundness by induction on the fuel and cases on the program; the loop case
builds a step or an exit of the loop relation. Completeness by induction on the
program, with an inner induction on the loop relation for the loop, taking the
maximum of the two fuels at each composition and appealing to monotonicity in
the fuel. Determinism: two behaviours give two successful runs, which agree
when both are given the larger fuel. The counting loop needs the two cases of
Refinement by Cases ({uses "refinement_by_steps_parts_cases"}[]) and the
Substitution Law ({uses "substitution_law"}[]) for the body.
:::

:::theorem "interpreter_partial_correctness" (parent := "programming_language_core") (tags := "programs, interpreter, execution, partial-correctness") (effort := "medium") (lean := "LaPToP.ProgramTheory.Spec.whileRel_of_always, LaPToP.ProgramTheory.Spec.whileRel_invariant, LaPToP.ProgramTheory.Interpreter.Eval, LaPToP.ProgramTheory.Interpreter.eval_of_run, LaPToP.ProgramTheory.Interpreter.denote_of_eval, LaPToP.ProgramTheory.Interpreter.eval_of_denote, LaPToP.ProgramTheory.Interpreter.eval_eq_denote, LaPToP.ProgramTheory.Interpreter.exists_run_of_eval, LaPToP.ProgramTheory.Interpreter.eval_iff_exists_run, LaPToP.ProgramTheory.Interpreter.eval_unique, LaPToP.ProgramTheory.Interpreter.eval_sound, LaPToP.ProgramTheory.Interpreter.eval_while_sound, LaPToP.ProgramTheory.Interpreter.eval_while_invariant, LaPToP.ProgramTheory.Interpreter.Diverges, LaPToP.ProgramTheory.Interpreter.diverges_iff, LaPToP.ProgramTheory.Interpreter.diverges_whileDo, LaPToP.ProgramTheory.Interpreter.Demo.countBody_preserves, LaPToP.ProgramTheory.Interpreter.Demo.count_partial, LaPToP.ProgramTheory.Interpreter.Demo.forever_diverges, LaPToP.ProgramTheory.Interpreter.Demo.forever_run_none")
Execution without fuel, and partial correctness. The fuel of
{uses "interpreter"}[] is an artefact of Lean's termination checking, not of the
theory: execution is a relation between a program, a prestate and a poststate,
and a nonterminating computation is one that relates its prestate to no
poststate at all. `Interpreter.Eval` is that relation — the big-step operational
semantics of the five notations, with no budget anywhere — and it coincides
exactly with the denotation, so running a program, evaluating it and specifying
it are one relation; a fuelled run is an evaluation, and every evaluation is
reached by some fuel.

What the coincidence buys is partial correctness, and only that: $`\mathsf{Eval}\ p\ \sigma\ \sigma'`
says that $`p` *can* finish in $`\sigma'`, so if $`W \Leftarrow` the denotation of
$`p` has been proved then every terminating execution of $`p` satisfies $`W`,
and nothing is claimed about whether $`p` terminates. The loop invariant rule
is proved in that form: if $`I` holds of the prestate and every iteration
preserves it, then every terminating execution of
$`\mathbf{while}\ b\ \mathbf{do}\ P\ \mathbf{od}` ends in a state satisfying
$`I` in which $`b` is false. Neither fuel nor a variant appears in its statement
or its proof, which is the point: this is the rule of
{uses "while_loop"}[] with the termination obligation dropped. A program that
relates its prestate to no poststate `Diverges`, and the interpreter reports it
honestly, failing for every fuel rather than returning an answer.

The demonstrations develop the counting loop a second way — by the invariant
$`s = i`, with no termination argument, concluding $`s' = n` on every execution
that finishes — and exhibit $`\mathbf{while}\ 0 \le 0\ \mathbf{do}\ \mathit{ok}\ \mathbf{od}`,
proved to diverge from every state. The tie to the least-fixed-point loop of
Section 6.1.1, which describes the nonterminating computations that no account
of runs can, is the node `loop_definition_terminating_runs` in the chapter on
recursion.
:::

:::proof "interpreter_partial_correctness"
That a fuelled run is an evaluation is by induction on the fuel and cases on the
program. That an evaluation satisfies the denotation is by induction on the
evaluation, and the converse by induction on the program with an inner induction
on the loop relation, so the two are equal as relations; the fuelled
characterization then follows from soundness and completeness of
{uses "interpreter_soundness"}[]. The invariant rule is an induction on the loop
relation whose motive is the implication from the invariant, which is why no
termination argument is needed. Divergence and failure for every fuel are each
immediate from the other by the fuelled characterization.
:::

:::theorem "interpreter_scope" (parent := "programming_language_core") (tags := "programs, interpreter, scope, frames") (effort := "medium") (lean := "LaPToP.ProgramTheory.Spec.inScope, LaPToP.ProgramTheory.Spec.newLocal, LaPToP.ProgramTheory.Spec.newLocal_self, LaPToP.ProgramTheory.Spec.newLocal_eq, LaPToP.ProgramTheory.Spec.newLocal_mono, LaPToP.ProgramTheory.Spec.newLocal_refines_newVar, LaPToP.ProgramTheory.Interpreter.run_newLocal, LaPToP.ProgramTheory.Interpreter.denote_newLocal, LaPToP.ProgramTheory.Interpreter.writes, LaPToP.ProgramTheory.Interpreter.writes_ok, LaPToP.ProgramTheory.Interpreter.writes_assign, LaPToP.ProgramTheory.Interpreter.writes_seq, LaPToP.ProgramTheory.Interpreter.writes_cond, LaPToP.ProgramTheory.Interpreter.writes_whileDo, LaPToP.ProgramTheory.Interpreter.writes_newLocal, LaPToP.ProgramTheory.Interpreter.unchanged_of_eval, LaPToP.ProgramTheory.Interpreter.frame_denote, LaPToP.ProgramTheory.Interpreter.refines_frame_denote, LaPToP.ProgramTheory.Interpreter.denote_newLocal_eq, LaPToP.ProgramTheory.Interpreter.refines_newVar_denote, LaPToP.ProgramTheory.Interpreter.eval_newLocal_self, LaPToP.ProgramTheory.Interpreter.Demo.declare, LaPToP.ProgramTheory.Interpreter.Demo.withLocal, LaPToP.ProgramTheory.Interpreter.Demo.withLocal_run, LaPToP.ProgramTheory.Interpreter.Demo.withLocal_no_leak, LaPToP.ProgramTheory.Interpreter.Demo.writes_withLocal, LaPToP.ProgramTheory.Interpreter.Demo.frame_withLocal")
Scope, executably. The frame of {uses "variable_suspension"}[] says what a
computation does *not* do, and the declaration of
{uses "variable_declaration"}[] puts the local variable beside the nonlocal
state. Neither runs as it stands, and this node makes both part of the syntax
that {uses "interpreter"}[] executes.

The frame is discharged statically. `Interpreter.writes` reads a program's write
set off its syntax — a declaration hiding its own variable — and no terminating
execution touches a variable outside it. Hence for
$`\mathsf{writes}\ p \subseteq xs` the framed specification and the denotation
are the same relation, $`\mathbf{frame}\ xs \cdot p = p`, so a framed
specification is implemented by a syntactic check on the program rather than an
argument about its behaviour.

The declaration borrows a slot. A machine with one flat state has no room beside
it, so `Prog.newLocal` runs the body with the state slot named $`x` holding the
initial value and puts back what the slot held before. That this is the book's
notation and not a new one is the content of `Spec.newLocal_eq`: the flat-state
declaration is exactly $`\mathbf{new}\ x : \mathit{Val} := e \cdot P` on the pair
state, framed so that the borrowed slot is restored. Since a machine must choose
the local's initial value where the book leaves it arbitrary, what is executed
*refines* $`\mathbf{new}\ x : \mathit{Val} \cdot P` — the honest direction, and the
one a development needs. The fuelled run, the fuel-free evaluation of
{uses "interpreter_partial_correctness"}[] and the denotation stay in lockstep
for the new construct, soundness, completeness and determinism included, because
the declaration that is executed is the initializing one.

The demonstration declares $`\mathbf{new}\ i : \mathit{int} := 5 \cdot s := s + i`: the
kernel runs it, $`i` is proved unchanged and $`s` increased by 5 from any
prestate, and the write set of the whole declaration is $`s` alone.

What remains. Whether a declaration is a *program* in the sense of
{uses "program_definition"}[] is not claimed: restoring a borrowed slot is not
expressible in the four notations, so the loop-free predicate has no case for it.
Arrays and assertions are still specifications only, not program syntax, and
there is no command-line binary outside Lean.
:::

:::proof "interpreter_scope"
That the flat-state declaration is the framed initializing declaration is a
two-way calculation on `Function.update`: forwards, the final value of the local
is the slot's value before it is restored; backwards, the frame condition says
the slot already holds what it must be restored to. The write-set theorem is one
induction on the evaluation relation, with the declaration case splitting on
whether the variable is the declared one. The frame equation follows, since
refinement in the other direction is the first conjunct of the frame. Run,
evaluation and denotation extend to the new construct exactly as the other four
notations do ({uses "interpreter_soundness"}[]), the fuel case mapping over the
restore.
:::

:::theorem "interpreter_arrays" (parent := "programming_language_core") (tags := "programs, interpreter, arrays, hehner-5.1.0") (effort := "medium") (lean := "LaPToP.ProgramTheory.Spec.assignAt, LaPToP.ProgramTheory.Spec.assignAt_const, LaPToP.ProgramTheory.Spec.assignAt_seq, LaPToP.ProgramTheory.Spec.assignArr, LaPToP.ProgramTheory.Spec.assignArr_eq_assignAt, LaPToP.ProgramTheory.Arrays.assignElem_iff_assignArr, LaPToP.ProgramTheory.Interpreter.run_assignAt, LaPToP.ProgramTheory.Interpreter.denote_assignAt, LaPToP.ProgramTheory.Interpreter.writes_assignAt, LaPToP.ProgramTheory.Interpreter.denote_assignAt_const, LaPToP.ProgramTheory.Interpreter.denote_assignAt_arr, LaPToP.ProgramTheory.Interpreter.writes_assignAt_arr, LaPToP.ProgramTheory.Interpreter.ArrayDemo.AVr, LaPToP.ProgramTheory.Interpreter.ArrayDemo.ASt, LaPToP.ProgramTheory.Interpreter.ArrayDemo.a_injective, LaPToP.ProgramTheory.Interpreter.ArrayDemo.setElem, LaPToP.ProgramTheory.Interpreter.ArrayDemo.denote_setElem, LaPToP.ProgramTheory.Interpreter.ArrayDemo.zero, LaPToP.ProgramTheory.Interpreter.ArrayDemo.ex₁, LaPToP.ProgramTheory.Interpreter.ArrayDemo.ex₁_run, LaPToP.ProgramTheory.Interpreter.ArrayDemo.ex₁_naive, LaPToP.ProgramTheory.Interpreter.ArrayDemo.ex₂, LaPToP.ProgramTheory.Interpreter.ArrayDemo.ex₂_result, LaPToP.ProgramTheory.Interpreter.ArrayDemo.ex₂_run, LaPToP.ProgramTheory.Interpreter.ArrayDemo.writes_ex₁, LaPToP.ProgramTheory.Interpreter.ArrayDemo.frame_ex₁")
Array element assignment, executed. The lesson of {uses "data_structures"}[] is
that $`A\,i := e` does not have a name on its left that the syntax fixes: it
writes the slot that $`i` names in the *prestate*, which is why substituting
into the syntax goes wrong. `Prog.assignAt` is precisely that construct —
assignment to a computed name — and `Spec.assignAt_seq` is the substitution that
does work, the book's rule "change $`A\,i := e` to $`A := i \to e \mid A` before
applying any programming theory". The assignment of {uses "assignment_spec"}[],
whose name is fixed and for which the Substitution Law is sound, is the special
case with a constant name.

An array reaches a flat state as the family of slots it indexes: "in program
theory, an array is a list variable", and a list variable on a state that maps
names to values is the family $`a\,0, a\,1, \ldots`. `Spec.assignArr` is the
book's $`A'i = e \land (\forall j \cdot j \neq i \Rightarrow A'j = A\,j) \land x' = x \land \ldots`
read that way, and it is assignment to the computed slot as soon as distinct
indices name distinct slots — the flat-state form of
$`A\,i := e = A := i \to e \mid A`. Nothing is duplicated: the new reading is
proved to be the book's element assignment on the array component of the record
state of {uses "data_structures"}[], with the scalar variables framed. Run,
evaluation and denotation extend to the new construct as the other notations do,
and the frame machinery of {uses "interpreter_scope"}[] covers it unchanged,
since the write set of an element assignment is the range of its computed name.

The demonstration runs the book's own two examples.
$`A\,2 := 3.\ i := 2.\ A\,i := 4` ends with $`i = 2` and $`A\,2 = 4`, so the
example's final test $`A\,i = A\,2` holds — where the Substitution Law had
claimed $`4 = A\,2` after $`A\,2 := 3`, which the run refutes. And
$`A\,2 := 2.\ A(A\,2) := 3` ends with $`A\,2 = 3` from any prestate, so the final
test $`A\,2 = 2` fails and the program is $`\bot` — where the Substitution Law
had left $`A\,2 := 2`. The three numerical facts are reductions in the kernel,
and the second example is also proved for every prestate, not only the one that
is run.

What remains. An array is the family of slots it indexes, not one variable
holding a list, because a flat state has no room for a list value; the two
readings are related but not identified. Two-dimensional arrays and records get
no syntax of their own — on this encoding they are the same construct with a
different index type, which is said rather than proved. Assertions are still
specifications only, not program syntax, and there is no command-line binary
outside Lean.
:::

:::proof "interpreter_arrays"
The flat-state element assignment is assignment to the computed slot by
extensionality on the poststate, splitting a variable into the indexed slot,
another slot of the array, and a variable outside it; injectivity of the family
is needed only for the second. The bridge to the record state is unfolding on
both sides, the clause about variables outside the array being vacuous when the
array is the whole state. Run, evaluation and denotation extend as for
{uses "interpreter_soundness"}[], the new case being as immediate as the
assignment case since the computed name is a function of the prestate. The
executed examples are reductions in the kernel; the general form of the second
unfolds the two assignments in sequence.
:::

:::theorem "interpreter_assertions" (parent := "programming_language_core") (tags := "programs, interpreter, assertions, backtracking, hehner-5.4") (effort := "medium") (lean := "LaPToP.ProgramTheory.Assertions.assert_finite, LaPToP.ProgramTheory.Interpreter.Det, LaPToP.ProgramTheory.Interpreter.run_ensure, LaPToP.ProgramTheory.Interpreter.run_or, LaPToP.ProgramTheory.Interpreter.denote_ensure, LaPToP.ProgramTheory.Interpreter.denote_or, LaPToP.ProgramTheory.Interpreter.writes_ensure, LaPToP.ProgramTheory.Interpreter.writes_or, LaPToP.ProgramTheory.Interpreter.denote_assert_eq_ensure, LaPToP.ProgramTheory.Interpreter.refines_denote_or_left, LaPToP.ProgramTheory.Interpreter.runAll, LaPToP.ProgramTheory.Interpreter.runAll_le, LaPToP.ProgramTheory.Interpreter.eval_of_mem_runAll, LaPToP.ProgramTheory.Interpreter.exists_mem_runAll_of_eval, LaPToP.ProgramTheory.Interpreter.mem_runAll_iff_eval, LaPToP.ProgramTheory.Interpreter.mem_runAll_iff_denote, LaPToP.ProgramTheory.Interpreter.run_eq_none_of_diverges, LaPToP.ProgramTheory.Interpreter.Demo.isOne, LaPToP.ProgramTheory.Interpreter.Demo.isOne_eval, LaPToP.ProgramTheory.Interpreter.Demo.choice, LaPToP.ProgramTheory.Interpreter.Demo.backtrack, LaPToP.ProgramTheory.Interpreter.Demo.denote_backtrack, LaPToP.ProgramTheory.Interpreter.Demo.runAll_backtrack, LaPToP.ProgramTheory.Interpreter.Demo.run_backtrack, LaPToP.ProgramTheory.Interpreter.Demo.not_det_backtrack, LaPToP.ProgramTheory.Interpreter.Demo.det_count, LaPToP.ProgramTheory.Interpreter.Demo.eval_backtrack")
Assertions and the choice, executed. `Prog.ensure b` succeeds without changing
anything when $`b` holds and has no poststate when it does not — the reading of
{uses "backtracking"}[] that "when $`b` is false, ... this is unimplementable",
now as something a machine does. An assertion is the same program: the
else-branch of {uses "assertions"}[] prints a message and waits until
$`\infty`, and a machine with no clock and no screen cannot tell that from
producing nothing. The identification is proved rather than assumed: from a
state at finite time, the behaviours of $`\mathbf{assert}\ b` that end in finite
time are exactly $`\mathbf{ensure}\ b`, so the whole difference between them —
that an assertion is implementable, by waiting forever, and an $`\mathbf{ensure}`
is not — lives in the time variable this state has not got.

`Prog.or` is the choice, whose point is that an implementation "must choose the
right one to satisfy a later binary expression". It is the one construct a
deterministic interpreter cannot be complete for, and the node says so in the
statements: completeness and determinism now hold on the *deterministic
fragment*, every notation but the choice. The fuelled interpreter resolves a
choice by taking the left branch — the book's "normally this choice is made as a
refinement" — which is sound and cannot backtrack.

Backtracking is therefore given its own interpreter. `runAll` returns every
poststate reachable within the fuel: a choice branches, an $`\mathbf{ensure}`
filters, and more fuel never loses a result. It is sound and complete for the
whole language, choice included — the states it finds are exactly the executions
of {uses "interpreter_partial_correctness"}[], hence exactly the denotation.
The demonstration is the book's own example
$`s := 0\ \mathbf{or}\ s := 1.\ \mathbf{ensure}\ s = 1 = s := 1`: proved from the
laws of {uses "backtracking"}[], found by the search (one poststate, with
$`s = 1`, computed in the kernel), missed by the deterministic interpreter, and
proved to hold of every execution from every prestate.

What remains. An assertion and an $`\mathbf{ensure}` are the same program here,
which is honest only because the state has no time variable and no output
channel; the book distinguishes them. The error message of a failed assertion is
not modelled. Nothing in the interpreter yet reaches concurrency, the time
variable, or channels, and there is still no command-line binary outside Lean —
the natural next slice.
:::

:::proof "interpreter_assertions"
The finite-time identification is the two cases of the assertion: when $`b`
holds it is $`\mathit{ok}`, and when it fails the final time is $`\infty`, which
the finiteness hypothesis excludes. Run, evaluation and denotation extend to both
new constructs as the other notations do ({uses "interpreter_soundness"}[]), the
choice case going to the left branch. Soundness and completeness of the search
are two inductions — on the fuel with cases on the program, and on the evaluation
— with list membership distributing over the concatenation of a choice and the
flat map of a composition, and the maximum of two fuels at each composition,
appealing to monotonicity in the fuel. The example follows from the law
$`(P \lor Q).\ \mathbf{ensure}\ b = (P.\ \mathbf{ensure}\ b) \lor (Q.\ \mathbf{ensure}\ b)`
of {uses "backtracking"}[]; the computed results are reductions in the kernel.
:::

:::theorem "interpreter_cli" (parent := "programming_language_core") (tags := "programs, interpreter, syntax, cli") (effort := "medium") (lean := "LaPToP.ProgramTheory.Interpreter.Demo.Tok, LaPToP.ProgramTheory.Interpreter.Demo.Tok.render, LaPToP.ProgramTheory.Interpreter.Demo.Toks, LaPToP.ProgramTheory.Interpreter.Demo.tokenize, LaPToP.ProgramTheory.Interpreter.Demo.parseExp, LaPToP.ProgramTheory.Interpreter.Demo.parseExpTail, LaPToP.ProgramTheory.Interpreter.Demo.parseTerm, LaPToP.ProgramTheory.Interpreter.Demo.parseTermTail, LaPToP.ProgramTheory.Interpreter.Demo.parseFactor, LaPToP.ProgramTheory.Interpreter.Demo.parseCond, LaPToP.ProgramTheory.Interpreter.Demo.parseCondTail, LaPToP.ProgramTheory.Interpreter.Demo.parseRel, LaPToP.ProgramTheory.Interpreter.Demo.parseProg, LaPToP.ProgramTheory.Interpreter.Demo.parseChoice, LaPToP.ProgramTheory.Interpreter.Demo.parseStmt, LaPToP.ProgramTheory.Interpreter.Demo.parseToks, LaPToP.ProgramTheory.Interpreter.Demo.parseProgram, LaPToP.ProgramTheory.Interpreter.Demo.sumToSrc, LaPToP.ProgramTheory.Interpreter.Demo.sumToToks, LaPToP.ProgramTheory.Interpreter.Demo.parseToks_sumTo, LaPToP.ProgramTheory.Interpreter.Demo.countSrc, LaPToP.ProgramTheory.Interpreter.Demo.countToks, LaPToP.ProgramTheory.Interpreter.Demo.parseToks_count, LaPToP.ProgramTheory.Interpreter.Demo.backtrackSrc, LaPToP.ProgramTheory.Interpreter.Demo.backtrackToks, LaPToP.ProgramTheory.Interpreter.Demo.parseToks_backtrack, LaPToP.ProgramTheory.Interpreter.Demo.withLocalSrc, LaPToP.ProgramTheory.Interpreter.Demo.withLocalToks, LaPToP.ProgramTheory.Interpreter.Demo.parseToks_withLocal, LaPToP.ProgramTheory.Interpreter.Demo.selfTests, LaPToP.ProgramTheory.Interpreter.Demo.state, LaPToP.ProgramTheory.Interpreter.Demo.state_zero_zero, LaPToP.ProgramTheory.Interpreter.Demo.renderState")
A concrete syntax, and programs run from a shell. Everything the interpreter of
{uses "interpreter"}[] executes has so far been written in Lean. This node adds
the layer that was missing for it to be used as an interpreter: a tokenizer and a
recursive-descent parser from text into the *same* abstract syntax, so a parsed
program is executed by the same `run` and `runAll` and means the same
specification. No semantics is added.

The grammar is the book's where it can be. Sequential composition is written
$`.` and binds loosest, so $`s := 0\ \mathbf{or}\ s := 1.\ \mathbf{ensure}\ s = 1`
is the choice followed by the $`\mathbf{ensure}`, as
{uses "interpreter_assertions"}[] reads it. Assignment, $`\mathbf{if}`,
$`\mathbf{while}`, the local declaration, $`\mathbf{ensure}`,
$`\mathbf{assert}` and the choice all have surface forms. Parsing is total:
tokenizer and parser are structurally recursive on a fuel budget read off the
input, and every failure is a message rather than a partial function.

What ties the binary to the development is four theorems: the parser turns the
tokens of each demonstration program into *that very Lean term* — the summation,
the counting loop with its proved specification, the backtracking example and the
local declaration that does not leak. So what runs from the command line is what
the theorems of {uses "interpreter_soundness"}[] and
{uses "interpreter_scope"}[] are about, not a lookalike.

Honest scope. The theorems are stated of the token lists, not of the source text:
reducing a string literal to its characters in the kernel costs minutes per
example while reducing the parser is instant, so that the tokenizer takes each
source to those tokens is *checked when the binary runs* and not proved. This is
the surface syntax of the demonstrations, not of the book: three integer
variables of fixed names, no array syntax (the array demonstration has its own
variable type), no declarations of new names, and no output. Nothing here reaches
concurrency, the time variable, or channels.
:::

:::proof "interpreter_cli"
Each parsing function recurses on a fuel argument, which makes the definitions
structural and therefore cheap for the kernel to reduce; that is what lets the
agreement with the demonstration programs be a theorem closed by reflexivity
rather than a test. The digits of a numeral are folded by hand instead of through
the string library for the same reason. The four agreements are then reflexivity
on closed terms.
:::
