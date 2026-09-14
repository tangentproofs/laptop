import Verso
import VersoManual
import VersoBlueprint
import LaPToP.ProgramTheory.WhileLoop
import LaPToP.ProgramTheory.ForLoop

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Programming Language" =>

:::group "programming_language_core"
Hehner's Chapter 5: the programming notations of "several languages" —
control structures, scope, data structures, subprograms — explained as
refinement notations or as specifications in the theory of Chapter 4. The
while-loop of Section 5.2.0 is formalized in `LaPToP.ProgramTheory.WhileLoop`
and the for-loop of Section 5.2.3 in `LaPToP.ProgramTheory.ForLoop`.
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
