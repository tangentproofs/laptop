import Verso
import VersoManual
import VersoBlueprint
import LaPToP.TheoryDesign.Stack

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Theory Design and Implementation" =>

:::group "theory_design_core"
Hehner's Chapter 7: "the stack, the queue, and the tree ... are presented here
as case studies in theory design and implementation", a theory being "a
contract between two parties, an implementer and a user". Data-stack theory
and its implementation are formalized in `LaPToP.TheoryDesign.Stack`.
:::

:::definition "data_stack_theory" (parent := "theory_design_core") (lean := "LaPToP.TheoryDesign.DataStackTheory, LaPToP.TheoryDesign.DataStackTheory.construction, LaPToP.TheoryDesign.DataStackTheory.construction_pred, LaPToP.TheoryDesign.DataStackTheory.induction_bunch, LaPToP.TheoryDesign.DataStackTheory.eq_empty_or_push, LaPToP.TheoryDesign.DataStackTheory.push_inj_of_lifo, LaPToP.TheoryDesign.WeakStackTheory, LaPToP.TheoryDesign.DataStackTheory.toWeak, LaPToP.TheoryDesign.unitStack, LaPToP.TheoryDesign.unitStack_push_eq_empty")
"We introduce the syntax $`\mathit{stack}`, $`\mathit{empty}`, $`\mathit{push}`,
$`\mathit{pop}`, and $`\mathit{top}`." The axioms: $`\mathit{empty} : \mathit{stack}`,
$`\mathit{push} : \mathit{stack} \to X \to \mathit{stack}`, $`\mathit{pop} : \mathit{stack} \to \mathit{stack}`,
$`\mathit{top} : \mathit{stack} \to X`; construction
$`\mathit{empty}, \mathit{push}\ \mathit{stack}\ X : \mathit{stack}` (equivalently
$`P\,\mathit{empty} \land (\forall s : \mathit{stack} \cdot \forall x : X \cdot P\,s \Rightarrow P(\mathit{push}\ s\ x)) \Leftarrow \forall s : \mathit{stack} \cdot P\,s`);
induction $`\mathit{empty}, \mathit{push}\ B\ X : B \Rightarrow \mathit{stack} : B` (equivalently
$`P\,\mathit{empty} \land (\forall s : \mathit{stack} \cdot \forall x : X \cdot P\,s \Rightarrow P(\mathit{push}\ s\ x)) \Rightarrow \forall s : \mathit{stack} \cdot P\,s`),
"to exclude anything else from being a stack"; "to say that the constructors
always construct different stacks", $`\mathit{push}\ s\ x \neq \mathit{empty}` and
$`\mathit{push}\ s\ x = \mathit{push}\ t\ y = (s = t \land x = y)`; and "last in, first
out": $`\mathit{pop}(\mathit{push}\ s\ x) = s`, $`\mathit{top}(\mathit{push}\ s\ x) = x`. A theory
is a Lean structure `DataStackTheory X` — a carrier type (the bunch
$`\mathit{stack}`, taken as a type so that the operations are total on it), the
four operations, and the axioms as fields; construction is automatic for a
type, and both predicate forms are proved. Consequences: every stack is
$`\mathit{empty}` or a $`\mathit{push}`, and the LIFO axioms alone make
$`\mathit{push}` injective. "According to the axioms we have so far" — before the
last four — "it is possible that all stacks are equal": the one-element carrier
satisfies the weak axioms, so $`\mathit{push}\ s\ x \neq \mathit{empty}` is independent of
them. Uses {uses "bunch_vs_set"}[], {uses "function_notation"}[] and
{uses "nat_induction_predicate"}[].
:::

:::theorem "data_stack_implementation" (parent := "theory_design_core") (tags := "theory design, stacks, hehner-7.0.1") (effort := "small") (lean := "LaPToP.TheoryDesign.ListStack.empty, LaPToP.TheoryDesign.ListStack.push, LaPToP.TheoryDesign.ListStack.pop, LaPToP.TheoryDesign.ListStack.top, LaPToP.TheoryDesign.ListStack.push_contents, LaPToP.TheoryDesign.ListStack.push_ne_empty, LaPToP.TheoryDesign.ListStack.induction, LaPToP.TheoryDesign.ListStack.pop_push, LaPToP.TheoryDesign.ListStack.top_push, LaPToP.TheoryDesign.ListStack.push_inj, LaPToP.TheoryDesign.ListStack.theory")
"Suppose that lists and functions are implemented. Then we can implement a
stack of integers by the following definitions: $`\mathit{stack} = [*\mathit{int}]`,
$`\mathit{empty} = [\mathit{nil}]`, $`\mathit{push} = \langle s : \mathit{stack} \cdot \langle x : \mathit{int} \cdot s ;; [x] \rangle\rangle`,
$`\mathit{pop} = \langle s : \mathit{stack} \cdot \mathbf{if}\ s = \mathit{empty}\ \mathbf{then}\ \mathit{empty}\ \mathbf{else}\ s\,[0;..\# s - 1] \rangle`,
$`\mathit{top} = \langle s : \mathit{stack} \cdot \mathbf{if}\ s = \mathit{empty}\ \mathbf{then}\ 0\ \mathbf{else}\ s\,(\# s - 1) \rangle`.
To prove that a theory is implemented, we prove (the axioms of the theory)
$`\Leftarrow` (the definitions of the implementation). ... According to a
distributive law, this can be done one axiom at a time." The book's worked
calculation is $`\mathit{top}(\mathit{push}\ s\ x) = x`; here every axiom is proved and the
implementation is a term of type `DataStackTheory ℤ` — the induction axiom by
induction on lists from the right. "Since we implemented it using list and
function theory, we know that if list and function theory are consistent, so
is stack theory." Uses {uses "data_stack_theory"}[], {uses "list_packaging"}[]
and {uses "list_axioms"}[].
:::

:::theorem "stack_theory_incomplete" (parent := "theory_design_core") (tags := "theory design, stacks, hehner-7.0.1") (effort := "small") (lean := "LaPToP.TheoryDesign.ListStack.pop_empty, LaPToP.TheoryDesign.ListStack.top_empty, LaPToP.TheoryDesign.ListStack'.pop, LaPToP.TheoryDesign.ListStack'.top, LaPToP.TheoryDesign.ListStack'.theory, LaPToP.TheoryDesign.ListStack'.pop_empty_ne, LaPToP.TheoryDesign.ListStack'.top_empty_ne, LaPToP.TheoryDesign.pop_empty_unclassified, LaPToP.TheoryDesign.top_empty_unclassified")
"Is stack theory complete? To show that a binary expression is unclassified,
we must implement stacks twice, making the expression a theorem in one
implementation, and an antitheorem in the other. The expressions
$`\mathit{pop}\ \mathit{empty} = \mathit{empty}` and $`\mathit{top}\ \mathit{empty} = 0` are theorems
in our implementation, but we can alter the implementation as follows —
$`\mathit{pop} = \langle s \cdot \mathbf{if}\ s = \mathit{empty}\ \mathbf{then}\ \mathit{push}\ \mathit{empty}\ 0\ \mathbf{else}\ \ldots \rangle`,
$`\mathit{top} = \langle s \cdot \mathbf{if}\ s = \mathit{empty}\ \mathbf{then}\ 1\ \mathbf{else}\ \ldots \rangle` —
to make them antitheorems. So stack theory is incomplete." Both
implementations are terms of type `DataStackTheory ℤ`, and neither
$`\mathit{pop}\ \mathit{empty} = \mathit{empty}` nor its negation holds in every model.
"The stack user must not use $`\mathit{pop}\ \mathit{empty} = \mathit{empty}` even though the
stack implementer has provided it; if the user wants it, it should be added to
the theory." Uses {uses "data_stack_implementation"}[].
:::
