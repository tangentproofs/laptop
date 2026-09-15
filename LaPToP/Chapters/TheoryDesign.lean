import Verso
import VersoManual
import VersoBlueprint
import LaPToP.TheoryDesign.Stack
import LaPToP.TheoryDesign.SimpleStack
import LaPToP.TheoryDesign.Queue
import LaPToP.TheoryDesign.Tree
import LaPToP.TheoryDesign.ProgramStack

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Theory Design and Implementation" =>

:::group "theory_design_core"
Hehner's Chapter 7: "the stack, the queue, and the tree ... are presented here
as case studies in theory design and implementation", a theory being "a
contract between two parties, an implementer and a user". The data theories
of Section 7.0 are formalized in `LaPToP.TheoryDesign.Stack`, `SimpleStack`,
`Queue` and `Tree`; program-stack theory (Section 7.1) in
`LaPToP.TheoryDesign.ProgramStack`.
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

:::definition "simple_data_stack_theory" (parent := "theory_design_core") (lean := "LaPToP.TheoryDesign.SimpleStackTheory, LaPToP.TheoryDesign.SimpleStackTheory.ofDataStack, LaPToP.TheoryDesign.SimpleStackTheory.listModel, LaPToP.TheoryDesign.SimpleStackTheory.streamModel, LaPToP.TheoryDesign.SimpleStackTheory.streamModel_every_push")
"In the data-stack theory just presented, we have axioms $`\mathit{empty} : \mathit{stack}`
and $`\mathit{pop} : \mathit{stack} \to \mathit{stack}`; from them we can prove
$`\mathit{pop}\ \mathit{empty} : \mathit{stack}`. ... An implementer is obliged to give a
stack for $`\mathit{pop}\ \mathit{empty}`, though it does not matter which one. If we never
want to pop an empty stack, then the theory is too strong. ... For most
purposes, it is sufficient to be able to push items onto a stack, pop items
off, and look at the top item. ... Our simpler data-stack theory introduces the
names $`\mathit{stack}`, $`\mathit{push}`, $`\mathit{pop}`, and $`\mathit{top}` with the following
four axioms: $`\mathit{stack} \neq \mathit{null}`, $`\mathit{push}\ s\ x : \mathit{stack}`,
$`\mathit{pop}(\mathit{push}\ s\ x) = s`, $`\mathit{top}(\mathit{push}\ s\ x) = x`." The design
remarks are made concrete: every data-stack theory is a simple one, the list
implementation is a model, and there is a model with *no* empty stack at all —
infinite stacks $`\mathit{nat} \to X`, in which every stack is a $`\mathit{push}` ("we
never need an empty stack, nor to test if a stack is empty"). "As an
engineering activity, theory design is the art of excluding all unwanted
implementations while allowing all the others." Uses {uses "data_stack_theory"}[]
and {uses "data_stack_implementation"}[].
:::

:::definition "data_queue_theory" (parent := "theory_design_core") (lean := "LaPToP.TheoryDesign.DataQueueTheory, LaPToP.TheoryDesign.DataQueueTheory.eq_emptyq_or_join, LaPToP.TheoryDesign.DataQueueTheory.front_foldl, LaPToP.TheoryDesign.DataQueueTheory.front_joins, LaPToP.TheoryDesign.ListQueue.emptyq, LaPToP.TheoryDesign.ListQueue.join, LaPToP.TheoryDesign.ListQueue.leave, LaPToP.TheoryDesign.ListQueue.front, LaPToP.TheoryDesign.ListQueue.join_ne_emptyq, LaPToP.TheoryDesign.ListQueue.theory")
"The queue data structure, also known as a buffer ... is the structure with the
motto: the first one in is the first one out. We introduce the syntax
$`\mathit{queue}`, $`\mathit{emptyq}`, $`\mathit{join}`, $`\mathit{leave}`, and $`\mathit{front}`."
Axioms: $`\mathit{emptyq} : \mathit{queue}`, $`\mathit{join}\ q\ x : \mathit{queue}`;
$`\mathit{join}\ q\ x \neq \mathit{emptyq}`, $`\mathit{join}\ q\ x = \mathit{join}\ r\ y = (q = r \land x = y)`;
queue induction $`\mathit{emptyq}, \mathit{join}\ B\ X : B \Rightarrow \mathit{queue} : B`; and
"first in, first out": $`\mathit{leave}(\mathit{join}\ \mathit{emptyq}\ x) = \mathit{emptyq}`,
$`q \neq \mathit{emptyq} \Rightarrow \mathit{leave}(\mathit{join}\ q\ x) = \mathit{join}(\mathit{leave}\ q)\ x`,
$`\mathit{front}(\mathit{join}\ \mathit{emptyq}\ x) = x`,
$`q \neq \mathit{emptyq} \Rightarrow \mathit{front}(\mathit{join}\ q\ x) = \mathit{front}\ q`. The typing
axioms $`q \neq \mathit{emptyq} \Rightarrow \mathit{leave}\ q : \mathit{queue}` and
$`q \neq \mathit{emptyq} \Rightarrow \mathit{front}\ q : X` "can now be proved" (automatic for a
carrier type). Derived: every queue is $`\mathit{emptyq}` or a $`\mathit{join}`, and the
item joined to the empty queue stays at the front whatever is joined afterwards.
"Data-queue implementation raises no new issues, so we leave it as Exercise
426": lists with $`\mathit{join}\ q\ x = q ;; [x]`, $`\mathit{leave}\ q = q\,[1;..\# q]`,
$`\mathit{front}\ q = q\,0` are a `DataQueueTheory ℤ`. Uses {uses "data_stack_theory"}[]
and {uses "list_axioms"}[].
:::

:::definition "data_tree_theory" (parent := "theory_design_core") (lean := "LaPToP.TheoryDesign.DataTreeTheory, LaPToP.TheoryDesign.SimpleTreeTheory, LaPToP.TheoryDesign.DataTreeTheory.eq_emptree_or_graft, LaPToP.TheoryDesign.DataTreeTheory.graft_inj_of_selectors, LaPToP.TheoryDesign.DataTreeTheory.toSimple, LaPToP.TheoryDesign.BinTree, LaPToP.TheoryDesign.BinTree.left, LaPToP.TheoryDesign.BinTree.right, LaPToP.TheoryDesign.BinTree.root, LaPToP.TheoryDesign.BinTree.theory, LaPToP.TheoryDesign.BinTree.example₁, LaPToP.TheoryDesign.BinTree.example₁_roots")
"We introduce the syntax $`\mathit{tree}`, $`\mathit{emptree}`, $`\mathit{graft}`, $`\mathit{left}`,
$`\mathit{right}`, $`\mathit{root}`. For the purpose of studying trees, we want a strong
theory": $`\mathit{emptree} : \mathit{tree}`, $`\mathit{graft} : \mathit{tree} \to X \to \mathit{tree} \to \mathit{tree}`,
induction $`\mathit{emptree}, \mathit{graft}\ B\ X\ B : B \Rightarrow \mathit{tree} : B`,
$`\mathit{graft}\ t\ x\ u \neq \mathit{emptree}`,
$`\mathit{graft}\ t\ x\ u = \mathit{graft}\ v\ y\ w = (t = v \land x = y \land u = w)`,
$`\mathit{left}(\mathit{graft}\ t\ x\ u) = t`, $`\mathit{root}(\mathit{graft}\ t\ x\ u) = x`,
$`\mathit{right}(\mathit{graft}\ t\ x\ u) = u`. "For most programming purposes, the following
simpler, weaker theory is sufficient": $`\mathit{tree} \neq \mathit{null}`,
$`\mathit{graft}\ t\ x\ u : \mathit{tree}` and the three selector axioms. Derived: every tree
is $`\mathit{emptree}` or a $`\mathit{graft}`; the selectors alone make $`\mathit{graft}`
injective. The book's implementation by nested lists
($`\mathit{graft}\ t\ x\ u = [t; x; u]`, $`\mathit{left}\ t = t\,0`, $`\mathit{root}\ t = t\,1`,
$`\mathit{right}\ t = t\,2`) mixes lists and items and is not expressible with the
homogeneous lists of {uses "list_packaging"}[]; the implementation here is the
inductive type of finite binary trees — the recursive data definition
$`\mathit{tree} = \mathit{emptree}, \mathit{graft}\ \mathit{tree}\ X\ \mathit{tree}` as a datatype (cf.
{uses "recursive_data_construction"}[]) — with the book's example tree
$`[[[\mathit{nil}]; 2; [[\mathit{nil}]; 5; [\mathit{nil}]]]; 3; [[\mathit{nil}]; 7; [\mathit{nil}]]]`. Uses
{uses "data_stack_theory"}[].
:::

:::definition "program_stack_theory" (parent := "theory_design_core") (lean := "LaPToP.TheoryDesign.ProgramStackTheory, LaPToP.TheoryDesign.refinesOfEq, LaPToP.TheoryDesign.ProgramStackTheory.push_pop_seq, LaPToP.TheoryDesign.ProgramStackTheory.balanced, LaPToP.TheoryDesign.ProgramStackTheory.ok_refines_balanced, LaPToP.TheoryDesign.ProgramStackTheory.ok_refines_push_push_pop_pop, LaPToP.TheoryDesign.ProgramStackTheory.refines_balanced_seq, LaPToP.TheoryDesign.ProgramStackTheory.top_push_push_push_pop_pop, LaPToP.TheoryDesign.ProgramStackTheory.top_push_balanced")
"Users and implementers of a data structure can freely see and change their
own variables, but they cannot freely see or change each other's variables.
... If we need only one stack ... we can obtain an economy of expression and
of execution by leaving it implicit." "The simplest version of program-stack
theory introduces three names: $`\mathit{push}` (a procedure with parameter of
type $`X`), $`\mathit{pop}` (a program), and $`\mathit{top}` (of type $`X`). ... The
following two axioms are sufficient: $`\mathit{top}' = x \Leftarrow \mathit{push}\ x`,
$`\mathit{ok} \Leftarrow \mathit{push}\ x.\ \mathit{pop}`." A program theory is a structure
over a state type with $`\mathit{push}` a parametrized specification, $`\mathit{pop}` a
specification and $`\mathit{top}` a state variable, the axioms being refinements.
"The second axiom says that a pop undoes a push. In fact, it says that any
natural number of pushes are undone by the same number of pops:
$`\mathit{ok} \Leftarrow \mathit{push}\ x.\ \mathit{pop} = \mathit{push}\ x.\ \mathit{ok}.\ \mathit{pop} \Leftarrow \mathit{push}\ x.\ \mathit{push}\ y.\ \mathit{pop}.\ \mathit{pop}`
... We can prove things like $`\mathit{top}' = x \Leftarrow \mathit{push}\ x.\ \mathit{push}\ y.\ \mathit{push}\ z.\ \mathit{pop}.\ \mathit{pop}`,
which say that when we push something onto the stack, we find it there later
at the appropriate time." Both are proved, the first for any number of
push–pop pairs. Uses {uses "simple_data_stack_theory"}[],
{uses "specification_notations"}[] and {uses "refinement_by_steps_parts_cases"}[].
:::

:::theorem "program_stack_implementation" (parent := "theory_design_core") (tags := "theory design, stacks, hehner-7.1.1") (effort := "small") (lean := "LaPToP.TheoryDesign.PS, LaPToP.TheoryDesign.ListProgramStack.push, LaPToP.TheoryDesign.ListProgramStack.pop, LaPToP.TheoryDesign.ListProgramStack.top, LaPToP.TheoryDesign.ListProgramStack.top_push, LaPToP.TheoryDesign.ListProgramStack.push_pop, LaPToP.TheoryDesign.ListProgramStack.theory")
"To implement program-stack theory, we introduce an implementer's variable
$`s : [*X]` and define $`\mathit{push} = \langle x : X \cdot s := s ;; [x] \rangle`,
$`\mathit{pop} = s := s\,[0;..\# s - 1]`, $`\mathit{top} = s\,(\# s - 1)`. And, of course, we must
show that these definitions satisfy the axioms. We'll do the first axiom
$`(\mathit{top}' = x \Leftarrow \mathit{push}\ x) = (s'(\# s' - 1) = x \Leftarrow s := s ;; [x]) = \top`,
and leave the other as Exercise 429." Both axioms are proved (the second by
$`(s ;; [x])[0;..\# s] = s`), so the list definitions form a
`ProgramStackTheory`. The implementer's state consists of the variable $`s`
alone; user variables, which the stack operations leave unchanged, would be
added as a product (cf. {uses "variable_suspension"}[]). Uses
{uses "program_stack_theory"}[] and {uses "list_axioms"}[].
:::

:::definition "fancy_and_weak_program_stack" (parent := "theory_design_core") (lean := "LaPToP.TheoryDesign.FancyProgramStackTheory, LaPToP.TheoryDesign.FancyProgramStackTheory.top_push_not_isempty, LaPToP.TheoryDesign.ListProgramStack.mkempty, LaPToP.TheoryDesign.ListProgramStack.isempty, LaPToP.TheoryDesign.ListProgramStack.fancyTheory, LaPToP.TheoryDesign.WeakProgramStackTheory, LaPToP.TheoryDesign.WeakProgramStackTheory.balanced, LaPToP.TheoryDesign.WeakProgramStackTheory.balance_refines_balanced, LaPToP.TheoryDesign.WeakProgramStackTheory.top_balanced, LaPToP.TheoryDesign.ProgramStackTheory.toWeak")
"A slightly fancier program-stack theory introduces two more names:
$`\mathit{mkempty}` (a program to make the stack empty) and $`\mathit{isempty}` (a binary
variable to say whether the stack is empty). Letting $`x : X`, the axioms are
$`\mathit{top}' = x \land \neg\mathit{isempty}' \Leftarrow \mathit{push}\ x`, $`\mathit{ok} \Leftarrow \mathit{push}\ x.\ \mathit{pop}`,
$`\mathit{isempty}' \Leftarrow \mathit{mkempty}`" — the list implementation satisfies them too.
"The program-stack theory we presented first can be weakened and still retain
its stack character. We must keep the axiom $`\mathit{top}' = x \Leftarrow \mathit{push}\ x`
but we do not need the composition $`\mathit{push}\ x.\ \mathit{pop}` to leave all variables
unchanged. We do require that any natural number of pushes followed by the same
number of pops gives back the original top. The axioms are
$`\mathit{top}' = \mathit{top} \Leftarrow \mathit{balance}`, $`\mathit{balance} \Leftarrow \mathit{ok}`,
$`\mathit{balance} \Leftarrow \mathit{push}\ x.\ \mathit{balance}.\ \mathit{pop}`, where $`\mathit{balance}` is a
specification that helps in writing the axioms, but is not an addition to the
theory, and does not need to be implemented." Proved: $`\mathit{top}' = \mathit{top}` after
any number of pushes followed by the same number of pops, and that the strong
theory implies the weak one (with $`\mathit{balance} := \mathit{ok}`). The book's remark
that the weak theory "allows an implementation in which popping ... marks the
last item as garbage" is not formalized. The axiom
$`\mathbf{screen}!\ \text{“error”} \Leftarrow \mathit{mkempty}.\ \mathit{pop}` mentioned for robustness
is a Chapter 9 notation, cf. {uses "assertions"}[]. Uses
{uses "program_stack_theory"}[] and {uses "program_stack_implementation"}[].
:::
