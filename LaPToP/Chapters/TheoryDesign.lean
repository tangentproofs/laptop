import Verso
import VersoManual
import VersoBlueprint
import LaPToP.TheoryDesign.Stack
import LaPToP.TheoryDesign.SimpleStack
import LaPToP.TheoryDesign.Queue
import LaPToP.TheoryDesign.Tree
import LaPToP.TheoryDesign.ProgramStack
import LaPToP.TheoryDesign.ProgramQueue
import LaPToP.TheoryDesign.DataTransformation
import LaPToP.TheoryDesign.SecuritySwitch
import LaPToP.TheoryDesign.TakeANumber
import LaPToP.TheoryDesign.LimitedQueue
import LaPToP.TheoryDesign.Parsing
import LaPToP.TheoryDesign.Incompleteness

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Theory Design and Implementation" =>

:::group "theory_design_core"
Hehner's Chapter 7: "the stack, the queue, and the tree ... are presented here
as case studies in theory design and implementation", a theory being "a
contract between two parties, an implementer and a user". The data theories
of Section 7.0 are formalized in `LaPToP.TheoryDesign.Stack`, `SimpleStack`,
`Queue` and `Tree`; program-stack theory (Sections 7.1.0–7.1.3) in
`LaPToP.TheoryDesign.ProgramStack` and program-queue and program-tree theory
(Sections 7.1.4–7.1.5) in `LaPToP.TheoryDesign.ProgramQueue`; data
transformation (Section 7.2) in `LaPToP.TheoryDesign.DataTransformation`, with
its examples in `SecuritySwitch` (Section 7.2.0), `TakeANumber` (7.2.1),
`Parsing` (7.2.2) and `LimitedQueue` (7.2.3), and its incompleteness
(Section 7.2.4, Exercise 465) in `LaPToP.TheoryDesign.Incompleteness`.
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

:::definition "program_queue_theory" (parent := "theory_design_core") (lean := "LaPToP.TheoryDesign.ProgramQueueTheory, LaPToP.TheoryDesign.ProgramQueueTheory.not_isemptyq_join, LaPToP.TheoryDesign.ProgramQueueTheory.front_mkemptyq_join, LaPToP.TheoryDesign.ProgramQueueTheory.join_join_leave, LaPToP.TheoryDesign.ProgramQueueTheory.join_join_leave_empty, LaPToP.TheoryDesign.ProgramQueueTheory.front_join_join_leave_empty, LaPToP.TheoryDesign.PQ, LaPToP.TheoryDesign.ListProgramQueue.mkemptyq, LaPToP.TheoryDesign.ListProgramQueue.isemptyq, LaPToP.TheoryDesign.ListProgramQueue.join, LaPToP.TheoryDesign.ListProgramQueue.leave, LaPToP.TheoryDesign.ListProgramQueue.front, LaPToP.TheoryDesign.ListProgramQueue.isemptyq_iff, LaPToP.TheoryDesign.ListProgramQueue.isemptyq_mkemptyq, LaPToP.TheoryDesign.ListProgramQueue.join_empty, LaPToP.TheoryDesign.ListProgramQueue.join_nonempty, LaPToP.TheoryDesign.ListProgramQueue.join_leave_empty, LaPToP.TheoryDesign.ListProgramQueue.join_leave_nonempty, LaPToP.TheoryDesign.ListProgramQueue.theory")
"Program-queue theory introduces five names: $`\mathit{mkemptyq}` (a program to
make the queue empty), $`\mathit{isemptyq}` (a binary variable to say whether the
queue is empty), $`\mathit{join}` (a procedure with parameter of type $`X`),
$`\mathit{leave}` (a program), and $`\mathit{front}` (of type $`X`). The axioms are
$`\mathit{isemptyq}' \Leftarrow \mathit{mkemptyq}`,
$`\mathit{isemptyq} \Rightarrow \mathit{front}' = x \land \lnot\mathit{isemptyq}' \Leftarrow \mathit{join}\ x`,
$`\lnot\mathit{isemptyq} \Rightarrow \mathit{front}' = \mathit{front} \land \lnot\mathit{isemptyq}' \Leftarrow \mathit{join}\ x`,
$`\mathit{isemptyq} \Rightarrow (\mathit{join}\ x.\ \mathit{leave} = \mathit{mkemptyq})`,
$`\lnot\mathit{isemptyq} \Rightarrow (\mathit{join}\ x.\ \mathit{leave} = \mathit{leave}.\ \mathit{join}\ x)`."
As for {uses "program_stack_theory"}[], the theory is a structure over a state
type; the first three axioms are refinements, and the two axioms of the form
$`b \Rightarrow (P = Q)` are stated pointwise, as $`\forall s, s' \cdot b\ s \Rightarrow (P\ s\ s' \Leftrightarrow Q\ s\ s')`.
Derived from the axioms alone: $`\lnot\mathit{isemptyq}' \Leftarrow \mathit{join}\ x`,
$`\mathit{front}' = x \land \lnot\mathit{isemptyq}' \Leftarrow \mathit{mkemptyq}.\ \mathit{join}\ x`, and first-in-first-out:
$`\mathit{join}\ x.\ \mathit{join}\ y.\ \mathit{leave} = \mathit{join}\ x.\ \mathit{leave}.\ \mathit{join}\ y`, which from an empty
queue is $`\mathit{mkemptyq}.\ \mathit{join}\ y`, after which the front is $`y`. The book gives
no implementation in this section; the list implementation suggested by
{uses "data_queue_theory"}[] — $`q : [{*}X]`, $`\mathit{mkemptyq} = q := [\mathit{nil}]`,
$`\mathit{isemptyq} = (q = [\mathit{nil}])`, $`\mathit{join}\ x = q := q ;; [x]`,
$`\mathit{leave} = q := q[1;..\# q]`, $`\mathit{front} = q\,0` — is proved to satisfy all five
axioms, using {uses "list_axioms"}[].
:::

:::definition "program_tree_theory" (parent := "theory_design_core") (lean := "LaPToP.TheoryDesign.Dir, LaPToP.TheoryDesign.ProgramTreeTheory, LaPToP.TheoryDesign.ProgramTreeTheory.go_assignNode_go, LaPToP.TheoryDesign.ProgramTreeTheory.go_work_work_go")
"Imagine a binary tree that is infinite in all directions; there are no leaves
and no root. You are standing at one node in the tree facing one of the three
directions up (toward the parent of this node), left (toward the left child of
this node), or right (toward the right child of this node). Variable
$`\mathit{node}` (of type $`X`) tells the value of the item where you are, and it can
be assigned a new value. Variable $`\mathit{aim}` tells what direction you are
facing, and it can be assigned a new direction. Program $`\mathit{go}` moves you to
the next node in the direction you are facing, and turns you facing back the
way you came. ... The axioms use an auxiliary specification that helps in
writing the axioms, but is not an addition to the theory, and does not need to
be implemented: $`\mathit{work}` means “Do anything, wander around changing the
values of nodes if you like, but do not go from this node (your location at
the start of $`\mathit{work}`) in this direction (the value of variable $`\mathit{aim}` at
the start of $`\mathit{work}`). End where you started, facing the way you were
facing at the start.” Here are the axioms.
$`(\mathit{aim}' = \mathit{up}) = (\mathit{aim} \neq \mathit{up}) \Leftarrow \mathit{go}`,
$`\mathit{node}' = \mathit{node} \land \mathit{aim}' = \mathit{aim} \Leftarrow \mathit{go}.\ \mathit{work}.\ \mathit{go}`,
$`\mathit{work} \Leftarrow \mathit{node} := x`,
$`\mathit{work} \Leftarrow a = \mathit{aim} \neq b \land (\mathit{aim} := b.\ \mathit{go}.\ \mathit{work}.\ \mathit{go}.\ \mathit{aim} := a)`,
$`\mathit{work} \Leftarrow \mathit{work}.\ \mathit{work}`." Only the structure of this first definition is
given (with the assignments to $`\mathit{node}` and $`\mathit{aim}` as fields), together
with the derived law $`\mathit{node}' = \mathit{node} \land \mathit{aim}' = \mathit{aim} \Leftarrow \mathit{go}.\ \mathit{node} := x.\ \mathit{go}`.
No implementation is given, and the book's second definition by implementer's
variables $`T`, $`p` with $`\mathit{node} = T@(p; 1)` is not formalized. Uses
{uses "program_queue_theory"}[] and {uses "data_tree_theory"}[].
:::


:::definition "data_transformation" (parent := "theory_design_core") (lean := "LaPToP.TheoryDesign.Spec.IsTransformer, LaPToP.TheoryDesign.Spec.transform, LaPToP.TheoryDesign.Spec.transform_spec, LaPToP.TheoryDesign.Spec.transform_mono, LaPToP.TheoryDesign.Spec.implementable_transform, LaPToP.TheoryDesign.Spec.IsTransformerU, LaPToP.TheoryDesign.Spec.transformU, LaPToP.TheoryDesign.Spec.transform_eq_transformU, LaPToP.TheoryDesign.Spec.isTransformer_iff_isTransformerU, LaPToP.TheoryDesign.Spec.transformU_mono, LaPToP.TheoryDesign.Caveat.S, LaPToP.TheoryDesign.Caveat.implementable_S, LaPToP.TheoryDesign.Caveat.not_implementable_transform")
"Since a theory user has no access to the implementer's variables except
through the theory, an implementer is free to change them in any way that
provides the same theory to the user. ... We can replace the old implementer's
variables by new implementer's variables using a data transformer, which is a
binary expression $`D` relating $`\mathit{old}` and $`\mathit{new}` such that
$`\forall\mathit{new}\cdot\exists\mathit{old}\cdot D`. Let $`D'` be the same as $`D` but with
primes on all the variables. Then each specification $`S` in the theory is
transformed to $`\forall\mathit{old}\cdot D \Rightarrow \exists\mathit{old}'\cdot D' \land S`. ... This
says that whatever related initial state $`\mathit{old}` the user was imagining,
there is a related final state $`\mathit{old}'` for the user to imagine as the
result of $`S`, and so the fiction is maintained." States are products of the
user's variables with the old or the new implementer's variables;
`Spec.transform D S` is literally the transformed specification. Proved:
transformation is monotonic with respect to refinement, and it preserves
implementability when the transformer is a bijective correspondence between
old and new states. Two honest caveats: totality
$`\forall\mathit{new}\cdot\exists\mathit{old}\cdot D` alone does *not* preserve implementability
— for the transformer $`w = \mathit{even}\ v` of Exercise 454(a) the implementable
$`\mathbf{if}\ v = 0\ \mathbf{then}\ v' = 0\ \mathbf{else}\ v' = 1` transforms to an unimplementable
specification, since from $`w = \top` the user may imagine $`v = 0` or $`v = 2` and
no single $`w'` serves both — so the implementability of each transformed
operation is to be checked, as the book does in its examples. Since "$`S`
talks about its nonlocal variables $`\mathit{old}` and $`\mathit{old}'` (and the user's
variables)", a transformer may mention the user's variables as well;
`Spec.transformU` is that general form (with $`D'` priming the user's variables
too) and `Spec.transform` its special case. Uses
{uses "variable_declaration"}[], {uses "specification_notations"}[] and
{uses "quantifier_forall_exists"}[].
:::

:::theorem "data_transformation_examples" (parent := "theory_design_core") (tags := "theory design, transformation, hehner-7.2") (effort := "small") (lean := "LaPToP.TheoryDesign.Exercise454.D, LaPToP.TheoryDesign.Exercise454.isTransformer, LaPToP.TheoryDesign.Exercise454.decide_even_succ, LaPToP.TheoryDesign.Exercise454.zero, LaPToP.TheoryDesign.Exercise454.increase, LaPToP.TheoryDesign.Exercise454.inquire, LaPToP.TheoryDesign.Exercise454.transform_zero, LaPToP.TheoryDesign.Exercise454.transform_increase, LaPToP.TheoryDesign.Exercise454.transform_inquire, LaPToP.TheoryDesign.Exercise455.D, LaPToP.TheoryDesign.Exercise455.isTransformer, LaPToP.TheoryDesign.Exercise455.set, LaPToP.TheoryDesign.Exercise455.flip, LaPToP.TheoryDesign.Exercise455.ask, LaPToP.TheoryDesign.Exercise455.transform_set, LaPToP.TheoryDesign.Exercise455.set_refines, LaPToP.TheoryDesign.Exercise455.transform_flip, LaPToP.TheoryDesign.Exercise455.flip_refines, LaPToP.TheoryDesign.Exercise455.transform_ask, LaPToP.TheoryDesign.Exercise455.ask_refines")
Exercise 454(a): "the user's variable is $`u : \mathit{bin}` and the implementer's
variable is $`v : \mathit{nat}`. The theory provides three operations,
$`\mathit{zero} = v := 0`, $`\mathit{increase} = v := v + 1`, $`\mathit{inquire} = u := \mathit{even}\ v`.
Since the only question asked of the implementer's variable is whether it is
even, we decide to replace it by a new implementer's variable $`w : \mathit{bin}`
according to the data transformer $`w = \mathit{even}\ v`." The book's calculations
(One-Point and change-of-variable laws) give $`\mathit{zero} = w := \top`,
$`\mathit{increase} = w := \neg w`, $`\mathit{inquire} = u := w`; all three equalities are
proved. Exercise 455(a), "just to show that it works both ways": $`u : \mathit{bin}`,
$`v : \mathit{bin}`, $`\mathit{set} = v := \top`, $`\mathit{flip} = v := \neg v`, $`\mathit{ask} = u := v`,
transformer $`v = \mathit{even}\ w` with new $`w : \mathit{nat}`; the operations become
$`\mathit{even}\ w' \land u' = u \Leftarrow w := 0`,
$`\mathit{even}\ w' = \neg\mathit{even}\ w \land u' = u \Leftarrow w := w + 1`,
$`\mathit{even}\ w' = \mathit{even}\ w = u' \Leftarrow u := \mathit{even}\ w`; the three transformed
specifications are computed as equalities and the three refinements proved.
Uses {uses "data_transformation"}[] and {uses "substitution_law"}[].
:::

:::theorem "security_switch" (parent := "theory_design_core") (tags := "theory design, transformation, hehner-7.2.0") (effort := "small") (lean := "LaPToP.TheoryDesign.SecuritySwitch.U, LaPToP.TheoryDesign.SecuritySwitch.O, LaPToP.TheoryDesign.SecuritySwitch.D, LaPToP.TheoryDesign.SecuritySwitch.isTransformer, LaPToP.TheoryDesign.SecuritySwitch.switchStep, LaPToP.TheoryDesign.SecuritySwitch.flipA, LaPToP.TheoryDesign.SecuritySwitch.flipB, LaPToP.TheoryDesign.SecuritySwitch.opA, LaPToP.TheoryDesign.SecuritySwitch.opB, LaPToP.TheoryDesign.SecuritySwitch.switchStepT, LaPToP.TheoryDesign.SecuritySwitch.transformU_switchStep, LaPToP.TheoryDesign.SecuritySwitch.transformU_opA, LaPToP.TheoryDesign.SecuritySwitch.transformU_opB, LaPToP.TheoryDesign.SecuritySwitch.majority, LaPToP.TheoryDesign.SecuritySwitch.xor_eq_majority, LaPToP.TheoryDesign.SecuritySwitch.xor_circuit")
"Exercise 460 is to design a security switch. It has three binary user's
variables $`a`, $`b`, and $`c`. The users assign values to $`a` and $`b` as input
to the switch. The switch's output is assigned to $`c`. The output changes when
both inputs have changed. More precisely, the output changes when both inputs
differ from what they were the previous time the output changed. ... We can
implement the switch with two binary implementer's variables: $`A` records the
state of input $`a` at the last previous output change, $`B` records the state
of input $`b` at the last previous output change. There are two operations:
$`a := \lnot a.\ \mathbf{if}\ a \neq A \land b \neq B\ \mathbf{then}\ c := \lnot c.\ A := a.\ B := b\ \mathbf{else}\ \mathit{ok}`
and the same with $`b := \lnot b`. ... This implementation is a direct
formalization of the problem, but it can be simplified by data transformation.
We replace implementer's variables $`A` and $`B` by nothing according to the
transformer $`A = B = c`. To check that this is a transformer, we check
$`\exists A, B \cdot A = B = c \Leftarrow \top`, generalization, using $`c` for both $`A`
and $`B`. ... The transformation does not affect the assignments to $`a` and
$`b`, so we have only one transformation to make.
$`\forall A, B \cdot A = B = c \Rightarrow \exists A', B' \cdot A' = B' = c' \land \mathbf{if}\ a \neq A \land b \neq B\ \mathbf{then}\ c := \lnot c.\ A := a.\ B := b\ \mathbf{else}\ \mathit{ok}`
$`= \mathbf{if}\ a \neq c \land b \neq c\ \mathbf{then}\ c := \lnot c\ \mathbf{else}\ \mathit{ok}`
$`= c := (a \neq c \land b \neq c) \neq c`.
Output $`c` becomes the majority value of $`a`, $`b`, and $`c`. (As a circuit,
that's three “exclusive or” gates and one “and” gate.)" The transformer
mentions the user's variable $`c`, so it is a transformer in the general form
`Spec.transformU` of {uses "data_transformation"}[], whose $`D'` primes the
user's variables too (as the book's $`A' = B' = c'` does). The book's chain of
equalities is proved as one equation, the transformed operations are
$`a := \lnot a.\ c := (a \neq c \land b \neq c) \neq c` and likewise for $`b`, and the
majority and circuit remarks are checked on the eight cases. Uses
{uses "binary_laws_basic"}[] and {uses "specification_laws"}[].
:::

:::theorem "take_a_number" (parent := "theory_design_core") (tags := "theory design, transformation, hehner-7.2.1") (effort := "medium") (lean := "LaPToP.TheoryDesign.TakeANumber.start, LaPToP.TheoryDesign.TakeANumber.take, LaPToP.TheoryDesign.TakeANumber.give, LaPToP.TheoryDesign.TakeANumber.Dbelow, LaPToP.TheoryDesign.TakeANumber.isTransformer_Dbelow, LaPToP.TheoryDesign.TakeANumber.D, LaPToP.TheoryDesign.TakeANumber.transform_start, LaPToP.TheoryDesign.TakeANumber.transform_take, LaPToP.TheoryDesign.TakeANumber.transform_give, LaPToP.TheoryDesign.TakeANumber.giveBook, LaPToP.TheoryDesign.TakeANumber.transform_give_refines_book, LaPToP.TheoryDesign.TakeANumber.transform_give_ne_book, LaPToP.TheoryDesign.TakeANumber.start_refines, LaPToP.TheoryDesign.TakeANumber.takeProg, LaPToP.TheoryDesign.TakeANumber.take_refines, LaPToP.TheoryDesign.TakeANumber.give_refines, LaPToP.TheoryDesign.TakeANumber.D₂, LaPToP.TheoryDesign.TakeANumber.takeProg₂, LaPToP.TheoryDesign.TakeANumber.take_refines₂, LaPToP.TheoryDesign.TakeANumber.Deo, LaPToP.TheoryDesign.TakeANumber.isTransformer_Deo, LaPToP.TheoryDesign.TakeANumber.takeProgEO, LaPToP.TheoryDesign.TakeANumber.take_refinesEO")
"Exercise 462 (take a number): Maintain a list of natural numbers standing for
those that are “in use”. The three operations are: make the list empty (for
initialization); assign to variable $`n` a number that is not in use, and add
this number to the list (now it is in use); given a number $`n` that is in use,
remove it from the list. The user's variable is $`n : \mathit{nat}`. ... We
therefore use a set variable $`s \subseteq \{\mathit{nat}\}` as our implementer's
variable. The three operations are
$`\mathit{start} = s' = \{\mathit{null}\} \land n' = n`,
$`\mathit{take} = \lnot n' \in s \land s' = s \cup \{n'\}`,
$`\mathit{give} = n \in s \Rightarrow \lnot n' \in s' \land s' \cup \{n\} = s \land n' = n`.
Here is a data transformation that replaces set $`s` with natural $`m` according
to the transformer $`s \subseteq \{0,..m\}`. Instead of maintaining the exact set
of numbers that are in use, we will maintain a possibly larger set. We will
still never give out a number that is in use." The book transforms
$`\mathit{start}` to $`n' = n \Leftarrow \mathit{ok}` ("it does not matter what $`m'` is; we may
as well leave it alone"), $`\mathit{take}` to $`m \le n' < m' \Leftarrow n := m.\ m := m+1`,
and $`\mathit{give}` to $`(n+1 = m \Rightarrow n \le m') \land (n+1 < m \Rightarrow m \le m') \land n' = n \Leftarrow \mathit{ok}`,
each after "several omitted steps". "Thanks to the data transformation, we have
an extremely efficient solution to the problem. One might argue that we have
not solved the problem because we do not maintain a list of numbers that are
“in use”. But who can tell?" The omitted steps are filled in as equalities
with {uses "data_transformation"}[]: $`\mathit{start}` and $`\mathit{take}` transform
exactly as the book says (the latter for any transformer $`s \subseteq \{0,..f\,\mathit{new}\}`).
Deviation, recorded: the transformed $`\mathit{give}` is
$`n < m \Rightarrow (n+1 = m \Rightarrow n \le m') \land (n+1 < m \Rightarrow m \le m') \land n' = n` — when
$`m \le n` no imagined set $`s \subseteq \{0,..m\}` contains $`n`, so the specification is
$`\top`; the book's line strengthens it to $`n' = n`, so it is a refinement of the
transformed specification, not equal to it (a counterexample is given), and
the conclusion $`\Leftarrow \mathit{ok}` holds for both. For two machines, the
transformer $`s \subseteq \{0,..i \uparrow j\}` gives
$`i \uparrow j \le n' < i' \uparrow j' \Leftarrow n := i \uparrow j.\ \mathbf{if}\ i \ge j\ \mathbf{then}\ i := i+1\ \mathbf{else}\ j := j+1`
("this data transformation does not provide the independent operation of two
machines"), and for the even/odd transformer
$`\forall k : {\sim}s \cdot \mathit{even}\ k \land k < i \lor \mathit{odd}\ k \land k < j` with
$`i : 2 \times \mathit{nat}`, $`j : 2 \times \mathit{nat} + 1`, the program
$`(n := i.\ i := i+2) \lor (n := j.\ j := j+2)` is proved to refine the transformed
$`\mathit{take}` under that typing (stated as hypotheses $`\mathit{even}\ i`, $`\mathit{odd}\ j`):
"we can take a number from either machine without disturbing the other. The
price of the distribution is that we have lost all fairness between the two
machines." Uses {uses "set_packaging"}[], {uses "bunch_interval"}[] and {uses "specification_laws"}[].
:::

:::theorem "parsing" (parent := "theory_design_core") (tags := "theory design, transformation, parsing, hehner-7.2.2") (effort := "large") (lean := "LaPToP.TheoryDesign.Parsing.Tok, LaPToP.TheoryDesign.Parsing.E, LaPToP.TheoryDesign.Parsing.E.head, LaPToP.TheoryDesign.Parsing.E_x_cons_iff, LaPToP.TheoryDesign.Parsing.E_if_cons_iff, LaPToP.TheoryDesign.Parsing.Cands, LaPToP.TheoryDesign.Parsing.cands_nil_iff, LaPToP.TheoryDesign.Parsing.cands_x_cons_iff, LaPToP.TheoryDesign.Parsing.cands_eog_cons_iff, LaPToP.TheoryDesign.Parsing.cands_tok_cons_iff, LaPToP.TheoryDesign.Parsing.cands_x_x, LaPToP.TheoryDesign.Parsing.cands_x_if, LaPToP.TheoryDesign.Parsing.cands_x_head, LaPToP.TheoryDesign.Parsing.cands_eog_eos, LaPToP.TheoryDesign.Parsing.not_cands_cons_nil, LaPToP.TheoryDesign.Parsing.SentC, LaPToP.TheoryDesign.Parsing.SentC.tail, LaPToP.TheoryDesign.Parsing.SentC.eog_cons, LaPToP.TheoryDesign.Parsing.SentC.prepend, LaPToP.TheoryDesign.Parsing.SentS, LaPToP.TheoryDesign.Parsing.SentS.drop_succ_eq_nil, LaPToP.TheoryDesign.Parsing.SentS.ne_eog, LaPToP.TheoryDesign.Parsing.PS, LaPToP.TheoryDesign.Parsing.assignN, LaPToP.TheoryDesign.Parsing.assignC, LaPToP.TheoryDesign.Parsing.assignQ, LaPToP.TheoryDesign.Parsing.assignN_seq, LaPToP.TheoryDesign.Parsing.assignC_seq, LaPToP.TheoryDesign.Parsing.R, LaPToP.TheoryDesign.Parsing.expansion, LaPToP.TheoryDesign.Parsing.Rprog, LaPToP.TheoryDesign.Parsing.R_refines, LaPToP.TheoryDesign.Parsing.cands_init_iff, LaPToP.TheoryDesign.Parsing.parse_refines, LaPToP.TheoryDesign.Parsing.parse_program_refines")
"Exercise 451 (parsing): Define $`E` as a bunch of strings of lists of characters
satisfying $`E = [\text{“x”}], [\text{“if”}]; E; [\text{“then”}]; E; [\text{“else”}]; E; [\text{“fi”}]`.
Given a string of lists of characters, write a program to determine if the
string is in the bunch $`E`. For the problem to be nontrivial, we assume that
recursive data definition and bunch inclusion are not implemented. ... Let the
given string be $`s` (a constant). ... we introduce natural variable $`n`,
increasing from $`0` to at most $`\leftrightarrow s`, indicating how much of $`s` we have
parsed. Let $`A` be a variable whose value is a bunch of strings of lists of
characters. Bunch $`A` will consist of all strings in $`E` that might possibly be
$`s` according to what we have seen of $`s`. We can express the result as the
final value of binary variable $`q`. ... We assume that $`s` ends with the
sentinel $`[\text{“eos”}]` (end of string) ... and when we initialize variable
$`A`, we will add the sentinel $`[\text{“eog”}]` (end of grammar) to the end of
every string ... $`q' = (s_{0;..\leftrightarrow s - 1} : E) \Leftarrow A := E; [\text{“eog”}].\ n := 0.\ P`
... $`P \Leftarrow \mathbf{if}\ s_n : A_n\ \mathbf{then}\ A := (\S a : A \cdot a_n = s_n).\ n := n+1.\ P\ \mathbf{else}\ q := [\text{“eog”}] : A_n \land s_n = [\text{“eos”}]`
... We omit the proofs of these refinements in order to pursue our current
topic, data transformation. We now replace variable $`A` with variable $`b`
whose value is a single string of lists of characters. ... The data
transformer is, informally, $`A = (b` with all occurrences of item
$`[\text{“E”}]` replaced by bunch $`E)`. ... We can make a minor improvement by
changing the representation of $`E` from $`[\text{“E”}]` to $`[\text{“x”}]` ...
Our next improvement is to notice that we don't need the initial portion of
$`b`, which is identical to the initial portion of $`s`. So we transform again,
replacing $`b` with $`c` using the transformer $`b = s_{0;..n}; c`. Let $`R` be the
result of transforming $`Q`.
$`q' = (s_{0;..\leftrightarrow s - 1} : E) \Leftarrow c := [\text{“x”}]; [\text{“eog”}].\ n := 0.\ R`;
$`R \Leftarrow \mathbf{if}\ s_n = c_0\ \mathbf{then}\ c := c_{1;..\leftrightarrow c}.\ n := n+1.\ R`
$`\mathbf{else\ if}\ c_0 = [\text{“x”}] \land s_n = [\text{“if”}]\ \mathbf{then}\ c := [\text{“x”}]; [\text{“then”}]; [\text{“x”}]; [\text{“else”}]; [\text{“x”}]; [\text{“fi”}]; c_{1;..\leftrightarrow c}.\ n := n+1.\ R`
$`\mathbf{else}\ q := c_0 = [\text{“eog”}] \land s_n = [\text{“eos”}]`."
The items are tokens and $`E` is defined inductively (the least solution, as in
{uses "recursive_data_construction"}[]). The specification $`R` — the result of
the two transformations, which the book computes informally — is stated
directly: $`q'` says whether the rest of the input $`s_{n;..\leftrightarrow s}` is one of
the strings represented by $`c`, "$`c` with all occurrences of item $`[\text{“x”}]`
replaced by bunch $`E`" and $`[\text{“eog”}]` standing for $`[\text{“eos”}]`. The
book's final program is proved to refine $`R` (the recursive call as a
specification, {uses "recursive_program_zap"}[]), and
$`q' = (s_{0;..\leftrightarrow s - 1} : E)` is refined by
$`c := [\text{“x”}]; [\text{“eog”}].\ n := 0.\ R` and hence by the whole program, under the
sentinel assumptions: $`[\text{“eos”}]` occurs in $`s` only at the end,
$`[\text{“eog”}]` does not occur in $`s`, and (an antecedent of $`R`) $`[\text{“eog”}]`
occurs in $`c` only at the end. The heart of the proof is what the first item of
the input decides: an $`E`-string begins with $`[\text{“x”}]` (and is then
$`[\text{“x”}]`) or with $`[\text{“if”}]` (and is then
$`[\text{“if”}]; a; [\text{“then”}]; b; [\text{“else”}]; c; [\text{“fi”}]`). Not formalized: the
bunch-valued variable $`A`, the intermediate program with $`b`, and the two
transformers, which the book gives informally and whose refinements it omits;
what is proved is that the final program meets the original specification,
which is what the transformations are for. The printed line
$`c := \ldots; [\text{“fi”}]\ c` is read as $`\ldots; [\text{“fi”}]; c_{1;..\leftrightarrow c}` (the
$`[\text{“x”}]` at $`c_0` is what is expanded). Uses {uses "data_transformation"}[],
{uses "string_axioms_indexing"}[] and {uses "specification_laws"}[].
:::

:::theorem "limited_queue" (parent := "theory_design_core") (tags := "theory design, transformation, queues, hehner-7.2.3") (effort := "medium") (lean := "LaPToP.TheoryDesign.LimitedQueue.U, LaPToP.TheoryDesign.LimitedQueue.O, LaPToP.TheoryDesign.LimitedQueue.N₀, LaPToP.TheoryDesign.LimitedQueue.N, LaPToP.TheoryDesign.LimitedQueue.Inside, LaPToP.TheoryDesign.LimitedQueue.Outside, LaPToP.TheoryDesign.LimitedQueue.D₀, LaPToP.TheoryDesign.LimitedQueue.D, LaPToP.TheoryDesign.LimitedQueue.isTransformer_D₀, LaPToP.TheoryDesign.LimitedQueue.isTransformer_D, LaPToP.TheoryDesign.LimitedQueue.mkemptyq, LaPToP.TheoryDesign.LimitedQueue.assignC, LaPToP.TheoryDesign.LimitedQueue.assignC_isemptyq, LaPToP.TheoryDesign.LimitedQueue.assignC_isfullq, LaPToP.TheoryDesign.LimitedQueue.not_implementable_isemptyq₀, LaPToP.TheoryDesign.LimitedQueue.mkemptyqT, LaPToP.TheoryDesign.LimitedQueue.isemptyqT, LaPToP.TheoryDesign.LimitedQueue.isfullqT, LaPToP.TheoryDesign.LimitedQueue.mkemptyq_refines, LaPToP.TheoryDesign.LimitedQueue.isemptyq_refines, LaPToP.TheoryDesign.LimitedQueue.isfullq_refines, LaPToP.TheoryDesign.LimitedQueue.implementable_isemptyqT, LaPToP.TheoryDesign.LimitedQueue.join, LaPToP.TheoryDesign.LimitedQueue.leave, LaPToP.TheoryDesign.LimitedQueue.assignX_front, LaPToP.TheoryDesign.LimitedQueue.joinT, LaPToP.TheoryDesign.LimitedQueue.leaveT, LaPToP.TheoryDesign.LimitedQueue.frontT, LaPToP.TheoryDesign.LimitedQueue.notFullT, LaPToP.TheoryDesign.LimitedQueue.notEmptyT, LaPToP.TheoryDesign.LimitedQueue.guardT, LaPToP.TheoryDesign.LimitedQueue.outside_index_lt, LaPToP.TheoryDesign.LimitedQueue.join_refines, LaPToP.TheoryDesign.LimitedQueue.leave_refines, LaPToP.TheoryDesign.LimitedQueue.front_refines")
"Exercise 464 transforms a limited queue to achieve a time bound that is not
met by the original implementation. A limited queue is a queue with a limited
number of places for items. Let the limit be $`n : \mathit{nat}+1`, and let
$`Q : [n{*}X]` and $`p : 0,..n+1` be implementer's variables. Then the original
implementation is as follows. $`\mathit{mkemptyq} = p := 0`, $`\mathit{isemptyq} = p = 0`,
$`\mathit{isfullq} = p = n`, $`\mathit{join}\ x = Q\,p := x.\ p := p+1`,
$`\mathit{leave} = \mathbf{for}\ i := 1;..p\ \mathbf{do}\ Q\,(i-1) := Q\,i\ \mathbf{od}.\ p := p-1`,
$`\mathit{front} = Q\,0`. ... Unfortunately, removing the front item from the queue
takes time $`p-1` to shift all remaining items down one index. We want to
transform the queue so that all operations are instant. Variables $`Q` and $`p`
will be replaced by $`R : [n{*}X]` and $`f, b : 0,..n+1` with $`f` and $`b` indicating
the current front and back. ... Here is the data transformer $`D`.
$`Q[0;..p] = R[f;..b] \lor Q[0;..p] = R[(f;..n); (0;..b)]`. The conjuncts
$`0 \le p \le n \land 0 \le f \le b \le n \land p = b - f` are implicit in the left disjunct, and
the conjuncts $`0 \le p \le n \land 0 \le f \le n \land 0 \le b \le n \land p = n - f + b` are implicit
in the right disjunct. Now we transform. First $`\mathit{mkemptyq}`. ...
$`\Leftarrow f := 0.\ b := 0`. Next we transform $`\mathit{isemptyq}`. ... we suppose $`c` is a
binary user's variable, and transform $`c := \mathit{isemptyq}`. ... Suspiciously, we
have $`\lnot c'` in every case. That's because $`f = b` is missing! So the transformed
operation is unimplementable. That's the transformer's way of telling us that
the new variables do not hold enough information to answer whether the queue
is empty. The problem occurs when $`f = b` because that could be either an empty
queue or a full queue. A solution is to add a new variable $`m : \mathit{bin}` to say
whether we have the “inside” mode or “outside” mode. We revise the transformer
$`D` as follows: $`m \land Q[0;..p] = R[f;..b] \lor \lnot m \land Q[0;..p] = R[(f;..n); (0;..b)]`.
Now we have to retransform $`\mathit{mkemptyq}`. ... $`\Leftarrow m := \top.\ f := 0.\ b := 0`. Next we
retransform $`c := \mathit{isemptyq}`. ... $`= c := \mathbf{if}\ m\ \mathbf{then}\ f = b\ \mathbf{else}\ b = 0 \land f = n`.
... Next we transform $`c := \mathit{isfullq}`. ... $`\Leftarrow c := \mathbf{if}\ m\ \mathbf{then}\ f = 0 \land b = n\ \mathbf{else}\ f = b`.
Next we transform $`\mathit{join}\ x`. Before this operation, there should be a
check that the queue is not full. ...
$`\Leftarrow \mathbf{if}\ b < n\ \mathbf{then}\ R\,b := x.\ b := b+1\ \mathbf{else}\ R\,0 := x.\ b := 1.\ m := \bot`.
Next we transform $`\mathit{leave}`. Before this operation, there should be a check
that the queue is not empty. ...
$`\Leftarrow \mathbf{if}\ f < n\ \mathbf{then}\ f := f+1\ \mathbf{else}\ f := 1.\ m := \top`. Last we
transform $`x := \mathit{front}` where $`x` is a user's variable of the same type as
the items. Before this operation, there should be a check that the queue is
not empty. ... $`\Leftarrow \mathbf{if}\ f < n\ \mathbf{then}\ x := R\,f\ \mathbf{else}\ x := R\,0`."
Lists of length $`n` are functions of which only the indexes below $`n` matter,
and the implicit conjuncts are made explicit in the transformers (the
"outside" items are $`R\,((f+k) \bmod n)`). The transformer property
$`\forall \mathit{new} \cdot \exists \mathit{old} \cdot D` is proved under the book's typing
$`f, b : 0,..n+1` (and, for the revised $`D`, the implicit conjunct of the chosen
mode). "$`f = b` is missing!" is a theorem: the transformed $`c := \mathit{isemptyq}` under
the first transformer is unimplementable, because from $`f = b` the imagined
queue may be empty (inside) or full (outside). With the mode bit the book's
three programs are proved to refine the transformed $`\mathit{mkemptyq}`,
$`c := \mathit{isemptyq}` and $`c := \mathit{isfullq}`, and the transformed $`c := \mathit{isemptyq}` is
now implementable. The programs for $`\mathit{join}\ x`, $`\mathit{leave}` and $`x := \mathit{front}`
are proved to refine the transformed operations under the checks the book
asks for — "not full", resp. "not empty", as preconditions on the new state
(the transformed $`\mathit{isfullq}` and $`\mathit{isemptyq}`) — with the full case
analysis over the two modes and the wrap-around $`(f+k) \bmod n`; the
"opportunity to rotate the queue within $`R`" is declined as in the book. The
book's intermediate equalities ("several omitted steps") are not reproduced. Uses {uses "data_transformation"}[], {uses "program_queue_theory"}[],
{uses "data_queue_theory"}[] and {uses "specification_laws"}[].
:::

:::theorem "data_transformation_incompleteness" (parent := "theory_design_core") (tags := "theory design, transformation, completeness, hehner-7.2.4") (effort := "medium") (lean := "LaPToP.TheoryDesign.Incompleteness.IJ, LaPToP.TheoryDesign.Incompleteness.init, LaPToP.TheoryDesign.Incompleteness.step, LaPToP.TheoryDesign.Incompleteness.initZero, LaPToP.TheoryDesign.Incompleteness.init_refines, LaPToP.TheoryDesign.Incompleteness.Dz, LaPToP.TheoryDesign.Incompleteness.isTransformer_Dz, LaPToP.TheoryDesign.Incompleteness.transform_initZero, LaPToP.TheoryDesign.Incompleteness.transform_step, LaPToP.TheoryDesign.Incompleteness.IB, LaPToP.TheoryDesign.Incompleteness.initB, LaPToP.TheoryDesign.Incompleteness.stepB, LaPToP.TheoryDesign.Incompleteness.no_transformer")
"Data transformation is sound in the sense that a user cannot tell that a
transformation has been made; that was the criterion of its design. But it is
possible to find two specifications of identical behavior (from a user's point
of view) for which there is no data transformer to transform one into the
other. In that sense, data transformation is incomplete. Exercise 465
illustrates the problem. The user's variable is $`i` and the implementer's
variable is $`j`, both of type $`0, 1, 2`. The operations are:
$`\mathit{initialize} = i' = 0`,
$`\mathit{step} = \mathbf{if}\ j > 0\ \mathbf{then}\ i := i{+}1.\ j := j{-}1\ \mathbf{else}\ ok`. The user
can look at $`i` but not at $`j`. The user can $`\mathit{initialize}`, which starts $`i` at $`0`
and starts $`j` at any of $`3` values. The user can then repeatedly $`\mathit{step}` and
observe that $`i` increases $`0` or $`1` or $`2` times and then stops increasing, which
effectively tells the user what value $`j` started with. If this were a practical
problem, we would notice that $`\mathit{initialize}` can be refined, resolving the
nondeterminism. For example, $`\mathit{initialize} \Leftarrow i := 0.\ j := 0`. We could then
transform $`\mathit{initialize}` and $`\mathit{step}` to get rid of $`j`, replacing it with
nothing. The transformer is $`j = 0`. It transforms the implementation of
$`\mathit{initialize}` as follows: $`\forall j \cdot j = 0 \Rightarrow \exists j' \cdot j' = 0 \land i' = j' = 0 = i := 0`.
And it transforms $`\mathit{step}` as follows:
$`\forall j \cdot j = 0 \Rightarrow \exists j' \cdot j' = 0 \land \mathbf{if}\ j > 0\ \mathbf{then}\ i := i{+}1.\ j := j{-}1\ \mathbf{else}\ ok = ok`.
If this were a practical problem, we would be done. But the theoretical
problem is to replace $`j` with binary variable $`b` without resolving the
nondeterminism, so that $`\mathit{initialize}` is transformed to $`i' = 0` and
$`\mathit{step}` is transformed to $`\mathbf{if}\ b \land i < 2\ \mathbf{then}\ i' = i{+}1\ \mathbf{else}\ ok`. Now
the transformed $`\mathit{initialize}` starts $`b` either at $`\top`, meaning that $`i` will be
increased, or at $`\bot`, meaning that $`i` will not be increased. Each use of the
transformed $`\mathit{step}` tests $`b` to see if we might increase $`i`, and checks $`i < 2` to
ensure that the increased value of $`i` will not exceed $`2`. If $`i` is increased, $`b` is
again assigned either of its two values. The user will see $`i` start at $`0` and
increase $`0` or $`1` or $`2` times and then stop increasing, exactly as in the original
specification. The nondeterminism is maintained. But there is no transformer in
variables $`i`, $`j`, and $`b` to do the job. That's because the initial value of $`j`
gives us $`3` different behaviors, but the initial value of binary variable $`b` cannot
distinguish among these $`3` behaviors."

Model notes. $`i`, $`j` are `Fin 3`; $`i := i{+}1` and $`j := j{-}1` are written on the
values, so $`\mathit{step}` is unsatisfiable at $`i = 2 \land j > 0`, a state the user cannot
reach. Soundness is `transform_spec` of {uses "data_transformation"}[]. The
practical resolution is proved with the transformer $`j = 0` and the new
implementer's type `Unit` ("replacing it with nothing"): $`\mathit{initialize} \Leftarrow i := 0.\ j := 0`,
the transformed $`i := 0.\ j := 0` is $`i := 0`, and the transformed $`\mathit{step}` is $`ok`, in the
style of {uses "data_transformation_examples"}[]. The theoretical claim is the
theorem `no_transformer`: for every transformer $`D` in the variables $`i`, $`j`, $`b`
(`transformU`, which may mention the user's variable) satisfying $`\forall b \cdot \exists j \cdot D`,
the transformed $`\mathit{initialize}` and $`\mathit{step}` are not both equal to $`i' = 0` and
$`\mathbf{if}\ b \land i < 2\ \mathbf{then}\ i' = i{+}1\ \mathbf{else}\ ok` (read with $`b'` arbitrary when $`i` is
increased and $`ok` fixing $`b' = b`). The proof follows the book's reason with four
instances of the $`\mathit{step}` equation: from $`(1, \bot)` to $`(1, \bot)` every $`j` related to
$`(1, \bot)` is $`0`; from $`(0, \top)` to $`(1, \bot)` every $`j` related to $`(0, \top)` is $`1`; from
$`(0, \top)` to $`(1, \top)` then $`D\,1\,0\,\top`; but from $`(1, \top)` to $`(2, \top)` every $`j` related to
$`(1, \top)` is positive — a contradiction, since some $`j` is related to $`(0, \top)`
({uses "specification_implementability"}[] of the transformer, $`\forall b \cdot \exists j \cdot D`).
:::
