import Verso
import VersoManual
import VersoBlueprint
import Aptop.BasicTheories.Binary
import Aptop.ProgramTheory.Specifications

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Prelude" =>

:::group "prelude_core"
Notational conventions and elementary Boolean / predicate scaffolding used
throughout Hehner's *A Practical Theory of Programming*. The book's Section 1.0
calls this *Binary Theory*; its laws (reference §11.3.1) are formalized in the
Lean module `Aptop.BasicTheories.Binary`.
:::

:::author "hehner" (name := "Eric Hehner")
:::

:::definition "boolean_domain" (parent := "prelude_core") (lean := "Aptop.BasicTheories.Binary, Aptop.BasicTheories.Binary.top, Aptop.BasicTheories.Binary.bot, Aptop.BasicTheories.Binary.imp, Aptop.BasicTheories.Binary.rimp")
Expressions in Aptop evaluate in a Boolean domain. We write $`\top` for true
and $`\bot` for false, and treat predicates as Boolean-valued expressions over
a state.

Hehner calls this *Binary Theory*: binary expressions take the values $`\top`
(a theorem) and $`\bot` (an antitheorem), with operators $`\neg`, $`\land`,
$`\lor`, $`\Rightarrow`, $`\Leftarrow`, $`=`, $`\neq`, and
$`\mathbf{if}\ a\ \mathbf{then}\ b\ \mathbf{else}\ c`. In Lean a binary value
is a `Bool` (`Binary`), $`\top` and $`\bot` are `true` and `false`, and the
operators are `!`, `&&`, `||`, `Binary.imp`, `Binary.rimp`, `==`, `!=`, and
`bif … then … else …`. The step from binary expressions to predicates over
program state is taken later, in {bpref "state_as_variables"}[].
:::

:::theorem "boolean_excluded_middle" (parent := "prelude_core") (owner := "hehner") (tags := "prelude, boolean") (effort := "small") (priority := "high") (lean := "Aptop.BasicTheories.Binary.excluded_middle")
For every Boolean $`b`, either $`b` or $`\neg b` holds:
$`b \lor \neg b`.
This is the classical excluded-middle sanity check for {uses "boolean_domain"}[].
:::

:::proof "boolean_excluded_middle"
Case-split on $`b`. Each case is immediate.
:::

```lean "boolean_excluded_middle"
theorem boolean_excluded_middle (b : Bool) :
    b = true ∨ b = false := by
  cases b <;> simp
```

:::theorem "binary_laws_basic" (parent := "prelude_core") (owner := "hehner") (tags := "prelude, binary, hehner-11.3.1") (effort := "small") (lean := "Aptop.BasicTheories.Binary.top_eq, Aptop.BasicTheories.Binary.not_bot, Aptop.BasicTheories.Binary.top_ne_bot, Aptop.BasicTheories.Binary.rimp_eq_imp, Aptop.BasicTheories.Binary.not_not, Aptop.BasicTheories.Binary.noncontradiction, Aptop.BasicTheories.Binary.not_and_bot, Aptop.BasicTheories.Binary.or_top, Aptop.BasicTheories.Binary.imp_top, Aptop.BasicTheories.Binary.bot_imp, Aptop.BasicTheories.Binary.top_and, Aptop.BasicTheories.Binary.bot_or, Aptop.BasicTheories.Binary.top_imp, Aptop.BasicTheories.Binary.top_beq, Aptop.BasicTheories.Binary.and_self, Aptop.BasicTheories.Binary.or_self, Aptop.BasicTheories.Binary.imp_self, Aptop.BasicTheories.Binary.beq_self, Aptop.BasicTheories.Binary.not_imp_bot, Aptop.BasicTheories.Binary.not_imp_self, Aptop.BasicTheories.Binary.and_imp_left, Aptop.BasicTheories.Binary.imp_or_left")
The elementary laws of Binary Theory (reference §11.3.1), for binary $`a, b`:
*Binary* $`\top`, $`\neg\bot`, $`\top \neq \bot`; *Mirror* $`(a \Leftarrow b) = (b \Rightarrow a)`;
*Double Negation* $`\neg\neg a = a`; *Noncontradiction* $`\neg(a \land \neg a)`;
*Base* $`\neg(a \land \bot)`, $`a \lor \top`, $`a \Rightarrow \top`, $`\bot \Rightarrow a`;
*Identity* $`\top \land a = a`, $`\bot \lor a = a`, $`(\top \Rightarrow a) = a`, $`(\top = a) = a`;
*Idempotent* $`a \land a = a`, $`a \lor a = a`; *Reflexive* $`a \Rightarrow a`, $`a = a`;
*Indirect Proof* $`(\neg a \Rightarrow \bot) = a`, $`(\neg a \Rightarrow a) = a`;
*Specialization* $`a \land b \Rightarrow a`; *Generalization* $`a \Rightarrow a \lor b`.
Together with {uses "boolean_excluded_middle"}[], these are the laws Hehner
uses most in calculations over {uses "boolean_domain"}[].
:::

:::proof "binary_laws_basic"
Each law is a truth table: case-split on the variables and evaluate
(`revert …; decide`).
:::

:::theorem "binary_laws_algebra" (parent := "prelude_core") (owner := "hehner") (tags := "prelude, binary, hehner-11.3.1") (effort := "small") (lean := "Aptop.BasicTheories.Binary.and_assoc, Aptop.BasicTheories.Binary.or_assoc, Aptop.BasicTheories.Binary.beq_assoc, Aptop.BasicTheories.Binary.bne_assoc, Aptop.BasicTheories.Binary.beq_bne_assoc, Aptop.BasicTheories.Binary.and_comm, Aptop.BasicTheories.Binary.or_comm, Aptop.BasicTheories.Binary.beq_comm, Aptop.BasicTheories.Binary.bne_comm, Aptop.BasicTheories.Binary.imp_and_imp, Aptop.BasicTheories.Binary.and_imp_self, Aptop.BasicTheories.Binary.imp_and_self, Aptop.BasicTheories.Binary.not_and, Aptop.BasicTheories.Binary.not_or, Aptop.BasicTheories.Binary.imp_not_comm, Aptop.BasicTheories.Binary.beq_not, Aptop.BasicTheories.Binary.bne_eq_not_beq, Aptop.BasicTheories.Binary.imp_eq_not_or, Aptop.BasicTheories.Binary.imp_eq_and_beq, Aptop.BasicTheories.Binary.imp_eq_or_beq, Aptop.BasicTheories.Binary.and_or_self, Aptop.BasicTheories.Binary.or_and_self, Aptop.BasicTheories.Binary.and_and_distrib, Aptop.BasicTheories.Binary.and_or_distrib, Aptop.BasicTheories.Binary.or_and_distrib, Aptop.BasicTheories.Binary.or_or_distrib, Aptop.BasicTheories.Binary.or_imp_distrib, Aptop.BasicTheories.Binary.or_beq_distrib, Aptop.BasicTheories.Binary.imp_and_distrib, Aptop.BasicTheories.Binary.imp_or_distrib, Aptop.BasicTheories.Binary.imp_imp_distrib, Aptop.BasicTheories.Binary.imp_beq_distrib, Aptop.BasicTheories.Binary.and_imp_antidistrib, Aptop.BasicTheories.Binary.or_imp_antidistrib, Aptop.BasicTheories.Binary.and_imp_eq_imp_imp, Aptop.BasicTheories.Binary.and_imp_eq_imp_not_or, Aptop.BasicTheories.Binary.beq_eq_or, Aptop.BasicTheories.Binary.bne_eq_or")
The algebraic laws of Binary Theory (reference §11.3.1), for binary $`a, b, c`:
*Associative* for $`\land`, $`\lor`, $`=`, $`\neq` and the mixed
$`(a = (b \neq c)) = ((a = b) \neq c)`; *Symmetry* for $`\land, \lor, =, \neq`;
*Antisymmetry* $`(a \Rightarrow b) \land (b \Rightarrow a) = (a = b)`;
*Discharge* $`a \land (a \Rightarrow b) = a \land b`, $`(a \Rightarrow a \land b) = (a \Rightarrow b)`;
*Duality* $`\neg(a \land b) = \neg a \lor \neg b`, $`\neg(a \lor b) = \neg a \land \neg b`;
*Exclusion* $`(a \Rightarrow \neg b) = (b \Rightarrow \neg a)`, $`(a = \neg b) = (a \neq b) = (\neg a = b)`;
*Inclusion* $`(a \Rightarrow b) = \neg a \lor b = (a \land b = a) = (a \lor b = b)`;
*Absorption* $`a \land (a \lor b) = a`, $`a \lor (a \land b) = a`;
*Distributive* (ten laws, e.g. $`a \Rightarrow (b \Rightarrow c) = (a \Rightarrow b) \Rightarrow (a \Rightarrow c)`);
*Antidistributive* $`(a \land b \Rightarrow c) = (a \Rightarrow c) \lor (b \Rightarrow c)`,
$`(a \lor b \Rightarrow c) = (a \Rightarrow c) \land (b \Rightarrow c)`;
*Portation* $`(a \land b \Rightarrow c) = (a \Rightarrow (b \Rightarrow c)) = (a \Rightarrow \neg b \lor c)`;
*Equality and Difference* $`(a = b) = (a \land b) \lor (\neg a \land \neg b)`,
$`(a \neq b) = (a \land \neg b) \lor (\neg a \land b)`.
Uses {uses "boolean_domain"}[].
:::

:::proof "binary_laws_algebra"
Truth tables (`revert …; decide`); Material Implication is the definition of
`Binary.imp`.
:::

:::theorem "binary_laws_reasoning" (parent := "prelude_core") (owner := "hehner") (tags := "prelude, binary, hehner-11.3.1") (effort := "small") (lean := "Aptop.BasicTheories.Binary.modus_ponens, Aptop.BasicTheories.Binary.modus_tollens, Aptop.BasicTheories.Binary.or_and_not_imp, Aptop.BasicTheories.Binary.and_and_trans, Aptop.BasicTheories.Binary.imp_trans, Aptop.BasicTheories.Binary.beq_trans, Aptop.BasicTheories.Binary.imp_beq_trans, Aptop.BasicTheories.Binary.beq_imp_trans, Aptop.BasicTheories.Binary.imp_eq_rimp_not, Aptop.BasicTheories.Binary.imp_rimp_imp, Aptop.BasicTheories.Binary.imp_and_right, Aptop.BasicTheories.Binary.imp_or_right, Aptop.BasicTheories.Binary.imp_imp_left, Aptop.BasicTheories.Binary.imp_and_imp_and, Aptop.BasicTheories.Binary.imp_and_imp_or, Aptop.BasicTheories.Binary.resolution_left, Aptop.BasicTheories.Binary.resolution_middle, Aptop.BasicTheories.Binary.resolution_right")
The laws of Binary Theory that license proof steps (reference §11.3.1):
*Direct Proof* $`(a \Rightarrow b) \land a \Rightarrow b`, $`(a \Rightarrow b) \land \neg b \Rightarrow \neg a`,
$`(a \lor b) \land \neg a \Rightarrow b`;
*Transitive* for $`\land`, $`\Rightarrow`, $`=` and the mixed forms
$`(a \Rightarrow b) \land (b = c) \Rightarrow (a \Rightarrow c)`, $`(a = b) \land (b \Rightarrow c) \Rightarrow (a \Rightarrow c)`;
*Antimonotonic* $`(a \Rightarrow b) = (\neg a \Leftarrow \neg b)`,
$`a \Rightarrow b \Rightarrow ((a \Rightarrow c) \Leftarrow (b \Rightarrow c))`;
*Monotonic* $`a \Rightarrow b \Rightarrow (a \land c \Rightarrow b \land c)`,
$`a \Rightarrow b \Rightarrow (a \lor c \Rightarrow b \lor c)`,
$`a \Rightarrow b \Rightarrow ((c \Rightarrow a) \Rightarrow (c \Rightarrow b))`;
*Conflation* $`(a \Rightarrow b) \land (c \Rightarrow d) \Rightarrow (a \land c \Rightarrow b \land d)` and the
$`\lor` version; *Resolution*
$`a \land c \Rightarrow (a \lor b) \land (\neg b \lor c) = (a \land \neg b) \lor (b \land c) \Rightarrow a \lor c`,
stated as its three steps. These justify the *monotonicity* and
*antimonotonicity* reasoning of Section 1.0.1 and the calculation style of
{bpref "calculation_style"}[]. Uses {uses "boolean_domain"}[].
:::

:::proof "binary_laws_reasoning"
Truth tables (`revert …; decide`).
:::

:::theorem "binary_laws_case" (parent := "prelude_core") (owner := "hehner") (tags := "prelude, binary, hehner-11.3.1") (effort := "small") (lean := "Aptop.BasicTheories.Binary.case_creation_imp, Aptop.BasicTheories.Binary.case_creation_and, Aptop.BasicTheories.Binary.case_creation_beq, Aptop.BasicTheories.Binary.cond_eq_or, Aptop.BasicTheories.Binary.cond_eq_and, Aptop.BasicTheories.Binary.cond_top_left, Aptop.BasicTheories.Binary.cond_bot_left, Aptop.BasicTheories.Binary.cond_top_right, Aptop.BasicTheories.Binary.cond_bot_right, Aptop.BasicTheories.Binary.cond_not_right, Aptop.BasicTheories.Binary.cond_not_left, Aptop.BasicTheories.Binary.cond_absorb_and, Aptop.BasicTheories.Binary.cond_absorb_imp, Aptop.BasicTheories.Binary.cond_absorb_beq, Aptop.BasicTheories.Binary.cond_absorb_not_and, Aptop.BasicTheories.Binary.cond_absorb_or, Aptop.BasicTheories.Binary.cond_absorb_bne, Aptop.BasicTheories.Binary.not_cond, Aptop.BasicTheories.Binary.cond_op, Aptop.BasicTheories.Binary.cond_op_cond, Aptop.BasicTheories.Binary.cond_and, Aptop.BasicTheories.Binary.cond_and_cond")
The laws for $`\mathbf{if}\ a\ \mathbf{then}\ b\ \mathbf{else}\ c` (reference §11.3.1):
*Case Creation* $`a = \mathbf{if}\ b\ \mathbf{then}\ b \Rightarrow a\ \mathbf{else}\ \neg b \Rightarrow a`
(and the $`\land`, $`=`/$`\neq` forms);
*Case Analysis* $`\mathbf{if}\ a\ \mathbf{then}\ b\ \mathbf{else}\ c = (a \land b) \lor (\neg a \land c) = (a \Rightarrow b) \land (\neg a \Rightarrow c)`;
*One Case* (six laws, e.g. $`\mathbf{if}\ a\ \mathbf{then}\ b\ \mathbf{else}\ \top = (a \Rightarrow b)`);
*Case Absorption* (six laws, e.g. $`\mathbf{if}\ a\ \mathbf{then}\ b\ \mathbf{else}\ c = \mathbf{if}\ a\ \mathbf{then}\ a \land b\ \mathbf{else}\ c`);
*Case Distributive* $`\neg\,\mathbf{if}\ a\ \mathbf{then}\ b\ \mathbf{else}\ c = \mathbf{if}\ a\ \mathbf{then}\ \neg b\ \mathbf{else}\ \neg c`,
$`(\mathbf{if}\ a\ \mathbf{then}\ b\ \mathbf{else}\ c) \land d = \mathbf{if}\ a\ \mathbf{then}\ b \land d\ \mathbf{else}\ c \land d`, and
$`\mathbf{if}\ a\ \mathbf{then}\ b \land c\ \mathbf{else}\ d \land e = (\mathbf{if}\ a\ \mathbf{then}\ b\ \mathbf{else}\ d) \land (\mathbf{if}\ a\ \mathbf{then}\ c\ \mathbf{else}\ e)`,
"and similarly replacing $`\land` by any of $`\lor = \neq \Rightarrow \Leftarrow`" — stated
once for an arbitrary binary operator. Uses {uses "boolean_domain"}[].
:::

:::proof "binary_laws_case"
Truth tables (`revert …; decide`); the generic Case Distributive laws are a
case split on the condition followed by `rfl`.
:::

:::definition "state_as_variables" (parent := "prelude_core") (lean := "Aptop.ProgramTheory.Spec.State")
A *state* assigns values to program variables. Informal specifications and
programs are expressions over those variables; refining one specification into
another is the central activity of the book.
:::
