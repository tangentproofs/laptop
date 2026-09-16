import Verso
import VersoManual
import VersoBlueprint
import LaPToP.Interaction.InteractiveVariables

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Interaction" =>

:::group "interaction_core"
Hehner's Chapter 9: "The interactive variables and communication channels of
this chapter allow ... a computation to interact with its environment while it
is in progress". Interactive variables (Section 9.0) are formalized in
`LaPToP.Interaction.InteractiveVariables`.
:::

:::definition "interactive_variables" (parent := "interaction_core") (lean := "LaPToP.Interaction.BT, LaPToP.Interaction.IVar, LaPToP.Interaction.ISpec, LaPToP.Interaction.ISpec.ext, LaPToP.Interaction.ISpec.newX, LaPToP.Interaction.ISpec.ok, LaPToP.Interaction.ISpec.assignA, LaPToP.Interaction.ISpec.assignX, LaPToP.Interaction.ISpec.assignXP, LaPToP.Interaction.ISpec.assignYQ, LaPToP.Interaction.ISpec.seq, LaPToP.Interaction.ISpec.par, LaPToP.Interaction.ISpec.ok_seq, LaPToP.Interaction.ISpec.seq_ok, LaPToP.Interaction.ISpec.seq_assoc, LaPToP.Interaction.ISpec.assignA_seq, LaPToP.Interaction.ISpec.substX, LaPToP.Interaction.ISpec.not_substitution_law")
"Let the notation $`\mathbf{new}\ x : \mathit{time} \to T \cdot S` declare $`x` to be an
interactive variable of type $`T` and scope $`S`. It is defined as follows.
$`\mathbf{new}\ x : \mathit{time} \to T \cdot S = \exists x : \mathit{time} \to T \cdot S` where $`\mathit{time}` is
the domain of time, either the extended naturals or the nonnegative extended
reals. An interactive variable is a function of time. The value of variable
$`x` at time $`t` is $`x\,t`. ... Suppose $`a` and $`b` are boundary variables, $`x` and
$`y` are interactive variables, and $`t` is time. The definition of $`\mathit{ok}` says
that the boundary variables and time are unchanged. $`\mathit{ok} = a' = a \land b' = b \land t' = t`.
... $`a := e = a' = e \land b' = b \land t' = t`. Assignment to an interactive variable
cannot be instantaneous because it is time that distinguishes its values.
$`x := e = a' = a \land b' = b \land x' = e \land (\forall t'' \cdot t \le t'' \le t' \Rightarrow y'' = y) \land t' = t + (\text{the time required to evaluate and store } e)`.
At the final time $`t'`, interactive variable $`x` has value $`e`, but nothing is
said about the value of $`x` during the assignment. Interactive variable $`y`
remains unchanged throughout the duration of the assignment to $`x`. ...
Sequential composition hides the intermediate values of the boundary and
time variables, leaving the intermediate values of the interactive variables
visible. ... $`P.\ Q = \exists a'', b'', t'' \cdot \langle a', b', t' \cdot P \rangle\ a''\ b''\ t'' \land \langle a, b, t \cdot Q \rangle\ a''\ b''\ t''`.
For concurrent composition we partition all the variables, both boundary and
interactive (but not time). Suppose $`a` and $`x` belong to $`P`, and $`b` and $`y`
belong to $`Q`.
$`P \parallel Q = \exists t_P, t_Q \cdot \langle t' \cdot P \rangle\ t_P \land (\forall t'' \cdot t_P \le t'' \le t' \Rightarrow x'' = x\,t_P) \land \langle t' \cdot Q \rangle\ t_Q \land (\forall t'' \cdot t_Q \le t'' \le t' \Rightarrow y'' = y\,t_Q) \land t' = t_P \uparrow t_Q`.
The new part says that when the shorter process is finished, its interactive
variables remain unchanged while the longer process is finishing. ... Most of
the specification laws and refinement laws survive the addition of
interactive variables, but sadly, the Substitution Law no longer works."
Model: time is $`\mathit{xnat}` (the book also allows the reals); the boundary
variables and time form the before/after state, and an interactive variable
is a function $`\mathit{xnat} \to \mathit{int}` of which a specification is a function — so
$`x'` is $`x\,t'` and the intermediate values of $`x` stay visible through
sequential composition, as the book says. The time an assignment takes is a
parameter. Besides the general assignment in all four variables, the
process-local forms used in the book's Exercise 496 (each process's
assignments expanded in its own variables) are defined; in $`P \parallel Q` the
process $`P` sees $`b` at its initial value. Proved: $`\mathit{ok}` is the identity of
sequential composition, which is associative; the Substitution Law still
holds for the boundary variable $`a`; and it fails for the interactive variable
$`x` — with "substitute $`e` for $`x`" read as replacing the function $`x` by the
constant $`e`, $`x := 2.\ \mathit{ok}` is not $`\mathit{ok}`, because the assignment takes time.
Uses {uses "concurrent_composition"}[], {uses "time_variable"}[],
{uses "variable_declaration"}[] and {uses "substitution_law"}[].
:::

:::theorem "exercise_496" (parent := "interaction_core") (tags := "interaction, concurrency, time, hehner-9.0") (effort := "medium") (lean := "LaPToP.Interaction.ISpec.leftP, LaPToP.Interaction.ISpec.rightQ, LaPToP.Interaction.ISpec.exercise_496")
"Exercise 496 is an example in the same variables $`a`, $`b`, $`x`, $`y`, and $`t`.
Suppose that time is an extended natural, and that each assignment takes time
$`1`. $`(x := 2.\ x := x+y.\ x := x+y) \parallel (y := 3.\ y := x+y)`, $`x` is a variable in the
left process and $`y` is a variable in the right process. Let's put $`a` in the
left process and $`b` in the right process.
$`= (a' = a \land x' = 2 \land t' = t+1.\ a' = a \land x' = x+y \land t' = t+1.\ a' = a \land x' = x+y \land t' = t+1) \parallel (b' = b \land y' = 3 \land t' = t+1.\ b' = b \land y' = x+y \land t' = t+1)`
$`= a' = a \land x(t+1) = 2 \land x(t+2) = x(t+1) + y(t+1) \land x(t+3) = x(t+2) + y(t+2) \land b' = b \land y(t+1) = 3 \land y(t+2) = x(t+1) + y(t+1) \land y(t+3) = y(t+2) \land t' = t+3`
$`= a' = a \land x(t+1) = 2 \land x(t+2) = 5 \land x(t+3) = 10 \land b' = b \land y(t+1) = 3 \land y(t+2) = y(t+3) = 5 \land t' = t+3`.
The example gives the appearance of lock-step synchrony only because we took
each assignment time to be $`1`." The equality is proved for a finite initial
time $`t` (the initial time $`\infty` is degenerate); $`y(t+3) = y(t+2)` comes from
the "remain unchanged" clause of $`\parallel`. Uses {uses "interactive_variables"}[].
:::
