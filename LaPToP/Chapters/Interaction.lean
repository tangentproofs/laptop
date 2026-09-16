import Verso
import VersoManual
import VersoBlueprint
import LaPToP.Interaction.InteractiveVariables
import LaPToP.Interaction.Communication
import LaPToP.Interaction.CommunicationTiming
import LaPToP.Interaction.Merge
import LaPToP.Interaction.ChannelDeclaration
import LaPToP.Interaction.Deadlock
import LaPToP.Interaction.PowerSeries

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Interaction" =>

:::group "interaction_core"
Hehner's Chapter 9: "The interactive variables and communication channels of
this chapter allow ... a computation to interact with its environment while it
is in progress". Interactive variables (Section 9.0) are formalized in
`LaPToP.Interaction.InteractiveVariables`, and communication channels
(Section 9.1) in `LaPToP.Interaction.Communication`.
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

:::definition "communication" (parent := "interaction_core") (lean := "LaPToP.Interaction.Scripts, LaPToP.Interaction.CS, LaPToP.Interaction.CSpec, LaPToP.Interaction.Channel.output, LaPToP.Interaction.Channel.input, LaPToP.Interaction.Channel.lastRead, LaPToP.Interaction.Channel.check, LaPToP.Interaction.Channel.input_seq, LaPToP.Interaction.Channel.output_seq, LaPToP.Interaction.Channel.Increasing, LaPToP.Interaction.Channel.increasing_ok, LaPToP.Interaction.Channel.increasing_input, LaPToP.Interaction.Channel.increasing_output, LaPToP.Interaction.Channel.increasing_seq, LaPToP.Interaction.Channel.increasing_cond")
"This section introduces named communication channels through which a
computation communicates with its environment, which may be people or other
computations running concurrently. For each channel, only one process (person
or computation) writes to it, but all processes can read all the messages,
each at its own speed. ... Communication on channel $`c` is described by two
infinite strings $`\mathcal{M}_c` and $`\mathcal{T}_c` called the message script and the
time script, and two extended natural variables $`r_c` and $`w_c` called the read
cursor and the write cursor. The message script is the string of all
messages, past, present, and future, that pass along the channel. The time
script is the corresponding string of times that the messages were or are or
will be sent. The scripts are state constants, not state variables. The read
cursor is a state variable saying how many messages have been read, or input,
from the channel. The write cursor is a state variable saying how many
messages have been written, or output, to the channel. ... after 3 more reads
the next input on channel $`c` will be $`\mathcal{M}_c\,(r_c+3)`, and after 5 more
writes the next output will be $`\mathcal{M}_c\,(w_c+5)` and it will occur at time
$`\mathcal{T}_c\,(w_c+5)`. ... The scripts and the cursors are not programming
notations, but they allow us to specify any desired communications. ... If
there are only a finite number of communications on a channel, then after the
last message, the time script items are all $`\infty`, and the message script
items are of no interest." "Here are four programming notations for
communication. Let $`c` be a channel. The notation $`c!\,e` describes a computation
that writes the output message $`e` on channel $`c`. The notation $`c?` describes a
computation that reads one input on channel $`c`. We use the channel name $`c` to
denote the message that was last previously read on the channel. And $`\surd c`
is a binary expression meaning “there is unread input available on channel
$`c`”. Here are the formal definitions.
$`c!\,e = \mathcal{M}w = e \land \mathcal{T}w = t \land (w := w+1)` “$`c` output $`e`”;
$`c? = r := r+1` “$`c` input”; $`c = \mathcal{M}(r-1)`; $`\surd c = \mathcal{T}r \le t` “check $`c`”."
And (Subsection 9.1.0): "During a computation, the memory variables can change
value in any way, but time and the cursors can only increase. Once an input
has been read, it cannot be unread; once an output has been written, it cannot
be unwritten. Every computation satisfies $`t' \ge t \land r' \ge r \land w' \ge w`."
Model: the scripts are functions $`\mathbb{N} \to \alpha` and $`\mathbb{N} \to \mathit{xnat}` (infinite strings),
constants of which a specification is a function, as for
{uses "interactive_variables"}[]; the state has the time, the two cursors (as
naturals — the book's extended naturals; a cursor is never $`\infty` in a finite
computation) and a memory variable. $`c!\,e` is literally
$`\mathcal{M}w = e \land \mathcal{T}w = t \land (w := w+1)`, a constraint on the constant scripts
together with the increment of the write cursor. The Substitution Laws for
$`c?` and $`c!\,e`, and the every-computation law for the primitives, closed under
sequential composition and conditional, are proved. Uses
{uses "time_variable"}[], {uses "string_syntax"}[] and {uses "specification_notations"}[].
:::

:::definition "communication_implementability" (parent := "interaction_core") (lean := "LaPToP.Interaction.Channel.ImplementableC, LaPToP.Interaction.Channel.implementableC_output, LaPToP.Interaction.Channel.implementableC_input")
"An implementable specification can say what the scripts are in the segment
written by a computation, that is the segment $`\mathcal{M}\,(w;..w')` and
$`\mathcal{T}\,(w;..w')` between the initial and final values of the write cursor, but
it cannot specify the scripts outside this segment. Furthermore, the time
script must be monotonic, and all its values in this segment must be in the
range from $`t` to $`t'`. A specification $`S` (in initial state $`\sigma`, final state
$`\sigma'`, message script $`\mathcal{M}`, and time script $`\mathcal{T}`) is implementable if and
only if
$`\forall \sigma, M, T \cdot \exists \sigma', \mathcal{M}, \mathcal{T} \cdot S \land t' \ge t \land r' \ge r \land w' \ge w \land \mathcal{M}(0;..w); (w';..\infty) = M(0;..w); (w';..\infty) \land \mathcal{T}(0;..w); (w';..\infty) = T(0;..w); (w';..\infty) \land \forall i, j : w,..w' \cdot i \le j \Rightarrow t \le \mathcal{T}i \le \mathcal{T}j \le t'`.
If we have many channels, we need similar conjuncts for each. If we have no
channels, implementability reduces to the definition given in Chapter 4. To
implement communication channels, it is not necessary to build two infinite
strings. At any given time, only those messages that have been written and
not yet read need to be stored. The time script is only for specification and
proof, and does not need to be stored." The definition is stated literally
(the scripts re-chosen only on the segment $`w;..w'`, the time script monotonic
and within $`t;..t'` there), and $`c!\,e` and $`c?` are proved implementable — the
output chooses $`\mathcal{M}w = e` and $`\mathcal{T}w = t`. Uses {uses "communication"}[]
and {uses "specification_implementability"}[].
:::

:::theorem "input_output_examples" (parent := "interaction_core") (tags := "interaction, channels, hehner-9.1.1") (effort := "small") (lean := "LaPToP.Interaction.CS2, LaPToP.Interaction.TwoChannels.inputC, LaPToP.Interaction.TwoChannels.outputD, LaPToP.Interaction.TwoChannels.lastReadC, LaPToP.Interaction.TwoChannels.inputC_seq, LaPToP.Interaction.TwoChannels.outputD_seq, LaPToP.Interaction.TwoChannels.evenSpec, LaPToP.Interaction.TwoChannels.evenSpec_iff, LaPToP.Interaction.TwoChannels.evenSpec_refines, LaPToP.Interaction.TwoChannels.doubling, LaPToP.Interaction.TwoChannels.doubling_refines")
"Here is an example specification. It says that if the next input on channel
$`c` is even, then the next output on channel $`d` will be $`\top`, and otherwise it
will be $`\bot`. Formally, we may write
$`\mathbf{if}\ \mathit{even}\,(\mathcal{M}_c\,r_c)\ \mathbf{then}\ \mathcal{M}_d\,w_d = \top\ \mathbf{else}\ \mathcal{M}_d\,w_d = \bot` or, more
briefly, $`\mathcal{M}_d\,w_d = \mathit{even}\,(\mathcal{M}_c\,r_c)`. ... Let us refine the specification
$`\mathcal{M}_d\,w_d = \mathit{even}\,(\mathcal{M}_c\,r_c)` given earlier.
$`\mathcal{M}_d\,w_d = \mathit{even}\,(\mathcal{M}_c\,r_c) \Leftarrow c?.\ d!\,\mathit{even}\ c`. To prove the refinement,
starting with the right side, $`c?.\ d!\,\mathit{even}\ c = r_c := r_c+1.\ \mathcal{M}_d\,w_d = \mathit{even}\,(\mathcal{M}_c\,(r_c-1)) \land \mathcal{T}_d\,w_d = t \land (w_d := w_d+1) = \mathcal{M}_d\,w_d = \mathit{even}\,(\mathcal{M}_c\,r_c) \land \mathcal{T}_d\,w_d = t \land r_c' = r_c+1 \land w_c' = w_c \land r_d' = r_d \land w_d' = w_d+1 \Rightarrow \mathcal{M}_d\,w_d = \mathit{even}\,(\mathcal{M}_c\,r_c)`.
... Our next problem is to read numbers from channel $`c`, and write their
doubles on channel $`d`. Ignoring time, the specification can be written
$`S = \forall n : \mathit{nat} \cdot \mathcal{M}_d\,(w_d+n) = 2 \times \mathcal{M}_c\,(r_c+n)`. The input and output may
not be the first input and output ever on channels $`c` and $`d`. But from now on,
starting at the initial read cursor $`r_c` and initial write cursor $`w_d`, the
outputs will be double the inputs. This specification can be refined as
follows. $`S \Leftarrow c?.\ d!\,2 \times c.\ S`. The proof is:
$`c?.\ d!\,2 \times c.\ S = r_c := r_c+1.\ \mathcal{M}_d\,w_d = 2 \times \mathcal{M}_c\,(r_c-1) \land (w_d := w_d+1).\ \forall n \cdot \mathcal{M}_d\,(w_d+n) = 2 \times \mathcal{M}_c\,(r_c+n) = \mathcal{M}_d\,w_d = 2 \times \mathcal{M}_c\,r_c \land \forall n \cdot \mathcal{M}_d\,(w_d+1+n) = 2 \times \mathcal{M}_c\,(r_c+1+n) = \forall n \cdot \mathcal{M}_d\,(w_d+n) = 2 \times \mathcal{M}_c\,(r_c+n) = S`."
On a state with two channels, both refinements are proved exactly as
calculated — the second with the recursive call $`S` as a specification, as in
{uses "recursive_program_zap"}[] — and the two forms of the first
specification are shown to agree. Uses {uses "communication"}[] and
{uses "substitution_law"}[].
:::

:::theorem "communication_timing" (parent := "interaction_core") (tags := "interaction, channels, time, hehner-9.1.2") (effort := "small") (lean := "LaPToP.Interaction.Channel.assignT, LaPToP.Interaction.Channel.tick, LaPToP.Interaction.Channel.assignT_seq, LaPToP.Interaction.Channel.inputT, LaPToP.Interaction.Channel.checkT, LaPToP.Interaction.Channel.inputT_eq, LaPToP.Interaction.Channel.inputT_refines")
"In the real time measure, we need to know how long output takes, how long
communication transit takes, and how long input takes, and we place time
increments appropriately. To be independent of these implementation details,
we can use the transit time measure, in which we suppose that the acts of
input and output take no time, and that communication transit takes 1 time
unit. The message to be read next on channel $`c` is $`\mathcal{M}_c\,r_c`. This message
was or is or will be sent at time $`\mathcal{T}_c\,r_c`. Its arrival time, according to
the transit time measure, is $`\mathcal{T}_c\,r_c + 1`. So input becomes
$`t := t \uparrow (\mathcal{T}_c\,r_c + 1).\ c?`. If the input has already arrived,
$`\mathcal{T}_c\,r_c + 1 \le t`, and no time is spent waiting for input; otherwise execution
of $`c?` is delayed until the input arrives. And the input check $`\surd c` becomes
$`\surd c = \mathcal{T}_c\,r_c + 1 \le t`. ... Exercise 516(a): Let $`W` be “wait for input on
channel $`c` and then read it”. Formally, $`W = t := t \uparrow (\mathcal{T}r + 1).\ c?`. Prove
$`W \Leftarrow \mathbf{if}\ \surd c\ \mathbf{then}\ c?\ \mathbf{else}\ t := t+1.\ W` where time is an extended
natural. The significance of this exercise is that input is often implemented
in just this way, with a test to see if input is available, and a loop if it is
not. Proof: $`\mathbf{if}\ \surd c\ \mathbf{then}\ c?\ \mathbf{else}\ t := t+1.\ W = \mathbf{if}\ \mathcal{T}r + 1 \le t\ \mathbf{then}\ c?\ \mathbf{else}\ t := t+1.\ t := t \uparrow (\mathcal{T}r + 1).\ c? = \mathbf{if}\ \mathcal{T}r + 1 \le t\ \mathbf{then}\ t := t.\ c?\ \mathbf{else}\ t := (t+1) \uparrow (\mathcal{T}r + 1).\ c?`
— if $`\mathcal{T}r + 1 \le t`, then $`t = t \uparrow (\mathcal{T}r + 1)`; if $`\mathcal{T}r + 1 > t` then
$`(t+1) \uparrow (\mathcal{T}r + 1) = \mathcal{T}r + 1 = t \uparrow (\mathcal{T}r + 1)` —
$`= \mathbf{if}\ \mathcal{T}r + 1 \le t\ \mathbf{then}\ t := t \uparrow (\mathcal{T}r + 1).\ c?\ \mathbf{else}\ t := t \uparrow (\mathcal{T}r + 1).\ c? = W`."
Transit-time input and the check are defined on the one-channel state of
{uses "communication"}[], and Exercise 516(a) is proved by the book's two
cases (as the busy-wait loop of {uses "time_dependence"}[]), using
{uses "refinement_by_steps_parts_cases"}[].
:::

:::theorem "recursive_communication" (parent := "interaction_core") (tags := "interaction, channels, recursion, hehner-9.1.3") (effort := "medium") (lean := "LaPToP.Interaction.TwoChannels.tick, LaPToP.Interaction.TwoChannels.tick_seq, LaPToP.Interaction.TwoChannels.dblBody, LaPToP.Interaction.TwoChannels.dblW, LaPToP.Interaction.TwoChannels.dblSeq, LaPToP.Interaction.TwoChannels.dblBody_apply, LaPToP.Interaction.TwoChannels.dblW_fixedPoint, LaPToP.Interaction.TwoChannels.fixedPoint_refines_dblW, LaPToP.Interaction.TwoChannels.bot_fixedPoint, LaPToP.Interaction.TwoChannels.dblSeq_eq, LaPToP.Interaction.TwoChannels.dblW_iff_forall")
"Define $`\mathit{dbl}` by the fixed-point construction (including recursive time
but ignoring input waits) $`\mathit{dbl} = c?.\ d!\,2 \times c.\ t := t+1.\ \mathit{dbl}`. Regarding
$`\mathit{dbl}` as the unknown, this equation has several solutions. The weakest is
$`\forall n : \mathit{nat} \cdot \mathcal{M}_d\,(w_d+n) = 2 \times \mathcal{M}_c\,(r_c+n) \land \mathcal{T}_d\,(w_d+n) = t+n`. The
strongest implementable solution is
$`(\forall n : \mathit{nat} \cdot \mathcal{M}_d\,(w_d+n) = 2 \times \mathcal{M}_c\,(r_c+n) \land \mathcal{T}_d\,(w_d+n) = t+n) \land r_c' = w_d' = t' = \infty \land w_c' = w_c \land r_d' = r_d`.
The strongest solution is $`\bot`. If this fixed-point construction is all we
know about $`\mathit{dbl}`, then we cannot say that it is equal to a particular one of
the solutions. But we can say this: it refines the weakest solution ... and it
is refined by the right side of the fixed-point construction ... Thus we can
use it to solve problems, and we can execute it. If we begin recursive
construction with $`\mathit{dbl}_0 = \top` we find
$`\mathit{dbl}_1 = c?.\ d!\,2 \times c.\ t := t+1.\ \mathit{dbl}_0 = \mathcal{M}_d\,w_d = 2 \times \mathcal{M}_c\,r_c \land \mathcal{T}_d\,w_d = t`,
$`\mathit{dbl}_2 = \ldots = \mathcal{M}_d\,w_d = 2 \times \mathcal{M}_c\,r_c \land \mathcal{T}_d\,w_d = t \land \mathcal{M}_d\,(w_d+1) = 2 \times \mathcal{M}_c\,(r_c+1) \land \mathcal{T}_d\,(w_d+1) = t+1`
and so on. The result of the construction
$`\mathit{dbl}_\infty = \forall n : \mathit{nat} \cdot \mathcal{M}_d\,(w_d+n) = 2 \times \mathcal{M}_c\,(r_c+n) \land \mathcal{T}_d\,(w_d+n) = t+n` is
the weakest solution of the $`\mathit{dbl}` fixed-point construction." Proved, on the
two-channel state of {uses "input_output_examples"}[]: one unrolling of the
construction in closed form; $`\mathit{dbl}_\infty` is a fixed point; every fixed point
refines $`\mathit{dbl}_\infty` (by induction on $`n`, unrolling once per output), which is
the sense in which "it refines the weakest solution"; $`\bot` is a fixed point;
and the construction sequence in closed form,
$`\mathit{dbl}_n = \forall k : 0,..n \cdot \mathcal{M}_d\,(w_d+k) = 2 \times \mathcal{M}_c\,(r_c+k) \land \mathcal{T}_d\,(w_d+k) = t+k`,
whose intersection is $`\mathit{dbl}_\infty`, as in
{uses "recursive_program_construction"}[] and {uses "least_fixed_points"}[].
Not stated: the "strongest implementable solution", whose $`r_c' = w_d' = \infty`
needs extended-natural cursors, while cursors are naturals here.
:::

:::theorem "merge" (parent := "interaction_core") (tags := "interaction, channels, merge, hehner-9.1.4") (effort := "medium") (lean := "LaPToP.Interaction.stepF, LaPToP.Interaction.guardedF, LaPToP.Interaction.stepF_seq, LaPToP.Interaction.guardedF_seq, LaPToP.Interaction.MS, LaPToP.Interaction.Merge.inputC, LaPToP.Interaction.Merge.inputD, LaPToP.Interaction.Merge.outputE, LaPToP.Interaction.Merge.lastC, LaPToP.Interaction.Merge.lastD, LaPToP.Interaction.Merge.checkC, LaPToP.Interaction.Merge.checkD, LaPToP.Interaction.Merge.waitC, LaPToP.Interaction.Merge.waitD, LaPToP.Interaction.Merge.tick, LaPToP.Interaction.Merge.mergeBody, LaPToP.Interaction.Merge.mergeBody_step, LaPToP.Interaction.Merge.timemergeBody, LaPToP.Interaction.Merge.implBody, LaPToP.Interaction.Merge.step_refines_c, LaPToP.Interaction.Merge.step_refines_d, LaPToP.Interaction.Merge.not_step_refines")
"Merging means reading repeatedly from two or more input channels and writing
those inputs onto an output channel. The output is an interleaving of the
messages from the input channels. The output must be all and only the
messages read from the inputs, and it must preserve the order in which they
were read on each channel. Infinite merging can be specified formally as
follows. Let the input channels be $`c` and $`d`, and the output channel be $`e`.
Then $`\mathit{merge} = (c?.\ e!\,c) \lor (d?.\ e!\,d).\ \mathit{merge}`. This specification does not
state any criterion for choosing between the input channels at each step. ...
Exercise 521(a) (time merge) asks us to choose the first available input at
each step. If input is already available on both channels $`c` and $`d`, take
either one; if input is available on just one channel, take that one; if input
is available on neither channel, wait for the first one and take it (in case of
a tie, take either one). Here is the specification.
$`\mathit{timemerge} = (\surd c \lor \mathcal{T}_c\,r_c \le \mathcal{T}_d\,r_d) \land (c?.\ e!\,c) \lor (\surd d \lor \mathcal{T}_c\,r_c \ge \mathcal{T}_d\,r_d) \land (d?.\ e!\,d).\ \mathit{timemerge}`.
To account for the time spent waiting for input, we should insert
$`t := t \uparrow (\mathcal{T}r + 1)` just before each input operation, and for recursive
time we should insert $`t := t+1` before the recursive call. In Subsection 9.1.2
on Communication Timing we proved that waiting for input can be implemented
recursively. Using the same reasoning, we implement $`\mathit{timemerge}` as follows.
$`\mathit{timemerge} \Leftarrow \mathbf{if}\ \surd c\ \mathbf{then}\ c?.\ e!\,c\ \mathbf{else}\ \mathit{ok}.\ \mathbf{if}\ \surd d\ \mathbf{then}\ d?.\ e!\,d\ \mathbf{else}\ \mathit{ok}.\ t := t+1.\ \mathit{timemerge}`
where time is an extended natural." Three channels, the transit-time check of
{uses "communication_timing"}[], and the recursive call as a specification as
in {uses "recursive_communication"}[]; $`\mathit{timemerge}` includes the waits and
the time increment the book says to insert. Proved: one step of
$`\mathit{merge}` reads one message from $`c` or $`d` and writes exactly that message on
$`e` at the current time ("all and only the messages read"); and an iteration of
the implementation is a $`\mathit{timemerge}` step when input is available on exactly
one channel. Honesty note: the book asserts the implementation "using the
same reasoning" and gives no proof. An iteration of the implementation is
*not* in general one $`\mathit{timemerge}` step — with input on both channels it reads
both, with input on neither it reads nothing and lets time pass — and the
two-input case is given as a counterexample to the step-wise refinement. The
book's refinement is one of fixed points (a two-input iteration is two steps,
a no-input iteration is the waiting hidden in $`t := t \uparrow (\mathcal{T}r+1)`) and is
not formalized here. Uses {uses "backtracking"}[] (for $`\lor`).
:::

:::definition "monitor" (parent := "interaction_core") (lean := "LaPToP.Interaction.MonS, LaPToP.Interaction.Monitor.checkIn0, LaPToP.Interaction.Monitor.checkIn1, LaPToP.Interaction.Monitor.checkReq0, LaPToP.Interaction.Monitor.checkReq1, LaPToP.Interaction.Monitor.m, LaPToP.Interaction.Monitor.act0, LaPToP.Interaction.Monitor.act1, LaPToP.Interaction.Monitor.act2, LaPToP.Interaction.Monitor.act3, LaPToP.Interaction.Monitor.tick, LaPToP.Interaction.Monitor.monitorBody, LaPToP.Interaction.Monitor.implBody, LaPToP.Interaction.Monitor.onlyIn0, LaPToP.Interaction.Monitor.onlyIn1, LaPToP.Interaction.Monitor.onlyReq0, LaPToP.Interaction.Monitor.onlyReq1, LaPToP.Interaction.Monitor.step_refines_in0, LaPToP.Interaction.Monitor.step_refines_in1, LaPToP.Interaction.Monitor.step_refines_req0, LaPToP.Interaction.Monitor.step_refines_req1")
"To obtain the effect of a fully shared variable, we create a process called a
monitor that resolves conflicting uses of the variable. Whenever the monitor
receives data from another process on one of the channels $`\mathit{xin}_0`,
$`\mathit{xin}_1`, ... to be written to variable $`x`, it writes the data to $`x`, and
sends an acknowledgement back to the process on one of the channels
$`\mathit{xack}_0`, $`\mathit{xack}_1`, ... . Whenever the monitor receives a request from
another process on one of the channels $`\mathit{xreq}_0`, $`\mathit{xreq}_1`, ... to read
variable $`x`, it sends the value of $`x` back to the requesting process on one of
the channels $`\mathit{xout}_0`, $`\mathit{xout}_1`, ... . A monitor for variable $`x` with two
writing processes and two reading processes can be defined as follows. Let $`m`
be the minimum of the times of the next input on each of the input channels.
$`m = \Downarrow [\mathcal{T}_{\mathit{xin}_0}\,r_{\mathit{xin}_0}; \mathcal{T}_{\mathit{xin}_1}\,r_{\mathit{xin}_1}; \mathcal{T}_{\mathit{xreq}_0}\,r_{\mathit{xreq}_0}; \mathcal{T}_{\mathit{xreq}_1}\,r_{\mathit{xreq}_1}]`
$`\mathit{monitor} = (\surd \mathit{xin}_0 \lor \mathcal{T}_{\mathit{xin}_0}\,r_{\mathit{xin}_0} = m) \land (\mathit{xin}_0?.\ x := \mathit{xin}_0.\ \mathit{xack}_0!\,\top) \lor (\surd \mathit{xin}_1 \lor \ldots) \land (\mathit{xin}_1?.\ x := \mathit{xin}_1.\ \mathit{xack}_1!\,\top) \lor (\surd \mathit{xreq}_0 \lor \ldots) \land (\mathit{xreq}_0?.\ \mathit{xout}_0!\,x) \lor (\surd \mathit{xreq}_1 \lor \ldots) \land (\mathit{xreq}_1?.\ \mathit{xout}_1!\,x).\ \mathit{monitor}`
Just like $`\mathit{timemerge}`, a monitor takes the first available input and
responds to it. ... Here's one way to implement a monitor, assuming time is an
extended natural:
$`\mathit{monitor} \Leftarrow \mathbf{if}\ \surd \mathit{xin}_0\ \mathbf{then}\ \mathit{xin}_0?.\ x := \mathit{xin}_0.\ \mathit{xack}_0!\,\top\ \mathbf{else}\ \mathit{ok}.\ \mathbf{if}\ \surd \mathit{xin}_1\ \mathbf{then} \ldots \mathbf{else}\ \mathit{ok}.\ \mathbf{if}\ \surd \mathit{xreq}_0\ \mathbf{then}\ \mathit{xreq}_0?.\ \mathit{xout}_0!\,x\ \mathbf{else}\ \mathit{ok}.\ \mathbf{if}\ \surd \mathit{xreq}_1\ \mathbf{then} \ldots \mathbf{else}\ \mathit{ok}.\ t := t+1.\ \mathit{monitor}`."
Defined as for {uses "merge"}[] (four input and four output channels, the
variable $`x`, the minimum $`m`, the recursive-time increment), and, as for the
merge, an iteration of the implementation is proved to be a monitor step
whenever exactly one input channel has input available (four lemmas, one per
channel); the same honesty note applies to the book's implementation.
:::

:::theorem "channel_declaration" (parent := "interaction_core") (tags := "interaction, channels, declaration, hehner-9.1.7") (effort := "medium") (lean := "LaPToP.Interaction.Channel.assignLast, LaPToP.Interaction.Channel.output_input_assign, LaPToP.Interaction.Channel.not_last_written, LaPToP.Interaction.newChannel, LaPToP.Interaction.liftChan, LaPToP.Interaction.newChannel_liftChan, LaPToP.Interaction.Channel.wait, LaPToP.Interaction.Channel.buffer, LaPToP.Interaction.Channel.newChannel_buffer, LaPToP.Interaction.Channel.outParIn, LaPToP.Interaction.Channel.outParInT, LaPToP.Interaction.Channel.not_last_written_par, LaPToP.Interaction.Channel.newChannel_outParIn, LaPToP.Interaction.Channel.newChannel_outParInT")
"The next input on a channel is not necessarily the one that was last
previously written on that channel. In one variable $`x` and one channel $`c`
(ignoring time), $`c!\,2.\ c?.\ x := c = \mathcal{M}w = 2 \land w' = w+1 \land r' = r+1 \land x' = \mathcal{M}r`.
We do not know that initially $`w = r`, so we cannot conclude that finally
$`x' = 2`. That's because there may have been a previous write that hasn't been
read yet. ... The same is true in a concurrent composition. ... In order to
achieve useful communication between processes, we have to introduce a local
channel. Channel declaration is similar to variable declaration; it defines a
new channel within some local portion of a program or specification.
$`\mathbf{new}\ c?!\,T \cdot S = \exists \mathcal{M}_c : \infty{*}T \cdot \exists \mathcal{T}_c : \infty{*}\mathit{xnat} \cdot \mathbf{new}\ r_c, w_c : \mathit{xnat} := 0 \cdot S = \exists \mathcal{M}_c \cdot \exists \mathcal{T}_c \cdot \exists r_c, r_c', w_c, w_c' : \mathit{xnat} \cdot r_c = w_c = 0 \land S`.
This declaration introduces new channel $`c` for input and output whose
communications are of type $`T`. ... A local channel can be used without
concurrency as a queue, or buffer. For example,
$`\mathbf{new}\ c?!\,\mathit{int} \cdot c!\,3.\ c!\,4.\ c?.\ x := c.\ c?.\ x := x+c` assigns $`7` to $`x`. Here is
the proof, including time. ... $`= x' = 7 \land t' = t+1 \land (\text{other variables unchanged})`.
Here are two processes with a communication between them. Ignoring time,
$`\mathbf{new}\ c?!\,\mathit{int} \cdot c!\,2 \parallel (c?.\ x := c) = \ldots = x' = 2 \land (\text{other variables unchanged}) = x := 2`.
Replacing $`2` by an arbitrary expression, we have a general theorem equating
communication on a local channel with assignment. If we had included transit
time, the result would have been $`x' = 2 \land t' = t+1 \land \ldots = x := 2 \parallel t := t+1`."
The declaration quantifies the scripts and the final cursors and fixes the
initial cursors at $`0` (the one-point law for $`r_c = w_c = 0` already applied);
outside it the state is the time and $`x` of {uses "time_variable"}[], as for
{uses "variable_declaration"}[]. Proved: the expansion of $`c!\,2.\ c?.\ x := c`
and a counterexample to $`x' = 2` (an unread earlier output); a specification
not mentioning the channel is unchanged by the declaration; the buffer
example with the input waits of {uses "communication_timing"}[],
$`x' = 7 \land t' = t+1`; and the general theorem
$`\mathbf{new}\ c?!\,\mathit{int} \cdot c!\,e \parallel (c?.\ x := c) = x := e`, with $`t' = t+1` in the
transit time measure. Model note: the concurrent composition
$`c!\,e \parallel (c?.\ x := c)` is taken as the book's own expansion
$`\mathcal{M}w = e \land w' = w+1 \land r' = r+1 \land x' = \mathcal{M}r` (cf. {uses "concurrent_composition"}[]);
a general $`\parallel` on channel states is not defined. Uses {uses "communication"}[].
:::

:::definition "reaction_controller" (parent := "interaction_core") (lean := "LaPToP.Interaction.SyS, LaPToP.Interaction.Synchronizer.inputDD, LaPToP.Interaction.Synchronizer.inputReq, LaPToP.Interaction.Synchronizer.latest, LaPToP.Interaction.Synchronizer.outputRep, LaPToP.Interaction.Synchronizer.checkReq, LaPToP.Interaction.Synchronizer.inputReq_outputRep_comm, LaPToP.Interaction.Synchronizer.synchronizerBody, LaPToP.Interaction.Synchronizer.synchronizerBody_step")
"Many kinds of reactions are controlled by a feedback loop ... The sensors send
their data continuously to the digitizer. The digitizer is fast and uniform,
sending digital data rapidly to the controller. The time required by the
controller to compute its output messages varies according to the input
messages ... When several inputs have piled up, the controller should not
continue to read them and compute outputs in the hope of catching up. Instead,
we want all but the latest input to be discarded. ... The solution is to place a
synchronizer between the digitizer and controller. ... It repeatedly reads the
data from the digitizer, always keeping only the latest. Whenever the
controller requests some data, the synchronizer sends the latest. This is
exactly the function of a monitor, and we could implement the synchronizer
that way. But a synchronizer is simpler than a monitor in three respects:
first, there is only one writing process (digitizer) and one reading process
(controller); second, the writing process does not need an acknowledgement;
and last, the writing process is uniformly faster than the reading process.
Here is its definition.
$`\mathit{synchronizer} = \mathit{digitaldata}?.\ \mathbf{if}\ \surd \mathit{request}\ \mathbf{then}\ \mathit{request}? \parallel \mathit{reply}!\,\mathit{digitaldata}\ \mathbf{else}\ \mathit{ok}.\ \mathit{synchronizer}`."
Defined on a state with the channels $`\mathit{digitaldata}`, $`\mathit{request}`, $`\mathit{reply}`;
the $`\parallel` of an input on one channel and an output on another is rendered
as their sequential composition, which is proved to commute. One step of the
synchronizer reads a datum and, if there is a request, replies with exactly
that datum — "the latest". A simplification of the {uses "monitor"}[]; uses
{uses "channel_declaration"}[].
:::

:::theorem "deadlock" (parent := "interaction_core") (tags := "interaction, channels, deadlock, hehner-9.1.8") (effort := "small") (lean := "LaPToP.Interaction.enat_eq_top_of_add_one_le, LaPToP.Interaction.enat_eq_top_of_eq_max_succ, LaPToP.Interaction.enat_eq_top_of_mutual_wait, LaPToP.Interaction.Channel.readThenWrite, LaPToP.Interaction.Channel.newChannel_readThenWrite, LaPToP.Interaction.DS, LaPToP.Interaction.newChannel2, LaPToP.Interaction.Deadlock.mutualWait, LaPToP.Interaction.Deadlock.newChannel2_mutualWait")
"In the previous subsection we saw that a local channel can be used as a
buffer. Let's see what happens if we try to read first and write after
(Exercise 528(a)). Inserting the input wait into $`\mathbf{new}\ c?!\,\mathit{int} \cdot c?.\ c!\,5`
we get $`\mathbf{new}\ c?!\,\mathit{int} \cdot t := t \uparrow (\mathcal{T}r + 1).\ c?.\ c!\,5 = \ldots = \exists \mathcal{M} \cdot \exists \mathcal{T} \cdot \mathcal{M}0 = 5 \land \mathcal{T}0 = t \uparrow (\mathcal{T}0 + 1) \land \ldots`
Look at the conjunct $`\mathcal{T}0 = t \uparrow (\mathcal{T}0 + 1)`. It says $`\mathcal{T}0 = \infty`.
$`= x' = x \land t' = \infty`. The theory tells us that execution takes forever because
the wait for input is infinite. The word “deadlock” is usually used to mean
that several processes are waiting on each other ... But it might also be
used to mean that a single sequential computation is waiting on itself, as in
the previous paragraph. Here's the more traditional example with two
processes and two local channels (Exercise 528(b)).
$`\mathbf{new}\ c, d?!\,\mathit{int} \cdot (c?.\ d!\,6) \parallel (d?.\ c!\,7)`. Inserting the input waits, we get
$`\mathbf{new}\ c, d?!\,\mathit{int} \cdot (t := t \uparrow (\mathcal{T}_c\,r_c + 1).\ c?.\ d!\,6) \parallel (t := t \uparrow (\mathcal{T}_d\,r_d + 1).\ d?.\ c!\,7)`
after a little work, we obtain
$`= \exists \mathcal{M}_c, \mathcal{M}_d \cdot \exists \mathcal{T}_c, \mathcal{T}_d \cdot \exists r_c, r_c', w_c, w_c', r_d, r_d', w_d, w_d' \cdot \mathcal{M}_d 0 = 6 \land \mathcal{T}_d 0 = t \uparrow (\mathcal{T}_c 0 + 1) \land \mathcal{M}_c 0 = 7 \land \mathcal{T}_c 0 = t \uparrow (\mathcal{T}_d 0 + 1) \land r_c' = w_c' = r_d' = w_d' = 1 \land x' = x \land t' = t \uparrow (\mathcal{T}_c 0 + 1) \uparrow (\mathcal{T}_d 0 + 1)`.
The conjuncts $`\mathcal{T}_d 0 = t \uparrow (\mathcal{T}_c 0 + 1)` and $`\mathcal{T}_c 0 = t \uparrow (\mathcal{T}_d 0 + 1)` imply
$`\mathcal{T}_d 0 = \mathcal{T}_c 0 = \infty`. $`= x' = x \land t' = \infty`. To prove that a computation is free
from deadlock, prove that all message times are finite." Both exercises are
proved as equalities, on the {uses "channel_declaration"}[] (a two-channel
declaration is defined the same way), with the input waits of
{uses "communication_timing"}[]; the $`\mathit{xnat}` facts are $`a + 1 \le a \Rightarrow a = \infty`,
hence $`a = t \uparrow (a+1) \Rightarrow a = \infty`, and the mutual-wait lemma. Model note:
the concurrent composition of 528(b) is taken as the book's own expansion
"after a little work" (cf. {uses "concurrent_composition"}[]), with $`r_c, w_d`
belonging to the left process and $`r_d, w_c` to the right.
:::

:::definition "broadcast" (parent := "interaction_core") (lean := "LaPToP.Interaction.BS, LaPToP.Interaction.Broadcast.input, LaPToP.Interaction.Broadcast.lastRead, LaPToP.Interaction.Broadcast.output, LaPToP.Interaction.Broadcast.parReaders, LaPToP.Interaction.Broadcast.input_lastRead, LaPToP.Interaction.Broadcast.parReaders_input")
"A channel consists of a message script, a time script, a read cursor, and a
write cursor. Whenever a computation splits into concurrent processes, the
state variables must be partitioned among the processes. The scripts are not
state variables; they do not belong to any process. The cursors are state
variables, so one of the processes can write to the channel, and one (perhaps
the same one, perhaps a different one) can read from the channel. ... A
communication channel must have only a single writing process, but it can
have more than one reading process. This is called a broadcast. In the
program structure $`P.\ (Q \parallel R \parallel S).\ T` we might want $`Q` to write, and both
of $`R` and $`S` to read, all on the same channel. Broadcast is achieved by
several read cursors, one for each reading process. Then all reading
processes read the same messages, each at its own rate. There is no harm in
two processes reading the same message, even at the same time. But there is a
problem with broadcast: what is the final value of the read cursor for the
concurrent composition? ... The solution is to say that the final time for the
concurrent composition is the maximum of the final times of the processes.
The same solution works for the read cursor. For each channel, the final
value of the read cursor in a concurrent composition is the maximum of the
final values of the read cursors of the processes." A broadcast channel has
one write cursor and $`k` read cursors; the input of reader $`i` advances its own
cursor, and $`c` in reader $`i` is the message it last read; the concurrent
composition of two readers takes the maximum of the final read cursors and
times. Proved: a reader reads the message at its own cursor, and two readers
each reading once end with each cursor advanced once ("no harm in two
processes reading the same message"). Uses {uses "communication"}[] and
{uses "deadlock"}[].
:::

:::theorem "power_series_multiplication" (parent := "interaction_core") (tags := "interaction, channels, recursion, hehner-9.1.10") (effort := "large") (lean := "LaPToP.Interaction.PowerSeries.conv, LaPToP.Interaction.PowerSeries.conv_zero, LaPToP.Interaction.PowerSeries.conv_one, LaPToP.Interaction.PowerSeries.conv_succ_succ, LaPToP.Interaction.PowerSeries.P, LaPToP.Interaction.PowerSeries.Loop, LaPToP.Interaction.PowerSeries.loop_step, LaPToP.Interaction.PowerSeries.main_step, LaPToP.Interaction.PowerSeries.QS, LaPToP.Interaction.PowerSeries.inputA, LaPToP.Interaction.PowerSeries.inputB, LaPToP.Interaction.PowerSeries.inputD, LaPToP.Interaction.PowerSeries.outputC, LaPToP.Interaction.PowerSeries.inputs, LaPToP.Interaction.PowerSeries.inputA_inputB_comm, LaPToP.Interaction.PowerSeries.inputB_inputD_comm, LaPToP.Interaction.PowerSeries.LoopSpec, LaPToP.Interaction.PowerSeries.loop_refines")
"To end, we present an example that combines communicating processes, local
channel declaration, and dynamic process generation, in one beautiful little
program. ... Exercise 527 is multiplication of power series: Write a program
to read from channel $`a` an infinite sequence of coefficients $`a_0\,a_1\,a_2\,a_3 \ldots`
of a power series $`a_0 + a_1 \times x + a_2 \times x^2 + a_3 \times x^3 + \ldots` and
concurrently to read from channel $`b` an infinite sequence of coefficients
$`b_0\,b_1\,b_2\,b_3 \ldots` ... and concurrently to write on channel $`c` the infinite
sequence of coefficients $`c_0\,c_1\,c_2\,c_3 \ldots` of the power series ... equal to
the product of the two input series. Assume that all inputs are already
available; there are no input delays. Produce the outputs one per time unit.
The question provides us with a notation for the coefficients:
$`a_n = \mathcal{M}_a\,(r_a+n)`, $`b_n = \mathcal{M}_b\,(r_b+n)`, and $`c_n = \mathcal{M}_c\,(w_c+n)`. ...
$`C = A \times B \land \forall n \cdot \mathcal{T}_c\,(w_c+n) = t+n` ... from which we see
$`c_n = \Sigma i : 0,..n+1 \cdot a_i \times b_{n-i}`. ...
$`A \times B = a_0 \times b_0 + (a_0 \times b_1 + a_1 \times b_0) \times x + (a_0 \times B_2 + A_1 \times B_1 + A_2 \times b_0) \times x^2`.
... We need a channel parameter, for which we invent the notation
$`\langle c?!\,T \cdot S \rangle`. ... $`P = \langle c?!\,\mathit{rat} \cdot C = A \times B \rangle`. We refine $`P\,c` as
follows.
$`P\,c \Leftarrow (a? \parallel b?).\ c!\,a \times b.\ \mathbf{new}\ a_0 : \mathit{rat} := a \cdot \mathbf{new}\ b_0 : \mathit{rat} := b \cdot \mathbf{new}\ d?!\,\mathit{rat} \cdot P\,d \parallel ((a? \parallel b?).\ c!\,a_0 \times b + a \times b_0.\ C = a_0 \times B + D + A \times b_0)`
$`C = a_0 \times B + D + A \times b_0 \Leftarrow (a? \parallel b? \parallel d?).\ c!\,a_0 \times b + d + a \times b_0.\ C = a_0 \times B + D + A \times b_0`
That is the whole program: 4 lines! ... Both $`P\,d` and its concurrent process
will be reading from channels $`a` and $`b` using separate read cursors. ... The
proof is completely straightforward. Here it is in detail. We start with the
right side of the first refinement, leaving out time. ... Make all
substitutions indicated by assignment
$`= \mathcal{M}_c\,w_c = \mathcal{M}_a\,r_a \times \mathcal{M}_b\,r_b \land \exists a_0, \ldots \cdot (\forall n \cdot d_n = \Sigma i : 0,..n+1 \cdot \mathcal{M}_a\,(r_a+1+i) \times \mathcal{M}_b\,(r_b+1+n-i)) \land \mathcal{M}_c\,(w_c+1) = \mathcal{M}_a\,r_a \times \mathcal{M}_b\,(r_b+1) + \mathcal{M}_a\,(r_a+1) \times \mathcal{M}_b\,r_b \land (\forall n \cdot \mathcal{M}_c\,(w_c+2+n) = \mathcal{M}_a\,r_a \times \mathcal{M}_b\,(r_b+2+n) + d_n + \mathcal{M}_a\,(r_a+2+n) \times \mathcal{M}_b\,r_b)`
Use the first universal quantification to replace $`d_n` in the second. ... Now
put the three conjuncts together
$`= \forall n \cdot \mathcal{M}_c\,(w_c+n) = \Sigma i : 0,..n+1 \cdot \mathcal{M}_a\,(r_a+i) \times \mathcal{M}_b\,(r_b+n-i) = P\,c`.
We still have to prove the loop refinement. ... Make all substitutions
indicated by assignment
$`= \mathcal{M}_c\,w_c = a_0 \times \mathcal{M}_b\,r_b + \mathcal{M}_d\,r_d + \mathcal{M}_a\,r_a \times b_0 \land \forall n \cdot \mathcal{M}_c\,(w_c+1+n) = a_0 \times \mathcal{M}_b\,(r_b+1+n) + \mathcal{M}_d\,(r_d+1+n) + \mathcal{M}_a\,(r_a+1+n) \times b_0`
Put the two conjuncts together $`= C = a_0 \times B + D + A \times b_0`." Coefficients are
rationals. The mathematical heart is the convolution identity
$`c_{n+2} = a_0 \times b_{n+2} + (A_1 \times B_1)_n + a_{n+2} \times b_0` with $`c_0 = a_0 \times b_0` and
$`c_1 = a_0 \times b_1 + a_1 \times b_0` ({uses "quantifier_numeric"}[]). The loop
refinement is proved at the program level, on a state with the cursors
$`r_a, r_b, r_d, w_c`, with the recursive call as a specification
({uses "recursive_communication"}[]) and the inputs on distinct channels
composed sequentially (they commute). The first refinement — which uses the
local channel $`d` ({uses "channel_declaration"}[]), local constants, and the
process $`P\,d` reading $`a` and $`b` with separate read cursors
({uses "broadcast"}[]) concurrently with the main process
({uses "concurrent_composition"}[]) — is proved at the level of the book's
displayed line after "make all substitutions indicated by assignment": those
conjuncts imply $`P\,c`. The substitution step with process generation is not
modelled as a program, and the remarks on placing time increments are not
formalized.
:::
