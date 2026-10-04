# laptop (LaPToP)

Lean formalization of Eric Hehner's *A Practical Theory of Programming*, with a
[Verso Blueprint](https://github.com/leanprover/verso-blueprint) site.

## Toolchain

- Lean: `leanprover/lean4:v4.33.1` (latest stable)
- Blueprint: `leanprover/verso-blueprint` **v4.33.0**
- Mathlib: pinned to **v4.33.1**; always use precompiled oleans (`lake exe cache get`)

## Build the Blueprint site (HTML only)

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /path/to/laptop
lake update          # first time / after dependency changes
lake exe cache get   # never compile Mathlib from scratch
./scripts/ci-pages.sh
```

Successful runs write the multi-page HTML site under:

```text
_out/site/html-multi/index.html
```

`./scripts/ci-pages.sh` is the same check the GitHub Pages workflow runs. It
does **not** build PDF (`--pdf` is intentionally omitted from CI).

## Run a program (`lake exe interp`)

The programming notations of Chapters 4 and 5 are not only specified but
executed: `LaPToP/ProgramTheory/Interpreter.lean` is an interpreter for them,
and `interp` runs programs written in the language of
`LaPToP/ProgramTheory/InterpreterLang.lean`.

```bash
lake build interp                      # first time: compiles the exe (a few minutes)
lake exe interp --help                 # options
lake exe interp --grammar              # the grammar of the concrete syntax
lake exe interp --demo=sumTo --n=10    # => n = 10, i = 10, s = 55
lake exe interp --selftest             # the sources parse to the proved programs
echo 'i:= 0. s:= 0. while i ≠ n do i:= i+1. s:= s+i od' | lake exe interp --n=20
echo 's:= 0 or s:= 1. ensure s = 1' | lake exe interp --all   # backtracking
echo 'while i ≠ n do i:= i+1. tick od' | lake exe interp --n=7 --timed
echo '(s:= 1 or s:= 2). assert s = 1' | lake exe interp --timed --all
echo 'A:= [0;0;0;0;0]. A 2:= 3. i:= 2. A i:= 4. b:= A i = A 2' | lake exe interp
lake exe interp --L='[5;3;9;1]' sort.ap   # a program in a file, with an initial list
lake exe interp --demo=listSum --L='[3;1;4;1;5]'   # the refinements of Section 4.1.1
lake exe interp --demo=deepExit                    # do ... exit 2 when ... od
```

A program file may be written the book's way, as refinements; a name on the
right is a call, and may be recursive:

```
-- Towers of Hanoi (Section 4.3): one tick per disk move
MovePile ⇐ if n = 0 then ok
           else n:= n-1. MovePile. moves:= moves+1. tick. MovePile. n:= n+1 fi
```

`lake exe interp --n=10 --timed hanoi.ap` reports `moves = 1023, time = 1023`.
A specification may take parameters, `MovePile(from, to, using) ⇐ ...`, called as
`MovePile(0, 1, 2)`; `x, y:= y, x` assigns simultaneously.

Channels are the book's (Section 9.1.1): `c! e` outputs, `c?` inputs, `c` is the
last message input and `√c` says one is waiting. A channel's script is the list
variable of its name, so input is supplied on the command line:

```bash
echo 'keyboard?. a:= keyboard. keyboard?. screen! a + keyboard' | lake exe interp --keyboard='[3;4]'
# => keyboard = [3; 4], screen = [7], a = 3
```

`P || Q` is concurrent composition (Section 8.0): each process owns the
variables it assigns and sees the other's only at their initial values, so
`x:= y || y:= x` swaps; on the clock it finishes when both processes have.

A program with channels and a `||` is a network of communicating processes
(Chapter 9, `LaPToP/ProgramTheory/Network.lean`): the processes of the main `||`,
each parenthesized, run concurrently with their own variables, communicate only
on channels, and a message arrives one unit of time after it is sent (§9.1.2).
The machine that runs them is proved determinate (any order of turns gives the
same result), sound and complete for the book's semantics, in which the scripts
are constants some choice makes consistent; a run that stops with a process
waiting for input that never comes is a deadlock, and the time is `∞`. `--net`
runs any program this way, for a process fed from the command line:

```bash
echo '(c! 3. tick. c! 4) || (c?. y:= c. c?. x:= c)' | lake exe interp
# => y = 3, x = 4, time = 2
#    c = [3; 4] sent at [0; 1]
echo '(c?. d! 2) || (d?. c! 1)' | lake exe interp     # => time = ∞, deadlock
echo 'S ⇐ c?. d! 2×c. S' | lake exe interp --net --c='[1;2;5]'
# => d = [2; 4; 10] sent at [1; 1; 1], then waits for more input
```

Probabilistic programs are the book's (Section 5.7): `if 1/3 then x:= 0 else x:= 1 fi`
and `x:= rand n`, and `--dist` prints the exact distribution of the final states:

```bash
echo 'x:= rand 6. y:= rand 6. ensure x + y = 7' | lake exe interp --dist
# => 1/36: x = 2, y = 5   (and three more)   8/9: no final state ...
```
`do ... exit when b ... od` is the exit-loop (`exit n when b` leaves `n` loops) and
`for i:= m;..n do P od` the for-loop; both are compiled to the refinements the
book defines them by.

Variables have any names; their values are integers, binaries (`⊤`, `⊥`) and
lists (`[3; 1; 2]`), and a variable never assigned is `0`. `--NAME=EXP` gives a
variable its initial value. An array is a list variable, as in the book:
juxtaposition indexes (`A i`), and `A i:= e` is the book's `A:= i→e | A`. The
book's symbols (`≠ ≤ ≥ ∧ ∨ ¬ ⇒ ×`) are accepted, each with an ASCII spelling.
`--all` searches for every poststate (`runAll`) instead of running the
deterministic interpreter once, which is what a choice needs. `--timed` adds a
clock: `tick` advances it, and a false `assert` waits until `∞` where a false
`ensure` has no poststate at all. `--timed --all` searches on the clock
(`runAllT`), so a choice and a clock combine. Exit status is 1 for a parse error
and 2 when there is no poststate. `--fuel` bounds the depth of the execution, so a
loop of `n` iterations needs at least `n`; a deterministic run keeps its state in
an array, proved to compute what the interpreter computes, and a million loop
iterations take well under a second. Building the executable links the whole import
chain, so it is a separate target: plain `lake build` and the Blueprint site do
not build it.

## Compile to the b4 virtual machine

`LaPToP/ProgramTheory/CompileB4.lean` compiles the integer fragment of the
language (assignment, sequence, `if`, `while`, calls of named statements, local
variables, over `+ - × div mod`, `<`, `=`, `¬ ∧ ∨` and conditional expressions
`if c then a else b fi`, whose code hops relatively with `h0`) to bytecode for
[b4](https://github.com/tangentstorm/b4), a small stack machine with
implementations in many languages. Named statements are laid out from `0x100`
and called with b4's `cl`; a local variable keeps its old value on the control
stack. Its Lean implementation (required from git, `imp/lean`, with its theory
in `B4/Theory.lean`) runs the code, and `load_correct` proves the result:
whenever the language takes a state to another without any value leaving 32
bits (or the control stack overflowing), the loaded machine halts with the
variables holding the final state. The `sumTo` loop compiles to 86 bytes, and
b4 computes `s = 55` from `n = 10`.

Networks run on a swarm of b4 machines (`CompileNet.lean`, and `B4/Swarm.lean`
in b4): each process on its own machine, channels reached through b4's `io`
(`'s'` sends, `'r'` receives), time in register `T`. `swarm_correct` proves that
every 32-bit run of the network machine is matched by the swarm, which halts
with the network's variables, times and scripts — the book's semantics, by
`swarm_book`. Each channel has one writer, so the swarm is confluent and stops
in at most one state (`CompileNetDeadlock.lean`): a network that deadlocks is a
swarm that stops with machines still waiting (`stuck_of_waiting`), and a swarm
that stops so is a network that cannot finish (`no_finish_of_stuck`).
`interp --b4` compiles and runs a program or a network there:

```bash
lake exe interp --b4 --demo=sumTo --n=10        # => n = 10, i = 10, s = 55, time = 0
echo '(c! 3. tick. c! 4) || (c?. y:= c. c?. x:= c)' | lake exe interp --b4
# => y = 3, x = 4, time = 2
#    c = [3; 4] sent at [0; 1]
printf 'Fact(k) ⇐ if k = 0 then r:= 1 else Fact(k-1). r:= r × k fi\nFact(n)' \
  | lake exe interp --b4 --n=10               # => n = 10, k = 0, r = 3628800, time = 0
```
The language's own parser builds the compiler's statements beside each program
it reads, so `--b4` takes `do`/`exit` and `for` loops, `new`, simultaneous
assignment, specifications with parameters and recursion, `c! e`, `c?` and a `||`
of processes, over 32-bit integers and binaries. `≠ ≤ > ≥ ⇒ ⇐` and the big
`== --> <--` are rewritten into the compiled operators, `a ^ n` for a literal
`n` into a product, and `div`/`mod` by a divisor that may be negative into a
conditional expression (b4's `dv`/`md` agree with the book's floor division
only for a positive divisor). It names the first construct
it does not take, and warns when a value leaves 32 bits. `interp --selftest`
checks it against the interpreters on the demonstrations.

Arrays — a variable holding a list, read as `A i` and written as `A i:= e` —
get a cell per item after the variables (`run_addr`, `store_runs`), and keep
their length: `#A` is a literal (proved in `exp_runs`), and `A:= [e₀; …]` pushes
every item before storing any (`fill_runs`), so `A:= [A 2; A 1; A 0]` reverses
`A`. `A:= B` is copied item by item, an array that starts as a number starts
as zeros, and a two-dimensional array (`A i j`, `A i j:= e`, a list of lists)
is laid out by rows. On them,
`Alloc.lean` writes the memory allocator of b4's `mm.b4a` in the language and
proves it against its model of blocks (`alloc_sEval`, `free_sEval`), on b4 as
well (`alloc_on_b4`). Backtracking — `P or Q`, `ensure c` — runs too
(`CompileBT.lean`): a choice keeps a choice point above the cells, a failed
`ensure` takes the last one back, and the machine is proved to do what the
language's backtracking does, finding a poststate the program has
(`bt_success`, `bt_sound`) or, when the search fails, none at all
(`bt_failure`, `bt_fail_sound`):
```sh
echo 's:= 0 or s:= 1. ensure s = 1' | lake exe interp --b4          # => s = 1, time = 0
lake exe interp --b4 --demo=subset --t=19
# => ... X = [0; 0; 0; 1; 1; 1], i = 6, s = 19, time = 0
echo 'A:= [[1;2];[3;4]]. A 0 1:= A 1 0 + A 1 1' | lake exe interp --b4
# => A = [[1; 7]; [3; 4]], time = 0
```

## Prove a theorem by calculation (`lake exe netty`)

Netty is a prover's assistant for calculational proofs — the tool described in
[the Netty document](https://www.cs.toronto.edu/~naiman/Netty_document.pdf) by
Eric Hehner, Robert Will, Lev Naiman and David Kordalewski. It keeps the proof,
its direction, the context and the law lists, and suggests the next line by
*showing what applying each law would write*. `Netty/` is its kernel: the
document model, the law matching, the suggestions and the save format, with no
user interface but a script language.

```bash
lake build netty                      # a few seconds: it needs neither Mathlib nor LaPToP
lake exe netty --help                 # options and the script language
lake exe netty --demo=portation       # the example proof from page 0 of the document
lake exe netty --demo=discharge       # zooming in, and the context a zoom in supplies
lake exe netty --demo=gap             # a gap left by direct entry, and closing it
lake exe netty --demo=minimize        # a law applied to a part of a line
lake exe netty --demo=segment         # a law applied to a segment of an association
lake exe netty --demo=segfold         # the same fold, by zooming into that segment
lake exe netty --list-laws            # the boolean laws in force
lake exe netty --selftest             # laws, law file and demonstrations
printf 'start ⇐ a ⇒ (b ⇒ a)\nsuggest\n' | lake exe netty
```

The `portation` demonstration replays the document's own first example and
prints its proof pane:

```
    0   [⇐] a ⇒ (b ⇒ a)   portation
    1    =  a ∧ b ⇒ a     specialization
>   2    =  ⊤
proves a ⇒ (b ⇒ a) = ⊤, that is, proves a ⇒ (b ⇒ a)
```

A law is matched against the line *modulo associativity*: the document says
that clicking any operand of `a + b + c` zooms in to it with no need of
associative laws, and applying a law reads a line the same way, so
`specialization`, `a ∧ b ⇒ a`, offers both `x` and `x ∧ y` from `x ∧ y ∧ z`.
Each reading is a suggestion of its own.

A law is also matched against each **part** of the line, which is the
document's applying it "to a part, as a result of minimization": `a ∨ a = a`
does not match `x ∧ (y ∨ y)` at all, but it folds its second operand, so
`x ∧ (y ∨ y) = x ∧ y` is one step instead of a zoom in, an application and a
zoom out. The parts are the main operands and, when the main operator is
associative, every contiguous **segment** of the association — the document
reads `x ∧ y ∧ z` as having the part `y ∧ z` just as it has the part `y` — so
`a ∧ a = a` takes `x ∧ y ∧ y ∧ z` to `x ∧ y ∧ z` in one step, folding the middle
two conjuncts and leaving the rest alone. The margin connective is the one
zooming out would have written, so a negative position turns the step around:
`x ≤ x + 1` on the subtrahend of `n - m` gives `n - m ≥ n - (m + 1)`, and a
neutral one — a factor of `×`, say — admits only `=`.

Every part is also a **level you can work inside**: `zoom 1` opens a subproof on
the first main operand and `zoom 1:2` on the two operands from the first, a
contiguous segment. The subproof's first line is that part, with the type,
direction and context the part carries, and `out` splices its bottom line back
where the part stood — the same `Part.replace` a one-step rewrite uses, so the
long way round and the short way round write the same line and the display draws
them alike.

The suggestions are *ranked*, by a heuristic written down in `Doc.rank` rather
than learned: the steps that can be taken before the ones that leave a law
variable free, fewer free variables, then the **shorter line** a step writes — so
a fold comes before the padding of the same law — then the place it rewrites (the
whole line, a single operand, the shorter runs of operands), and last the law
file's own order. The same line and the same laws always give the same list, so a
number read off the pane means the same thing the next time.

The shorter line outranks the place on purpose. `a ∧ a ≡ a` folds
`x ∧ y ∧ y ∧ z` to `x ∧ y ∧ z`, which no rewrite of the whole line and no rewrite
of a single operand can do; ordering by place first buried it 124 suggestions
deep, behind every way of reassociating and commuting the whole line. It is now
the third of the 227 offered.

Laws are plain text files (`Netty/laws/boolean.laws` holds the Binary laws of
aPToP §11.3.1); add your own with `--laws=FILE`. `Netty/Laws.lean` reads the
shipped file at compile time and `Netty.boolean_isTautology` checks in Lean's
kernel that every law in it is a tautology; `Netty/Replay.lean` replays every
demonstration in Lean and proves that each ends with no gaps, fully
zoomed out, and proving the formula it claims. Exit status is 1 when a `check`
fails and 2 for a bad script or law file.

### The three panes in a browser (`netty-web/`)

`netty --serve` answers one JSON request per line of standard input with the
whole state of the session — every line with its depth, its margin connective
and its main operands, the context, the numbered suggestions, and what the
proof proves — which is what a window with three panes needs and a terminal
does not. `netty-web/` is that window: a Node server that forwards a request to
the kernel, and a TypeScript client that draws the proof, context and
suggestion panes and turns a click into one line of the script language.

```bash
lake build netty
cd netty-web && npm install && npm run serve   # http://127.0.0.1:4173/
```

The model is not duplicated in TypeScript: a click on a suggestion is
`apply #N`, a click on a line number is `focus N`, and a click on a part of the
line before the focus is `zoom` and the name the kernel gave that part — `N` for
a main operand, `S:L` for a contiguous segment of an association, the runs the
client draws under the line. The client never composes those names, so a click
cannot mean a different part from the one a suggestion's site or a script zoom
means, and every change still goes through `Netty.Doc.step`. `netty-web/README.md`
has the details; `netty --selftest` checks the request service too, by replaying
each demonstration through it and saving and loading the result.

## GitHub Pages

Workflows:

- `.github/workflows/pages.yml` — caller (PR build + deploy on `main`)
- `.github/workflows/blueprint-pages.yml` — reusable build/deploy

After merge, enable Pages once (repo admin):

**Settings → Pages → Build and deployment → Source: GitHub Actions**

The public URL will be:

**https://tangentproofs.github.io/laptop/**

Do not enable Pages via API from automation; a human should flip that switch.

## Coverage

Every section of Chapters 1–9 of the book is formalized, and the law tables of
the Reference chapter (§11.3) are surveyed law by law. The Blueprint nodes are
formalized and sorry-free (the old `collatz_conjecture` demo node was removed;
Exercise 255 timing remains as `collatz_time`). Chapter 10 exercise *statements*
are deferred stubs in `LaPToP/Exercises/` (signatures with `sorry` only). What
is intentionally not formalized is listed in `MISSING.md`.

| Blueprint chapter | Book sections |
|---|---|
| Prelude | §1.0 Binary Theory |
| Basic Theories | §1.0.1 calculation, §1.1 numbers, §2.0–2.1 bunches and sets; §11.3.0 Generic laws |
| Function Theory | §3.0–3.4 functions, quantifiers, fine points, functions as data, limits and reals; §11.3.7–11.3.9 laws |
| Data Structures | §2.2–2.3 strings, lists and multidimensional structures |
| Program Theory | §4.0–4.4 specifications, refinement, time, space, old program theory; §11.3.10–11.3.13 laws |
| Programming Language | §5.0–5.8 scope, data structures, loops, time and space dependence, assertions, subprograms, alias, probabilistic and functional programming |
| Recursion and Concurrency | §6.0–6.2 recursive definition; §8.0–8.1 concurrency |
| Theory Design and Implementation | §7.0–7.2 data and program theories, data transformation (incl. §7.2.4) |
| Interaction | §9.0–9.1 interactive variables and communication |

`.sci/laws-survey.md` maps each of the ~450 laws of the fourteen §11.3 tables to
the Lean theorem stating it. The laws that are not statable in this typed model
fall into three classes, each explained in the corresponding node: decimal
Counting laws (notation); the type distinctions `{A} ⧧ A` and `[S] ⧧ S`; and
bunch-valued operators (`x/0 = ∞, –∞`, exponent inclusions, bunches of functions
applied as functions, strings of bunches). §4.2.3 (Soundness and Completeness), meta-statements about
observations of computations, is explained in prose in the Program Theory
chapter. Side conditions the model adds (finite `n` in the ⇑⇓ arithmetic laws,
finite domains for Σ and Π, indices in range) are stated on the theorems.

## Layout

```text
LaPToP/
  Basic.lean                 # existing library stub (imports Mathlib)
  Blueprint.lean             # top-level Blueprint document
  Chapters/                  # one Verso chapter per theme, in book order
    Prelude.lean             # §1.0 Binary Theory
    BasicTheories.lean       # §1.0.1–2.1 numbers, bunches, sets, calculation; §11.3.0
    FunctionTheory.lean      # §3 functions, quantifiers, functions as data, limits
    DataStructures.lean      # §2.2–2.3 strings and lists
    ProgramTheory.lean       # §4 specifications, refinement, time, space, old theory
    ProgrammingLanguage.lean # §5 loops, scope, data structures, subprograms, probability, functional
    RecursionConcurrency.lean# §6 recursive definition, §8 concurrency
    TheoryDesign.lean        # §7 theory design and data transformation
    Interaction.lean         # §9 interactive variables and communication
    Collatz.lean             # Exercise 255 Collatz timing (proved)
  Exercises/                # Ch.10 statement stubs (sorry; not Blueprint nodes)
  BasicTheories/             # Binary, Bunch, Numbers, NumberLaws, Calculation, GenericLaws
  DataStructures/            # Strings, Lists, Multidimensional
  FunctionTheory/            # Functions, Quantifiers, FinePoints, HigherOrder, Limits, QuantifierDistribution
  ProgramTheory/             # Specifications, Programs, Time, Space, Search, FastExp, Fibonacci, CollatzTime,
                             #   OldTheory, AssertionLaws, WhileLoop, ForLoop, ExitLoop, TwoDimSearch, GoTo, Scope,
                             #   Arrays, TimeDependence, Assertions, Subprograms, Alias, Probabilistic,
                             #   ProbabilisticSums, RandomNumbers, Blackjack, Information, Functional,
                             #   Interpreter (executable AST with local declarations, array
                             #   element assignment, assertions and backtracking choice; fuelled
                             #   run, searching runAll and fuel-free Eval; write sets and frames;
                             #   denotation into Spec), InterpreterSyntax (tokenizer + parser for
                             #   the demonstration syntax), InterpreterTime (the same syntax on a
                             #   state with a clock; the untimed one is its finite-time part)
  RecursiveDefinition/       # Nat, DataConstruction, Programs, LoopBridge (terminating runs vs the
                             #   §6.1.1 least-fixed-point loop)
  TheoryDesign/              # Stack, SimpleStack, Queue, Tree, ProgramStack, ProgramQueue, DataTransformation,
                             #   SecuritySwitch, TakeANumber, Parsing, LimitedQueue, Incompleteness
  Concurrency/               # Composition, ListConcurrency, Transformation, InsertionSort, DiningPhilosophers
  Interaction/               # InteractiveVariables, GrowSlow, Communication, CommunicationTiming, Merge,
                             #   MergeInterleave, ChannelDeclaration, Deadlock, PowerSeries, Thermostat
Netty/                       # the Netty proof-assistant kernel (no Mathlib, no LaPToP)
  Expr.lean Parser.lean      #   the boolean/number fragment of aPToP, and reading it
  Law.lean Laws.lean         #   laws, their variants, matching; the shipped law list
  laws/boolean.laws          #   the Binary laws of §11.3.1, as a Netty law file
  Doc.lean Render.lean       #   the proof document, zoom stack, context, suggestions
  Json.lean Script.lean      #   saving a proof; the script language and the demos
  Api.lean                   #   the session as one JSON request and one JSON answer
  Replay.lean                #   the document's examples, replayed and checked in Lean
netty-web/                   # the three panes in a browser, over `netty --serve`
  src/protocol.ts            #   the shapes Netty/Api.lean writes
  src/kernel.ts src/server.ts#   the kernel as a child process; static files and POST /api
  src/client.ts public/      #   the proof, context and suggestion panes
LaPToPMain.lean              # Verso generator entry point (`lake exe vbp`)
InterpMain.lean              # interpreter command line (`lake exe interp`)
NettyMain.lean               # Netty command line (`lake exe netty`)
scripts/ci-pages.sh          # builds the site, then scripts/enhance-site-ux.py
.sci/laws-survey.md          # §11.3 Reference law tables mapped to Lean theorems
```

Every Blueprint node quotes the book and points at sorry-free Lean
declarations. Where the Lean model departs from the book — or where the book's
argument is corrected, or asserted without proof and left unproved — the node
prose and the module docstrings say so explicitly; see the published site.
