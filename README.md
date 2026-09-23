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
and `interp` runs programs written in the concrete syntax of its demonstrations.

```bash
lake build interp                      # first time: compiles the exe (a few minutes)
lake exe interp --help                 # options
lake exe interp --grammar              # the grammar of the concrete syntax
lake exe interp --demo=sumTo --n=10    # => n = 10, i = 10, s = 55
lake exe interp --selftest             # the sources parse to the proved programs
echo 'i:= 0. s:= 0. while i != n do i:= i+1. s:= s+i od' | lake exe interp --n=20
echo 's:= 0 or s:= 1. ensure s = 1' | lake exe interp --all   # backtracking
echo 'while i != n do i:= i+1. tick od' | lake exe interp --n=7 --timed
```

The state is the three integer variables `n`, `i`, `s`. `--all` searches for
every poststate (`runAll`) instead of running the deterministic interpreter
once, which is what a choice needs. `--timed` adds a clock: `tick` advances it,
and a false `assert` waits until `∞` where a false `ensure` has no poststate at
all. Exit status is 1 for a parse error and 2
when there is no poststate. Building the executable links the whole import
chain, so it is a separate target: plain `lake build` and the Blueprint site do
not build it.

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

Laws are plain text files (`Netty/laws/boolean.laws` holds the Binary laws of
aPToP §11.3.1); add your own with `--laws=FILE`. `Netty/Laws.lean` reads the
shipped file at compile time and `Netty.boolean_isTautology` checks in Lean's
kernel that every law in it is a tautology; `Netty/Replay.lean` replays all
three demonstrations in Lean and proves that each ends with no gaps, fully
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
`apply #N`, a click on a subexpression is `zoom N`, a click on a line number is
`focus N`, and every change still goes through `Netty.Doc.step`. `netty-web/README.md`
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
