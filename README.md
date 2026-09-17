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
the Reference chapter (§11.3) are surveyed law by law. The Blueprint has 167
nodes; all are formalized and sorry-free except the intentionally open demo
node `collatz_conjecture`.

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
    Collatz.lean             # unfinished demo node
  BasicTheories/             # Binary, Bunch, Numbers, NumberLaws, Calculation, GenericLaws
  DataStructures/            # Strings, Lists, Multidimensional
  FunctionTheory/            # Functions, Quantifiers, FinePoints, HigherOrder, Limits, QuantifierDistribution
  ProgramTheory/             # Specifications, Programs, Time, Space, Search, FastExp, Fibonacci, CollatzTime,
                             #   OldTheory, AssertionLaws, WhileLoop, ForLoop, ExitLoop, TwoDimSearch, GoTo, Scope,
                             #   Arrays, TimeDependence, Assertions, Subprograms, Alias, Probabilistic,
                             #   ProbabilisticSums, RandomNumbers, Blackjack, Information, Functional
  RecursiveDefinition/       # Nat, DataConstruction, Programs
  TheoryDesign/              # Stack, SimpleStack, Queue, Tree, ProgramStack, ProgramQueue, DataTransformation,
                             #   SecuritySwitch, TakeANumber, Parsing, LimitedQueue, Incompleteness
  Concurrency/               # Composition, ListConcurrency, Transformation, InsertionSort, DiningPhilosophers
  Interaction/               # InteractiveVariables, GrowSlow, Communication, CommunicationTiming, Merge,
                             #   MergeInterleave, ChannelDeclaration, Deadlock, PowerSeries, Thermostat
LaPToPMain.lean              # Verso generator entry point
scripts/ci-pages.sh          # builds the site, then scripts/enhance-site-ux.py
.sci/laws-survey.md          # §11.3 Reference law tables mapped to Lean theorems
```

Every Blueprint node quotes the book and points at sorry-free Lean
declarations. Where the Lean model departs from the book — or where the book's
argument is corrected, or asserted without proof and left unproved — the node
prose and the module docstrings say so explicitly; see the published site.
