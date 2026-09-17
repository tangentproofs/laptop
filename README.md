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

## Layout

```text
LaPToP/
  Basic.lean                 # existing library stub (imports Mathlib)
  Blueprint.lean             # top-level Blueprint document
  Chapters/                  # one Verso chapter per theme, in book order
    Prelude.lean             # §1.0 Binary Theory
    BasicTheories.lean       # §1.0.1–2.1 numbers, bunches, sets, calculation
    FunctionTheory.lean      # §3 functions, quantifiers, functions as data
    DataStructures.lean      # §2.2–2.3 strings and lists
    ProgramTheory.lean       # §4 specifications, refinement, time, space
    ProgrammingLanguage.lean # §5 loops, scope, data structures, subprograms
    RecursionConcurrency.lean# §6 recursive definition, §8 concurrency
    TheoryDesign.lean        # §7 theory design and data transformation
    Interaction.lean         # §9 interactive variables and communication
    Collatz.lean             # unfinished demo node
  BasicTheories/  DataStructures/  FunctionTheory/  ProgramTheory/
  RecursiveDefinition/  TheoryDesign/  Concurrency/  Interaction/
                             # the Lean modules the chapters point at
LaPToPMain.lean              # Verso generator entry point
scripts/ci-pages.sh          # builds the site, then scripts/enhance-site-ux.py
.sci/laws-survey.md          # §11.3 Reference law tables mapped to Lean theorems / gaps
```

Every Blueprint node quotes the book and points at sorry-free Lean
declarations. Where the Lean model departs from the book — or where the book's
argument is corrected, or asserted without proof and left unproved — the node
prose and the module docstrings say so explicitly; see the published site.
