# Missing from the LaPToP formalization

This file lists what from Eric Hehner's *A Practical Theory of Programming*
(aPToP) is **not** formalized in Lean, and why. Coverage of Chapters 1–9
section-by-section and of the §11.3 law tables is otherwise complete; see
`README.md`, `.sci/laws-survey.md`, and the Blueprint nodes.

Exercise *statements* for Chapter 10 are inventoried as deferred theorem
signatures in `LaPToP/Exercises/` (Memnar #1032 exception: `sorry` stubs only).
Those stubs are not proofs and are not Blueprint nodes.

## 1. Three hard law classes (typed model)

Recorded law-by-law in `.sci/laws-survey.md`. None of these are bugs to “fix”
without changing the modelling discipline.

### 1.1 Decimal Counting notation (§11.3.2 Numbers)

The book’s Counting laws (`d0+1 = d1`, …, `d9+1 = (d+1)0`) are decimal
*notation*, not algebraic content. Lean decides concrete digit arithmetic with
`norm_num` on instances. Not modelled as named theorems (10 laws in the survey
table).

### 1.2 Type distinctions `{A} ⧧ A` and `[S] ⧧ S`

In the book, bunches, sets, and lists share one untyped syntax, so
`{A} ⧧ A` (set packaging) and `[S] ⧧ S` (list packaging) are meaningful
inequalities. In Lean they are different types (`Bunch` / `HSet` / `HList` /
`Str`), so the inequalities are not statable as propositions about a common
carrier. Recorded under §11.3.4 Sets and §11.3.6 Lists.

### 1.3 Bunch-valued division, exponentiation, and function-bunch application

The book’s operators distribute over bunches:

- `x/0` is the bunch `∞, –∞` (and related `xreal` cases);
- exponent laws include bunch *inclusions* such as `x^(y+z)` including
  `x^y × x^z`;
- a bunch of functions applied as a function; strings of bunches as bunches of
  strings; `S{A}`; function intersection forms.

Here arithmetic, application, and strings are functions of *elements*, and
bunches are sets of results (`applyBunch`, `applyFns`, pointwise bunch
equations). The elementwise / set-level equations that *are* statable are
proved; the genuinely bunch-valued readings are not. See survey rows for
§11.3.3 Bunches, §11.3.5 Strings, §11.3.7 Functions.

## 2. §4.2.3 Soundness and Completeness (meta-statements)

Section 4.2.3 discusses soundness and completeness of the programming theory
relative to *observations* of computations. Those are meta-statements about the
relationship between the formal system and informal observation, not theorems
inside the object theory. They appear as prose in the Program Theory Blueprint
chapter intro; there is no Lean statement.

## 3. Reference extras (not object-theory formalization targets)

- **Symbols / notation / precedence / distribution tables** in Chapter 11
  (Reference): documentation of the book’s syntax, not laws to prove. Precedence
  and distribution are reflected in Lean’s notation and in the bunch-distribution
  lemmas where applicable; there is no separate “symbols table” formalization.
- **Exercise solutions** (hehner.ca/aPToP/solutions): out of scope. Chapter 10
  statements are stubbed in `LaPToP/Exercises/`; solutions are not imported.

## 4. Residual honesty notes (already explained in nodes)

These are covered by formalized material plus documented caveats — listed here
so “missing” is not confused with “unfinished demo”:

- §7 weak stack “garbage” remark; informal parsing transformers in §7.2.2.
- §8.0.1 time remark on the sequential-to-concurrent transformation.
- §5.4 `screen!` output (Chapter 9 notation).
- §9.1.4/9.1.6 Merge’s literal fixed-point refinement (Interleave invariant
  proved instead); §9.1.1 “strongest implementable solution” with
  extended-natural cursors.
- Open **Collatz conjecture** (termination / finiteness of the time function
  `f` in Exercise 255): *not* a Blueprint node. The Exercise 255 *timing
  refinements* are proved (`collatz_time` / `LaPToP.ProgramTheory.CollatzTime`).
  The conjecture itself remains open mathematics; see stub `exercise_255`.

## 5. Chapter 10 exercise inventory

| Book § | Theme | Stubs module | Count |
|---|---|---|---|
| 10.0 | Introduction | `LaPToP.Exercises.Ch0` | 4 |
| 10.1 | Basic Theories | `LaPToP.Exercises.Ch1` | 37 |
| 10.2 | Basic Data Structures | `LaPToP.Exercises.Ch2` | 28 |
| 10.3 | Function Theory | `LaPToP.Exercises.Ch3` | 51 |
| 10.4 | Program Theory | `LaPToP.Exercises.Ch4` | 185 |
| 10.5 | Programming Language | `LaPToP.Exercises.Ch5` | 60 |
| 10.6 | Recursive Definition | `LaPToP.Exercises.Ch6` | 55 |
| 10.7 | Theory Design and Implementation | `LaPToP.Exercises.Ch7` | 55 |
| 10.8 | Concurrency | `LaPToP.Exercises.Ch8` | 18 |
| 10.9 | Interaction | `LaPToP.Exercises.Ch9` | 39 |
| | **Total** | | **532** |

Numbering follows the book’s Chapter 10. Gaps **94** and **393** do not appear
as exercises in this edition’s text extract. A minority of exercises already
have real developments under `LaPToP/**` (e.g. 172, 174, 255, 491, …); the
Chapter 10 stubs remain as inventory only.
