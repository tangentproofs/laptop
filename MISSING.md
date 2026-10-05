# Missing from the LaPToP formalization

This file lists what from Eric Hehner's *A Practical Theory of Programming*
(aPToP) is **not** formalized in Lean, and why. Coverage of Chapters 1–9
section-by-section and of the §11.3 law tables is otherwise complete; see
`README.md`, `.sci/laws-survey.md`, and the Blueprint nodes.

Chapter 10's exercises are in `LaPToP/Exercises/`, one module per section: an
exercise is either formalized and proved there, or still a deferred stub
(`Statement n`, with `sorry`), or recorded below as informal. The stubs are not
proofs and are not Blueprint nodes; see §5 for the count.

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
  The precedence table is compared with the parsers below.
- **Precedence**: the book's table (Section 11.6) next to the two parsers that
  read the book's notation, the interpreter's language
  (`InterpreterLangSyntax.lean`, `interp --grammar`) and Netty's
  (`Netty/Parser.lean`). The first level binds tightest; a dash means the parser
  does not have the operator.

  | level | the book (§11.6) | `interp` | Netty |
  | ----- | ---------------- | -------- | ----- |
  | 0 | `⊤ ⊥ ( ) { } [ ] 〈 〉 if fi do od`, numbers, names, superscripts | `⊤ ⊥ ( ) [ ]`, `if … fi` in expressions, numbers, names; `a ^ n` (the superscript) just below juxtaposition, so `-a^2` is `-(a^2)` | `⊤ ⊥ ( )`, `if … fi`, numbers, names |
  | 1 | `@`, adjacency (left to right) | adjacency is indexing: `A i j` is `(A i) j` | — |
  | 2 | prefix `– ¢ $ ↔ # * ~ ☐ → √`, quantifiers on functions | prefix `-`, `#`, `√`, and **`¬`** (see level 8) | — |
  | 3 | `× / ∩ ↑ ↓` | `× * div mod` | `×` |
  | 4 | `+`, infix `–`, `∪` | `+ -` | `+ -` |
  | 5 | `; ;.. ;; '` | `;` only between the items of `[ ]`, `;..` only in `for` | — |
  | 6 | `, ,.. –, \| ⊲⊳` | `,` only in simultaneous assignment and parameters | — |
  | 7 | `= ⧧ < > ≤ ≥ : :: ∈ ⊆`, **continuing** | `= ≠ < ≤ > ≥`, **one** comparison: `a = b = c` does not parse | `= ⧧ < > ≤ ≥ :`, grouped **to the left** |
  | 8 | `¬` | the word `not`: `not x = y` is `¬(x = y)` | `¬`: `¬a = b` is `¬(a = b)` |
  | 9 | `∧` | `∧ /\ and` | `∧` |
  | 10 | `∨` | `∨ \/` | `∨` |
  | 11 | `⇒ ⇐`, **continuing** | `⇒ => ->` and `<== <-`, grouped **to the right** | `⇒ ⇐`, grouped **to the left** |
  | 12 | `:= ! ?` | `:=`, `c! e`, `c?` (statements) | — |
  | 13 | `exit when`, `go to`, `wait until`, `assert`, `ensure`, `or` | `exit … when`, `assert`, `ensure` (statements); `or` binds tighter than `\|\|` and looser than `:=` | — |
  | 14 | `.` `\|\|` `value` | `.`, and `\|\|` binding **tighter** than `.` | — |
  | 15 | `∀· ∃· Σ· Π·` (abbreviated quantifiers), `new·`, `frame·` | `new x:= e in P end`, bracketed by its keywords | `∀ ∃`, whose body runs to the end of the expression, **past** level 16 |
  | 16 | large `= ⇒ ⇐`, **continuing** | `== --> <--` (or `≡ ⟹ ⟸`), grouped **to the left** | `≡ ⟹ ⟸`, grouped **to the left** |

  Where they differ from the book (in bold):
  - **Continuing operators.** On levels 7, 11 and 16 the book's operators are
    continuing: `a = b = c` means `a = b ∧ b = c`, and `a ≤ b < c` means
    `a ≤ b ∧ b < c`. Neither parser reads them so. The interpreter takes at most
    one comparison and groups `⇒ ⇐` to the right; Netty groups everything to the
    left.
  - **`¬`.** In the interpreter the glyph `¬` binds tightest (`¬x = y` is
    `(¬x) = y`), and the word `not` takes the book's level 8.
  - **`.` and `||`.** The book puts them on one level. The interpreter binds
    `||` tighter, so `P. Q || R` is `P. (Q || R)`.
  - **Netty's quantifiers.** Their body runs past the large operators, as in the
    Netty document's grammar, where the book's level 15 stops at level 16.
  - **`or`.** Program-level choice is on level 13, with `ensure` and `assert`:
    between the assignments of level 12 and the `.` and `||` of level 14. That is
    where the interpreter has it.
- **Exercise solutions** (hehner.ca/aPToP/solutions): not imported. Chapter 10
  exercises are being formalized from the book's text in `LaPToP/Exercises/`
  (§5).

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

| Book § | Theme | Module | Count | Proved | Informal | Stubs left |
|---|---|---|---|---|---|---|
| 10.0 | Introduction | `LaPToP.Exercises.Ch0` | 4 | 4 | 0 | 0 |
| 10.1 | Basic Theories | `LaPToP.Exercises.Ch1` | 37 | 27 | 10 | 0 |
| 10.2 | Basic Data Structures | `LaPToP.Exercises.Ch2` | 28 | 16 | 12 | 0 |
| 10.3 | Function Theory | `LaPToP.Exercises.Ch3` | 52 | 38 | 14 | 0 |
| 10.4 | Program Theory | `LaPToP.Exercises.Ch4` | 185 | 4 | | 181 |
| 10.5 | Programming Language | `LaPToP.Exercises.Ch5` | 60 | | | 60 |
| 10.6 | Recursive Definition | `LaPToP.Exercises.Ch6` | 55 | | | 55 |
| 10.7 | Theory Design and Implementation | `LaPToP.Exercises.Ch7` | 55 | | | 55 |
| 10.8 | Concurrency | `LaPToP.Exercises.Ch8` | 18 | | | 18 |
| 10.9 | Interaction | `LaPToP.Exercises.Ch9` | 39 | | | 39 |
| | **Total** | | **533** | **89** | **36** | **408** |

*Informal* exercises ask to design notation, to explain in words, or to
translate English, and have no single formal statement: in §10.1 these are 13,
17, 20, 25, 32, 33, 34, 37, 39 and 40. Some proved exercises also have informal
parts, named in their module's docstring (4's succinctness, 11(e)–(f),
15(b)–(d), 19's discussion, 29(c)–(f)).

In §10.4 the proofs are written in aPToP's own notation, as calculation files
(`LaPToP/Exercises/calc/`), checked step by step by the Netty kernel and
translated into Lean theorems by `netty_proofs` (`LaPToP.Exercises.Calc`):
121, 136 and 137 (all parts) and 140 (a specification file and an
implementation extending it) are proved.

Numbering follows the book’s Chapter 10. Exercise **94** is in the book (the
earlier inventory missed it, and it is now proved); **393** does not appear in
this edition. A minority of exercises already
have real developments under `LaPToP/**` (e.g. 172, 174, 255, 491, …); the
Chapter 10 stubs remain as inventory only.
