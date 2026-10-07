# aPToP → Netty book census

Source of truth for which Hehner *A Practical Theory of Programming* proofs
are Netty examples (or could be). Generated on the `feat/aptop-site` branch.
Book edition: **2026-9-21** (`hehner.ca/aPToP/aPToP.pdf`). Exercise numbering
follows Chapter 10; Lean inventory in `LaPToP/Exercises/` and `MISSING.md` §5.

## What counts as “a proof from the book”

Included in the **Netty-candidate** set when **either**:

1. **Worked chapter calculation** — a continuing equation with law hints printed
   in Chapters 1–9 (Netty’s native format), e.g. §1.0.1 Law of Portation; or
2. **Chapter 10 exercise** whose published solution
   (`hehner.ca/aPToP/solutions/ExN.pdf`) is primarily such a calculation
   (prove/simplify with binary or program laws Netty aims to support).

**Not** Netty candidates (status `OUT_OF_SCOPE`): English puzzles; “design
notation / explain in words”; yes/no implementability without a calc;
bunch/string/list/function/concurrency/interaction exercises that need
grammar Netty does not target; counterexamples by instantiation;
meta-theory. Those remain Lean/exercise inventory only.

Status values:

| Status | Meaning |
|--------|---------|
| **PASS** | `.calc` exists; every step `apply`s; in hierarchical picker (loadable) |
| **FAIL** | `.calc` exists; audit refuses (apply gap / compound hint / …); shown disabled |
| **MISSING** | Netty-candidate with no working `.calc` yet |
| **OUT_OF_SCOPE** | Not a Netty calc target (reason in table) |

Standing: **apply-only** calc-load (refuse on gap / no red `!`). Honesty over coverage.

## Netty-candidate summary

| Status | Count |
|--------|------:|
| PASS | 19 |
| FAIL | 7 |
| MISSING | 33 |
| OUT_OF_SCOPE | 1 |
| **Total candidates** | **60** |

Plus **6** kernel demos (always PASS, separate top-level group).

**PASS book calcs loadable in picker: 19** (was 13 before this census pass).

### Counts by chapter / section (candidates only)

| Group | PASS | FAIL | MISSING | OUT | Total |
|-------|-----:|-----:|--------:|----:|------:|
| Expression and Proof Format | 1 | 1 | 0 | 0 | 2 |
| §10.1 Ex.5 — Simplify binary | 4 | 0 | 2 | 0 | 6 |
| §10.1 Ex.6 — Prove binary laws | 6 | 0 | 17 | 0 | 23 |
| §10.1 Ex.7 — if-then-else laws | 1 | 0 | 7 | 0 | 8 |
| §10.1 Ex.12 — Drink and drive | 3 | 0 | 0 | 1 | 4 |
| §10.4 Ex.121 — Simplify programs | 4 | 0 | 7 | 0 | 11 |
| §10.4 Ex.136–140 — Programs & refinement | 0 | 6 | 0 | 0 | 6 |

## Netty-candidate inventory (detail)

Hierarchical picker data: `netty-web/public/examples/manifest.json` (copy: `netty-web/examples/manifest.json`).

### 1 · Basic Theories

#### Expression and Proof Format

| id | bookRef | title | status | path | blocker / next step |
|----|---------|-------|--------|------|---------------------|
| `portation` | §1.0.1 | Law of Portation (continuing equation) | **PASS** | `examples/portation.calc` | — |
| `portation-top` | §1.0.1 | Law of Portation reduced to ⊤ | **FAIL** | `examples/portation-top.calc` | zoom/inclusion: nested inclusion after MI; needs zoom (#54) |

### 10 · Exercises

#### §10.1 Ex.5 — Simplify binary

| id | bookRef | title | status | path | blocker / next step |
|----|---------|-------|--------|------|---------------------|
| `ex5a` | §10.1 Ex.5(a) | Simplify x ∧ ¬x | **MISSING** | `—` | law gap: Add ¬⊤≡⊥ (binary law) or allow part-apply of noncontradiction |
| `ex5b` | §10.1 Ex.5(b) | Simplify x ∨ ¬x (excluded middle) | **PASS** | `examples/ex5b.calc` | — |
| `ex5c` | §10.1 Ex.5(c) | Simplify x ⇒ ¬x | **PASS** | `examples/ex5c.calc` | — |
| `ex5d` | §10.1 Ex.5(d) | Simplify x ⇐ ¬x | **PASS** | `examples/ex5d.calc` | — |
| `ex5e` | §10.1 Ex.5(e) | Simplify x = ¬x | **MISSING** | `—` | law gap: Need unequality / ¬(x=x) rewrite chain from solution |
| `ex5f` | §10.1 Ex.5(f) | Simplify x ⧧ ¬x | **PASS** | `examples/ex5f.calc` | — |

#### §10.1 Ex.6 — Prove binary laws

| id | bookRef | title | status | path | blocker / next step |
|----|---------|-------|--------|------|---------------------|
| `ex6a` | §10.1 Ex.6(a) | Prove a∧b ⇒ a∨b | **PASS** | `examples/ex6a.calc` | — |
| `ex6b` | §10.1 Ex.6(b) | Prove (a∧b)∨(b∧c)∨(c∧a) = (a∨b)∧(b∨c)∧(c∧a) | **MISSING** | `—` | law gap: Solution uses distribute + compound symmetry/idempotence |
| `ex6c` | §10.1 Ex.6(c) | Prove ¬a ⇒ (a⇒b) | **PASS** | `examples/ex6c.calc` | — |
| `ex6d` | §10.1 Ex.6(d) | Prove a=(b⇒a) = a∨b | **MISSING** | `—` | compound hint: Solution chains symmetry/associativity/inclusion of = |
| `ex6e` | §10.1 Ex.6(e) | Prove a=(a⇒b) = a∧b | **MISSING** | `—` | compound hint: Same shape as (d) |
| `ex6f` | §10.1 Ex.6(f) | Prove (a⇒c)∧(b⇒¬c) ⇒ ¬(a∧b) | **MISSING** | `—` | law gap: Solution uses conflation + contrapositive phrasing |
| `ex6g` | §10.1 Ex.6(g) | Prove a∧¬b ⇒ a∨b | **PASS** | `examples/ex6g.calc` | — |
| `ex6h` | §10.1 Ex.6(h) | Prove (a⇒b)∧(c⇒d)∧(a∨c) ⇒ (b∨d) | **MISSING** | `—` | compound hint: Portation then conflation as one theorem claim |
| `ex6i` | §10.1 Ex.6(i) | Prove a∧¬a ⇒ b | **PASS** | `examples/ex6i.calc` | — |
| `ex6j` | §10.1 Ex.6(j) | Prove (a⇒b)∨(b⇒a) | **PASS** | `examples/ex6j.calc` | — |
| `ex6k` | §10.1 Ex.6(k) | Prove ¬(a ∧ ¬(a∨b)) | **MISSING** | `—` | Book-marked done in text; write calc from absorption/duality |
| `ex6l` | §10.1 Ex.6(l) | Prove (¬a⇒¬b)∧(a⧧b) ∨ (a∧c⇒b∧c) | **MISSING** | `—` | compound hint: Multi-operator solution |
| `ex6m` | §10.1 Ex.6(m) | Prove (a⇒¬a)⇒¬a | **MISSING** | `—` | Short calc via portation/indirect; write .calc |
| `ex6n` | §10.1 Ex.6(n) | Prove (a⇒b)∧(¬a⇒b)=b | **MISSING** | `—` | Case / identity style; write .calc |
| `ex6o` | §10.1 Ex.6(o) | Prove (a⇒b)⇒a = a | **MISSING** | `—` | Write .calc from solution |
| `ex6p` | §10.1 Ex.6(p) | Prove a=b ∨ a=c ∨ b=c | **MISSING** | `—` | Write .calc from solution |
| `ex6q` | §10.1 Ex.6(q) | Prove a∧b ∨ a∧¬b = a | **MISSING** | `—` | Distributive/identity; write .calc |
| `ex6r` | §10.1 Ex.6(r) | Prove a⇒(b⇒a) | **PASS** | `examples/ex6r.calc` | — |
| `ex6s` | §10.1 Ex.6(s) | Prove a⇒a∧b = a⇒b = a∨b⇒b | **MISSING** | `—` | compound hint: Continuing equation of three sides |
| `ex6t` | §10.1 Ex.6(t) | Prove (a⇒a∧b)∨(b⇒a∧b) | **MISSING** | `—` | Write .calc from solution |
| `ex6u` | §10.1 Ex.6(u) | Prove (a⇒(p=x))∧(¬a⇒p) = p=(x∨¬a) | **MISSING** | `—` | program/state: Mixes equality with parameters; check Netty grammar |
| `ex6v` | §10.1 Ex.6(v) | Prove (a⇒b⇒¬a)∨(b∧c⇒a∧c) | **MISSING** | `—` | Write .calc from solution |
| `ex6w` | §10.1 Ex.6(w) | Prove a=(b∧c)∧d=(¬b∧¬c)∧e=((a∨d)=c) ⇒ e=b | **MISSING** | `—` | compound hint: Long multi-conjunct solution |

#### §10.1 Ex.7 — if-then-else laws

| id | bookRef | title | status | path | blocker / next step |
|----|---------|-------|--------|------|---------------------|
| `ex7a` | §10.1 Ex.7(a) | if a then a else ¬a ≡ ⊤ | **PASS** | `examples/ex7a.calc` | — |
| `ex7b` | §10.1 Ex.7(b) | if b then c else ¬c = if c then b else ¬b | **MISSING** | `—` | Rewrite solution with one Netty law per step (case analysis, distributive) |
| `ex7c` | §10.1 Ex.7(c) | if b∧c then P else Q = if b then if c then P else Q else Q | **MISSING** | `—` | compound hint: Rewrite solution with one Netty law per step (case analysis, distributive) |
| `ex7d` | §10.1 Ex.7(d) | if b∨c then P else Q = if b then P else if c then P else Q | **MISSING** | `—` | compound hint: Rewrite solution with one Netty law per step (case analysis, distributive) |
| `ex7e` | §10.1 Ex.7(e) | if b then P else if b then Q else R = if b then P else R | **MISSING** | `—` | compound hint: Rewrite solution with one Netty law per step (case analysis, distributive) |
| `ex7f` | §10.1 Ex.7(f) | if if b then c else d then P else Q = … | **MISSING** | `—` | compound hint: Rewrite solution with one Netty law per step (case analysis, distributive) |
| `ex7g` | §10.1 Ex.7(g) | if b then if c then P else R else if c then Q else R = … | **MISSING** | `—` | compound hint: Rewrite solution with one Netty law per step (case analysis, distributive) |
| `ex7h` | §10.1 Ex.7(h) | if b then if c then P else R else if d then Q else R = … | **MISSING** | `—` | compound hint: Rewrite solution with one Netty law per step (case analysis, distributive) |

#### §10.1 Ex.12 — Drink and drive

| id | bookRef | title | status | path | blocker / next step |
|----|---------|-------|--------|------|---------------------|
| `ex12ab` | §10.1 Ex.12(a)=(b) | ¬(drink∧drive) ≡ drink ⇒ ¬drive | **PASS** | `examples/ex12ab.calc` | — |
| `ex12bc` | §10.1 Ex.12(b)=(c) | drink ⇒ ¬drive ≡ drive ⇒ ¬drink | **PASS** | `examples/ex12bc.calc` | — |
| `ex12ae` | §10.1 Ex.12(a)=(e) | ¬(drink∧drive) ≡ ¬drink ∨ ¬drive | **PASS** | `examples/ex12ae.calc` | — |
| `ex12ad` | §10.1 Ex.12(a)≠(d) | ¬(drink∧drive) differs from ¬drink ∧ ¬drive | **OUT_OF_SCOPE** | `—` | other: Counterexample/instantiation, not a continuing-equation calc |

#### §10.4 Ex.121 — Simplify programs

| id | bookRef | title | status | path | blocker / next step |
|----|---------|-------|--------|------|---------------------|
| `ex121a` | §10.4 Ex.121(a) | Substitution after x:= y+1 | **PASS** | `examples/ex121a.calc` | — |
| `ex121b` | §10.4 Ex.121(b) | Substitution into a conjunction | **PASS** | `examples/ex121b.calc` | — |
| `ex121c` | §10.4 Ex.121(c) | x:= y+1. y′=2×x | **MISSING** | `—` | missing: Write .calc from LaPToP/Exercises/calc/ch4.calc and audit |
| `ex121d` | §10.4 Ex.121(d) | x:= 1 with exists; needs quantifier + arithmetic | **MISSING** | `—` | grammar: Write .calc from LaPToP/Exercises/calc/ch4.calc and audit |
| `ex121e` | §10.4 Ex.121(e) | x:= y with exists; binder capture | **MISSING** | `—` | grammar: Write .calc from LaPToP/Exercises/calc/ch4.calc and audit |
| `ex121f` | §10.4 Ex.121(f) | Assignment then ok | **PASS** | `examples/ex121f.calc` | — |
| `ex121g` | §10.4 Ex.121(g) | Two assignments | **PASS** | `examples/ex121g.calc` | — |
| `ex121h` | §10.4 Ex.121(h) | Named spec P; needs definition of P | **MISSING** | `—` | program/state: Write .calc from LaPToP/Exercises/calc/ch4.calc and audit |
| `ex121i` | §10.4 Ex.121(i) | Three assignments | **MISSING** | `—` | program/state: Write .calc from LaPToP/Exercises/calc/ch4.calc and audit |
| `ex121j` | §10.4 Ex.121(j) | Assignment then if | **MISSING** | `—` | program/state: Write .calc from LaPToP/Exercises/calc/ch4.calc and audit |
| `ex121k` | §10.4 Ex.121(k) | Impossible / inconsistency style | **MISSING** | `—` | missing: Write .calc from LaPToP/Exercises/calc/ch4.calc and audit |

#### §10.4 Ex.136–140 — Programs & refinement

| id | bookRef | title | status | path | blocker / next step |
|----|---------|-------|--------|------|---------------------|
| `ex136a` | §10.4 Ex.136(a) | x:= x=y. x:= x=y ≡ ok | **FAIL** | `examples/ex136a.calc` | compound hint: step 3: unresolved hint “Associative Law for binary =” |
| `ex136b` | §10.4 Ex.136(b) | swap via ⧧ | **FAIL** | `examples/ex136b.calc` | compound hint: step 4: unresolved hint “Associativity and Symmetry of ⧧” |
| `ex137a` | §10.4 Ex.137(a) | b:= a–b. b:= a–b ≡ ok | **FAIL** | `examples/ex137a.calc` | compound hint: step 3: empty hint (would need direct) |
| `ex137b` | §10.4 Ex.137(b) | swap via +/– | **FAIL** | `examples/ex137b.calc` | substitution: substitution law fails on arithmetic shape |
| `ex139` | §10.4 Ex.139 | Refine P with n:=n+1 and if | **FAIL** | `examples/ex139.calc` | program/state: step 3: empty hint (would need direct) |
| `ex140-R` | §10.4 Ex.140 | Sum 0..n–1 via Q loop | **FAIL** | `examples/ex140-R.calc` | program/state: step 3: empty hint (would need direct) |

## Full Chapter 10 exercise roll-call

Every numbered exercise in the book (0–533; **393** absent this edition).
Lean modules: `LaPToP/Exercises/Ch0.lean`–`Ch9.lean`. Informal list from module
docstrings / `MISSING.md` §5. Netty-candidate parents link to the detail table above.

### 10.0 Introduction

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 0 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 1 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 2 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 3 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |

### 10.1 Basic Theories

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 4 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 5 | yes | MISSING×5, PASS | see candidates (6 part(s)) |
| 6 | yes | PASS×5, MISSING×18 | see candidates (23 part(s)) |
| 7 | yes | PASS, MISSING×7 | see candidates (8 part(s)) |
| 8 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 9 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 10 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 11 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 12 | yes | PASS, MISSING×2, OUT_OF_SCOPE | see candidates (4 part(s)) |
| 13 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 14 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 15 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 16 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 17 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 18 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 19 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 20 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 21 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 22 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 23 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 24 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 25 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 26 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 27 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 28 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 29 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 30 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 31 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 32 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 33 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 34 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 35 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 36 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 37 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 38 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 39 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 40 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |

### 10.2 Basic Data Structures

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 41 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 42 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 43 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 44 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 45 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 46 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 47 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 48 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 49 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 50 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 51 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 52 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 53 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 54 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 55 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 56 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 57 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 58 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 59 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 60 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 61 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 62 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 63 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 64 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 65 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 66 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 67 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 68 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |

### 10.3 Function Theory

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 69 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 70 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 71 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 72 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 73 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 74 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 75 | no | OUT_OF_SCOPE | not a Netty calc target (stub / other theory) |
| 76 | no | OUT_OF_SCOPE | not a Netty calc target (stub / other theory) |
| 77 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 78 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 79 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 80 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 81 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 82 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 83 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 84 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 85 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 86 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 87 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 88 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 89 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 90 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 91 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 92 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 93 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 94 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 95 | no | OUT_OF_SCOPE | not a Netty calc target (stub / other theory) |
| 96 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 97 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 98 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 99 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 100 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 101 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 102 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 103 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 104 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 105 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 106 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 107 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 108 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 109 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 110 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 111 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 112 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 113 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 114 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 115 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |
| 116 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 117 | no | OUT_OF_SCOPE | not a Netty calc target (stub / other theory) |
| 118 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 119 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 120 | no | OUT_OF_SCOPE | informal / design / explain (MISSING.md) |

### 10.4 Program Theory

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 121 | yes | PASS×4, MISSING×7 | see candidates (11 part(s)) |
| 122 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 123 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 124 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 125 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 126 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 127 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 128 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 129 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 130 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 131 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 132 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 133 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 134 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 135 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 136 | yes | FAIL×2 | see candidates (2 part(s)) |
| 137 | yes | FAIL×2 | see candidates (2 part(s)) |
| 138 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 139 | yes | FAIL | see candidates (1 part(s)) |
| 140 | yes | FAIL | see candidates (1 part(s)) |
| 141 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 142 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 143 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 144 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 145 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 146 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 147 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 148 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 149 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 150 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 151 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 152 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 153 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 154 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 155 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 156 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 157 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 158 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 159 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 160 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 161 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 162 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 163 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 164 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 165 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 166 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 167 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 168 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 169 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 170 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 171 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 172 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 173 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 174 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 175 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 176 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 177 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 178 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 179 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 180 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 181 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 182 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 183 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 184 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 185 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 186 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 187 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 188 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 189 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 190 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 191 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 192 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 193 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 194 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 195 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 196 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 197 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 198 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 199 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 200 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 201 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 202 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 203 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 204 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 205 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 206 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 207 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 208 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 209 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 210 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 211 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 212 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 213 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 214 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 215 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 216 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 217 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 218 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 219 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 220 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 221 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 222 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 223 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 224 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 225 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 226 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 227 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 228 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 229 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 230 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 231 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 232 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 233 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 234 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 235 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 236 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 237 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 238 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 239 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 240 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 241 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 242 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 243 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 244 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 245 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 246 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 247 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 248 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 249 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 250 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 251 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 252 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 253 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 254 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 255 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 256 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 257 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 258 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 259 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 260 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 261 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 262 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 263 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 264 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 265 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 266 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 267 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 268 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 269 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 270 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 271 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 272 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 273 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 274 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 275 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 276 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 277 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 278 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 279 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 280 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 281 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 282 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 283 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 284 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 285 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 286 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 287 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 288 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 289 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 290 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 291 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 292 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 293 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 294 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 295 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 296 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 297 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 298 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 299 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 300 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 301 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 302 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 303 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 304 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 305 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |

### 10.5 Programming Language

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 306 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 307 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 308 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 309 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 310 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 311 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 312 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 313 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 314 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 315 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 316 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 317 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 318 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 319 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 320 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 321 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 322 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 323 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 324 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 325 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 326 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 327 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 328 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 329 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 330 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 331 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 332 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 333 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 334 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 335 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 336 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 337 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 338 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 339 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 340 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 341 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 342 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 343 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 344 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 345 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 346 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 347 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 348 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 349 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 350 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 351 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 352 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 353 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 354 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 355 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 356 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 357 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 358 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 359 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 360 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 361 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 362 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 363 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 364 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 365 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |

### 10.6 Recursive Definition

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 366 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 367 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 368 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 369 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 370 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 371 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 372 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 373 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 374 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 375 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 376 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 377 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 378 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 379 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 380 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 381 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 382 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 383 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 384 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 385 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 386 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 387 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 388 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 389 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 390 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 391 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 392 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 394 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 395 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 396 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 397 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 398 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 399 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 400 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 401 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 402 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 403 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 404 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 405 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 406 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 407 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 408 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 409 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 410 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 411 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 412 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 413 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 414 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 415 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 416 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 417 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 418 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 419 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 420 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 421 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |

### 10.7 Theory Design and Implementation

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 422 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 423 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 424 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 425 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 426 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 427 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 428 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 429 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 430 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 431 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 432 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 433 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 434 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 435 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 436 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 437 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 438 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 439 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 440 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 441 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 442 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 443 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 444 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 445 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 446 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 447 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 448 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 449 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 450 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 451 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 452 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 453 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 454 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 455 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 456 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 457 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 458 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 459 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 460 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 461 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 462 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 463 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 464 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 465 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 466 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 467 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 468 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 469 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 470 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 471 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 472 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 473 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 474 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 475 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 476 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |

### 10.8 Concurrency

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 477 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 478 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 479 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 480 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 481 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 482 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 483 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 484 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 485 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 486 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 487 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 488 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 489 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 490 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 491 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 492 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 493 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 494 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |

### 10.9 Interaction

| # | Netty? | Default status | Note |
|--:|--------|----------------|------|
| 495 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 496 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 497 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 498 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 499 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 500 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 501 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 502 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 503 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 504 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 505 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 506 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 507 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 508 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 509 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 510 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 511 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 512 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 513 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 514 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 515 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 516 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 517 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 518 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 519 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 520 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 521 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 522 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 523 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 524 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 525 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 526 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 527 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 528 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 529 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 530 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 531 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 532 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |
| 533 | no | OUT_OF_SCOPE | Lean formalized or stub; not Netty calc format |

### Roll-call counts

- Netty-candidate exercise **numbers** (may have several parts): **9**
- OUT_OF_SCOPE exercise numbers: **524**
- Book exercises in ranges above (excl. 393): **533**

Chapter-body worked calcs outside Ch.10: **2** (portation, portation-top) — counted in Netty-candidate summary, not in the Ch.10 roll-call.

## Blocker categories (FAIL + MISSING)

| Blocker | Count |
|---------|------:|
| compound hint | 15 |
| no .calc yet | 9 |
| program/state | 6 |
| law gap | 4 |
| missing | 2 |
| grammar | 2 |
| zoom/inclusion | 1 |
| substitution | 1 |

Top themes: **compound book hints** (multi-law phrases, “twice”, empty hints),
**program/`state`/`spec`** (#55), **zoom/nested inclusion** (portation-top, #54),
**law gaps** (binary ¬⊤≡⊥, unequality chains, distribute phrasing), **grammar**
(quantifiers/binders in Ex.121).

## Related files

- `netty-web/public/examples/*.calc` — calc sources
- `netty-web/public/examples/manifest.json` — picker hierarchy
- `netty-web/AUDIT-CALCS.md` — last apply-only audit (points here)
- `netty-web/DROPPED.md` — historical drop list (points here)
- `LaPToP/Exercises/calc/` — longer program calcs (ex139, 140, 121…)
- `MISSING.md` §5 — Lean formalization inventory (not Netty)
