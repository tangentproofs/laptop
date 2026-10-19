# Ampheck examples step-validity audit

Source of truth for inventory/blockers: [`BOOK-CENSUS.md`](BOOK-CENSUS.md).
Hierarchical picker: `public/examples/manifest.json`.

| id | in picker | status | reason |
|----|-----------|--------|--------|
| `ex121a` | yes | **PASS** | every apply ok, no gaps |
| `ex121b` | yes | **PASS** | every apply ok, no gaps |
| `ex121c` | no | **PASS** | every apply ok, no gaps |
| `ex121d` | no | **FAIL** | no applicable suggestion from a law named ‘arithmetic’ @ apply arithmetic : = ⊤ ⇒ ∃x: int· y′ = 2×x |
| `ex121e` | no | **PASS** | every apply ok, no gaps |
| `ex121f` | yes | **PASS** | every apply ok, no gaps |
| `ex121g` | yes | **PASS** | every apply ok, no gaps |
| `ex121h` | no | **FAIL** | no applicable suggestion from a law named ‘definition of p’ @ apply definition of P : = x:= 1. y:= 2 |
| `ex121i` | no | **FAIL** | no applicable suggestion from a law named ‘arithmetic’ @ apply arithmetic : = x′ = 3 ∧ y′ = 2 |
| `ex121j` | no | **FAIL** | step 1: unresolved hint “assignment, assignment” |
| `ex121k` | no | **FAIL** | no applicable suggestion from a law named ‘arithmetic’ @ apply arithmetic : = ∃x″: int· ∃y″: int· x″ > 1 ∧ x″ = x′–1 |
| `ex12ab` | yes | **PASS** | every apply ok, no gaps |
| `ex12ae` | yes | **PASS** | every apply ok, no gaps |
| `ex12bc` | yes | **PASS** | every apply ok, no gaps |
| `ex136a` | no | **FAIL** | step 3: unresolved hint “Associative Law for binary =” |
| `ex136b` | no | **FAIL** | step 4: unresolved hint “Associativity and Symmetry of ⧧” |
| `ex137a` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex137b` | no | **FAIL** | no applicable suggestion from a law named ‘substitution law’ @ apply substitution law : = a′=b ∧ b′ = (a+b)–b ∧ c′=c |
| `ex139` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex140-R` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex5a` | no | **FAIL** | no applicable suggestion from a law named ‘binary law’ @ apply binary law : = ¬¬⊥ |
| `ex5b` | yes | **PASS** | every apply ok, no gaps |
| `ex5c` | yes | **PASS** | every apply ok, no gaps |
| `ex5d` | yes | **PASS** | every apply ok, no gaps |
| `ex5e` | no | **FAIL** | expected an operand but found ‘¬’ @ start = x = ¬x |
| `ex5f` | yes | **PASS** | every apply ok, no gaps |
| `ex6a` | yes | **PASS** | every apply ok, no gaps |
| `ex6b` | no | **FAIL** | no applicable suggestion from a law named ‘distribute’ @ apply distribute : = (a∨b∨c)∧(a∨b∨a)∧(a∨c∨c)∧(a∨c∨a)∧(b∨b∨c)∧(b∨b∨a)∧(b∨c∨c)∧(b∨c∨a) |
| `ex6c` | yes | **PASS** | every apply ok, no gaps |
| `ex6d` | no | **FAIL** | step 1: unresolved hint “symmetry of =” |
| `ex6e` | no | **FAIL** | step 1: unresolved hint “symmetry of =” |
| `ex6f` | no | **FAIL** | no applicable suggestion from a law named ‘law of conflation’ @ apply law of conflation : ⇒ a∧b ⇒ c ∧ ¬c |
| `ex6g` | yes | **PASS** | every apply ok, no gaps |
| `ex6h` | no | **PASS** | every apply ok, no gaps |
| `ex6i` | yes | **PASS** | every apply ok, no gaps |
| `ex6j` | yes | **PASS** | every apply ok, no gaps |
| `ex6k` | no | **PASS** | every apply ok, no gaps |
| `ex6l` | no | **FAIL** | step 2: empty hint (would need direct) |
| `ex6m` | no | **PASS** | every apply ok, no gaps |
| `ex6n` | no | **FAIL** | no applicable suggestion from a law named ‘antidistributive law’ @ apply antidistributive law : = a∨¬a ⇒ b |
| `ex6o` | no | **FAIL** | no applicable suggestion from a law named ‘double negation’ @ apply double negation : = (a ∧ ¬b) ∨ a |
| `ex6p` | no | **FAIL** | step 1: unresolved hint “identity and reflexive laws for =” |
| `ex6q` | no | **FAIL** | no applicable suggestion from a law named ‘factor’ @ apply factor : = a∧(b ∨ ¬b) = a |
| `ex6r` | yes | **PASS** | every apply ok, no gaps |
| `ex6s` | no | **FAIL** | step 1: unresolved hint “distribute ⇒ over ∧; antidistribute ⇒ over ∨” |
| `ex6t` | no | **FAIL** | step 1: unresolved hint “anti-distributive” |
| `ex6u` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex6v` | no | **FAIL** | no applicable suggestion from a law named ‘continuing implication’ @ apply continuing implication : = (a⇒b) ∧ (b⇒¬a) ∨ (b∧c ⇒ a∧c) |
| `ex6w` | no | **FAIL** | step 5: unresolved hint “reflexive, identity” |
| `ex7a` | yes | **PASS** | every apply ok, no gaps |
| `ex7b` | no | **FAIL** | no applicable suggestion from a law named ‘symmetry twice’ @ apply symmetry twice : = c∧b ∨ ¬c∧¬b |
| `ex7c` | no | **FAIL** | step 1: unresolved hint “case analysis, twice” |
| `ex7d` | no | **FAIL** | step 4: unresolved hint “distribute, duality” |
| `ex7e` | no | **FAIL** | no applicable suggestion from a law named ‘context’ @ apply context : = if b then P else if ⊥ then Q else R fi fi |
| `ex7f` | no | **FAIL** | no applicable suggestion from a law named ‘distribute’ @ apply distribute : = if b then c∧P else d∧P fi ∨ if b then ¬c∧Q else ¬d∧Q fi |
| `ex7g` | no | **FAIL** | no applicable suggestion from a law named ‘case idempotent’ @ apply case idempotent : = if c then if b then if c then P else R fi else if c then Q else R fi fi else if b then if c then P else R fi else if c then Q else R fi fi fi |
| `ex7h` | no | **FAIL** | no applicable suggestion from a law named ‘case analysis law’ @ apply case analysis law : = if b then c else d fi ∧ if b then P else Q fi ∨ ¬if b then c else d fi ∧ R |
| `portation-top` | no | **FAIL** | no applicable suggestion from a law named ‘inclusion’ @ apply inclusion : = (¬(a ∧ b) ∨ c ≡ ¬a ∨ (¬b ∨ c)) |
| `portation` | yes | **PASS** | every apply ok, no gaps |
| `demo:portation` | yes | **PASS** | demo, no gaps |
| `demo:discharge` | yes | **PASS** | demo, no gaps |
| `demo:minimize` | yes | **PASS** | demo, no gaps |
| `demo:segment` | yes | **PASS** | demo, no gaps |
| `demo:fold` | yes | **PASS** | demo, no gaps |
| `demo:merge` | yes | **PASS** | demo, no gaps |
