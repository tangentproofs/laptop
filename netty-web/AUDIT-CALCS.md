# Netty examples step-validity audit

Source of truth for inventory/blockers: [`BOOK-CENSUS.md`](BOOK-CENSUS.md).
Hierarchical picker: `public/examples/manifest.json`.

| id | in picker | status | reason |
|----|-----------|--------|--------|
| `ex121a` | yes | **PASS** | every apply ok, no gaps |
| `ex121b` | yes | **PASS** | every apply ok, no gaps |
| `ex121f` | yes | **PASS** | every apply ok, no gaps |
| `ex121g` | yes | **PASS** | every apply ok, no gaps |
| `ex12ab` | yes | **PASS** | every apply ok, no gaps |
| `ex12ae` | yes | **PASS** | every apply ok, no gaps |
| `ex12bc` | yes | **PASS** | every apply ok, no gaps |
| `ex136a` | no | **FAIL** | step 3: unresolved hint “Associative Law for binary =” |
| `ex136b` | no | **FAIL** | step 4: unresolved hint “Associativity and Symmetry of ⧧” |
| `ex137a` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex137b` | no | **FAIL** | no applicable suggestion from a law named ‘substitution law’ @ apply substitution law : = a′=b ∧ b′ = (a+b)–b ∧ c′=c |
| `ex139` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex140-R` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex5b` | yes | **PASS** | every apply ok, no gaps |
| `ex5c` | yes | **PASS** | every apply ok, no gaps |
| `ex5d` | yes | **PASS** | every apply ok, no gaps |
| `ex5f` | yes | **PASS** | every apply ok, no gaps |
| `ex6a` | yes | **PASS** | every apply ok, no gaps |
| `ex6c` | yes | **PASS** | every apply ok, no gaps |
| `ex6g` | yes | **PASS** | every apply ok, no gaps |
| `ex6i` | yes | **PASS** | every apply ok, no gaps |
| `ex6j` | yes | **PASS** | every apply ok, no gaps |
| `ex6r` | yes | **PASS** | every apply ok, no gaps |
| `ex7a` | yes | **PASS** | every apply ok, no gaps |
| `portation-top` | no | **FAIL** | no applicable suggestion from a law named ‘inclusion’ @ apply inclusion : = (¬(a ∧ b) ∨ c ≡ ¬a ∨ (¬b ∨ c)) |
| `portation` | yes | **PASS** | every apply ok, no gaps |
| `demo:portation` | yes | **PASS** | demo, no gaps |
| `demo:discharge` | yes | **PASS** | demo, no gaps |
| `demo:minimize` | yes | **PASS** | demo, no gaps |
| `demo:segment` | yes | **PASS** | demo, no gaps |
| `demo:fold` | yes | **PASS** | demo, no gaps |
| `demo:merge` | yes | **PASS** | demo, no gaps |
