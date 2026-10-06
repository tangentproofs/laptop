# Netty examples step-validity audit

| id | in picker | status | reason |
|----|-----------|--------|--------|
| `ex121a` | no | **FAIL** | no applicable suggestion from a law named ‘substitution law’ @ apply substitution law : = y′ > x′ |
| `ex121b` | no | **FAIL** | no applicable suggestion from a law named ‘substitution law’ @ apply substitution law : = y′ > x+1 ∧ x′ > x+1 |
| `ex121f` | no | **FAIL** | no applicable suggestion from a law named ‘ok’ @ apply ok : = x:= 1. x′ = x ∧ y′ = y |
| `ex121g` | no | **FAIL** | no applicable suggestion from a law named ‘assignment’ @ apply assignment : = x:= 1. x′ = x ∧ y′ = 2 |
| `ex12ab` | no | **FAIL** | no applicable suggestion from a law named ‘inclusion’ @ apply inclusion : = ¬¬drink ⇒ ¬drive |
| `ex136a` | no | **FAIL** | step 3: unresolved hint “Associative Law for binary =” |
| `ex136b` | no | **FAIL** | step 4: unresolved hint “Associativity and Symmetry of ⧧” |
| `ex137a` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex137b` | no | **FAIL** | no applicable suggestion from a law named ‘expand last assignment’ @ apply expand last assignment : = a:= a+b. b:= a–b. a′ = a–b ∧ b′=b ∧ c′=c |
| `ex139` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex140-R` | no | **FAIL** | step 3: empty hint (would need direct) |
| `ex5b` | yes | **PASS** | every apply ok, no gaps |
| `ex6a` | no | **FAIL** | no applicable suggestion from a law named ‘generalization’ @ apply generalization : ⇒ a ∨ b |
| `ex6c` | no | **FAIL** | no applicable suggestion from a law named ‘noncontradiction’ @ apply noncontradiction : = ⊥ ⇒ b |
| `ex6i` | no | **FAIL** | no applicable suggestion from a law named ‘noncontradiction’ @ apply noncontradiction : = ⊥ ⇒ b |
| `ex6j` | no | **FAIL** | no applicable suggestion from a law named ‘symmetry’ @ apply symmetry : = a ∨ ¬a ∨ b ∨ ¬b |
| `ex6r` | yes | **PASS** | every apply ok, no gaps |
| `ex7a` | yes | **PASS** | every apply ok, no gaps |
| `portation-top` | no | **FAIL** | step 1: unresolved hint “Material Implication, 3 times” |
| `portation` | yes | **PASS** | every apply ok, no gaps |
| `demo:portation` | yes | **PASS** | demo, no gaps |
| `demo:discharge` | yes | **PASS** | demo, no gaps |
| `demo:minimize` | yes | **PASS** | demo, no gaps |
| `demo:segment` | yes | **PASS** | demo, no gaps |
| `demo:fold` | yes | **PASS** | demo, no gaps |
| `demo:merge` | yes | **PASS** | demo, no gaps |
