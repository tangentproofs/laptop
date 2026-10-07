# Examples dropped from the Netty picker

Picker = **audit PASS only** for *loading*; hierarchical UI also *shows* FAIL/MISSING
(disabled, with reason). See [`BOOK-CENSUS.md`](BOOK-CENSUS.md) for the full inventory
and [`AUDIT-CALCS.md`](AUDIT-CALCS.md) from `node netty-web/scripts/audit-calcs.mjs`.

## In picker as loadable (book PASS)

| id | label |
|----|-------|
| portation | Law of Portation |
| ex5b | Excluded middle |
| ex5c | Simplify x ⇒ ¬x |
| ex5d | Simplify x ⇐ ¬x |
| ex5f | Simplify x ⧧ ¬x |
| ex6a | Specialization then generalization |
| ex6c | Portation and noncontradiction |
| ex6g | a ∧ ¬b ⇒ a ∨ b |
| ex6i | Contradiction implies anything |
| ex6j | Either a ⇒ b or b ⇒ a |
| ex6r | Portation proves a ⇒ (b ⇒ a) |
| ex7a | If-then-else by case analysis |
| ex12ab | Don't drink and drive |
| ex12ae | Don't drink and drive ≡ ¬drink ∨ ¬drive |
| ex12bc | drink ⇒ ¬drive ≡ drive ⇒ ¬drink |
| ex121a | Substitution after x:= y+1 |
| ex121b | Substitution into a conjunction |
| ex121f | Assignment then ok |
| ex121g | Two assignments |

Plus kernel demos: portation, discharge, minimize, segment, fold, merge.

## Visible but not loadable (FAIL; files under `public/examples/`)

| file | audit reason |
|------|----------------|
| portation-top | Nested inclusion after two MI steps needs zoom; book "3 times" not one apply (#54) |
| ex136a/b | Compound book hints ("Associative Law for binary =", "Associativity and Symmetry of ⧧") |
| ex137a, ex139, ex140-R | Empty hints / multi-phrase steps (would need direct) |
| ex137b | Later substitution step fails on arithmetic shape |

## Kernel / loader notes (this branch)

- `state` / `spec` are interactive script commands (serve + CLI) so program rules apply (#55 still open for full refine workflows).
- Apply names are lowercased at parse time ("Substitution Law" → `substitution law`).
- calc-load aliases map book phrases; generalization emits `with b := …` for the hole.
- Hierarchical examples picker: `manifest.json` → chapter → section → proof; PASS buttons load; FAIL/MISSING disabled with tooltip.
- Examples page redirects to Interpreter; one Symbols dock (desktop) / sheet (mobile).
