# Examples dropped from the Netty picker

Picker = **audit PASS only**: every step `apply`s, **no gaps**, no `direct` dump.
See `AUDIT-CALCS.md` from `node netty-web/scripts/audit-calcs.mjs`.

## In picker (book)

| id | label |
|----|-------|
| portation | Law of Portation (Material Implication→inclusion, Duality→duality) |
| ex6r | Portation proves a ⇒ (b ⇒ a) |
| ex5b | Excluded middle |
| ex6a | Specialization then generalization |
| ex6c | Portation and noncontradiction |
| ex6i | Contradiction implies anything |
| ex6j | Either a ⇒ b or b ⇒ a |
| ex7a | If-then-else by case analysis |
| ex12ab | Don't drink and drive |
| ex121a | Substitution after x:= y+1 |
| ex121b | Substitution into a conjunction |
| ex121f | Assignment then ok |
| ex121g | Two assignments |

Plus kernel demos: portation, discharge, minimize, segment, fold, merge.

## Dropped from picker (files remain under `public/examples/`)

| file | audit reason |
|------|----------------|
| portation-top | Nested inclusion after two MI steps needs zoom; book "3 times" not one apply (#54) |
| ex136a/b | Compound book hints ("Associative Law for binary =", "Associativity and Symmetry of ⧧") |
| ex137a, ex139, ex140-R | Empty hints / multi-phrase steps (would need direct) |
| ex137b | Later substitution step fails on arithmetic shape |
| demo `gap` | intentionally gappy |
| demo `segfold` | UI gadget |

## Kernel / loader notes (this branch)

- `state` / `spec` are interactive script commands (serve + CLI) so program rules apply.
- Apply names are lowercased at parse time ("Substitution Law" → `substitution law`).
- calc-load aliases map book phrases; generalization emits `with b := …` for the hole.
- Examples page redirects to Interpreter; one Symbols dock (desktop) / sheet (mobile).
