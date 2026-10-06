# Examples dropped from the Netty picker

Picker = **audit PASS only**: every step `apply`s, **no gaps**, no `direct` dump.
See `AUDIT-CALCS.md` from `node netty-web/scripts/audit-calcs.mjs`.

## In picker (book)

| id | label |
|----|-------|
| portation | Law of Portation (aliases Material Implication→inclusion, Duality→duality) |
| ex6r | Portation proves a ⇒ (b ⇒ a) |
| ex5b | Excluded middle |
| ex7a | If-then-else by case analysis (rewritten: one law/step) |

Plus kernel demos: portation, discharge, minimize, segment, fold, merge.

## Dropped from picker (files remain under `public/examples/`)

| file | audit reason |
|------|----------------|
| ex6a | `apply specialization` failed in ⇒ session (before startDir fix — re-check) |
| ex6c, ex6i | `noncontradiction` does not rewrite `a ∧ ¬a ⇒ b` → `⊥ ⇒ b` in interactive apply |
| ex12ab | `inclusion` did not offer `¬drink ∨ ¬drive` → `¬¬drink ⇒ ¬drive` |
| ex6j | speculative rewrite; symmetry step failed |
| portation-top | “Material Implication, 3 times” — multi-apply book phrasing (#54/#56) |
| ex121*, ex136*, ex137*, ex139, ex140-R | program-theory laws missing (#55) |
| demo `gap` | intentionally gappy |
| demo `segfold` | UI gadget |

## Michal screenshot

ex7a on live site showed gap `!` after case analysis — caused by old `apply`→`direct`
fallback for “idempotence twice”. Current `ex7a.calc` is one-law-per-step and
**audit PASS**; loader no longer falls back to `direct`.
