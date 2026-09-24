# Netty (after interpreter core)

Standing decision 2026-09-23 (Michal): once the **interpreter core** is done, next product work is a Netty-style calculational proof tool. Use the Netty document as the guide for both the proof UX and growing the full aPToP / Unified Algebra surface language.

Source of truth for UX/grammar: https://www.cs.toronto.edu/~naiman/Netty_document.pdf

## Interpreter core (gate — do not start Netty UI before this)

- [x] Phase 1: fuelled AST + denote soundness + Blueprint
- [x] Phase 2a: fuel-free Eval + LoopBridge
- [x] Phase 2b: locals/frames, arrays, assertions/or
- [x] Phase 2c: concrete Demo syntax + `lake exe interp`
- [x] Phase 2d: time/`Prog.tick`, timed run, assert ≠ ensure (`223ec04`, 2026-09-23)

Concurrency (`||`), channels, ivar, full book syntax are **language growth**, not the gate. Grow them using Netty’s grammar as the checklist after the kernel MVP exists.

## Netty MVP (first slice after 2d READY)

1. [x] **Kernel** (library + headless CLI), 2026-09-23 on main: `Netty/` and `lake exe netty`.
   Proof document model (lines with depth, direction, zoom stack, gaps, focus), law lists as plain
   text files, suggestion generation (the document's six variants per law + one-way matching),
   commands as pure state transitions, JSON save/load, a script language with `undo`.
2. [x] **Replay target**, 2026-09-23: `netty --demo=portation` replays the document's page-0 proof and
   prints its proof pane; `Netty.Replay.portation_proves` / `portation_lines` / `portation_complete`
   check *in Lean* that the session ends with no gaps, fully zoomed out, and proving `a ⇒ (b ⇒ a)`.
   Two more replays (zoom + context, gap + fill) and one number-direction replay are checked the same
   way, and `netty --selftest` checks that the demo scripts parse to exactly those command lists.
3. [x] **Web UI**, 2026-09-23 on main: `Netty/Api.lean` + `netty --serve` + `netty-web/`.
   The kernel gained a request/response mode — one JSON request per line of standard input, one line
   of JSON back carrying the whole state: the lines with depth, margin connective, main operands
   (`Expr.operandTexts`, each with the parentheses it carries in the line) and focusable/zoomable
   flags; the context; the numbered suggestions with their unconstrained variables; the outcome; and
   the three text panes. The requests are `state`, `cmd` (one line of the *existing* script language),
   `demo`, `reset`, `save`, `load`; the script language's file commands are refused over that channel,
   so a proof file travels as text.
   `netty-web/` is the window: a Node server (only `typescript`/`@types/node`) spawning
   `lake exe netty --serve` behind `POST /api` on loopback, and a TypeScript client drawing the proof
   as structured lines — clickable parts for `zoom …` (main operands in the line, and from item 12 the
   runs of them under it), clickable line numbers for `focus N`,
   clickable suggestions for `apply #N`, a direct-entry box at the focus, undo / zoom out / save /
   load, a text view of the same three panes, and keys `0`–`9` / `u` / `o`. The document model is not
   duplicated in TypeScript. `netty --selftest` replays every demonstration through the service and
   saves and loads the result, so the protocol cannot drift.
   Residual, from the UI's own side: a saved proof carries the law list (~30 KB); laws are added by
   `NETTY_CMD` rather than from the window; the suggestion list is long because the kernel offers
   every variant that matches (the ones with unconstrained variables are greyed and come last); no
   ML ranking, no VS Code webview. (The display collapses the panes lacked are done, item 8.)
4. [ ] **Out of MVP:** ML suggestion ranking, VS Code webview, execute-hook, program/spec line types, channels.

5. [x] **Matching modulo associativity**, 2026-09-23 on main. `Expr.matchAll` flattens a pattern and a
   line that are associations of the same associative operator and tries every cut of the line's
   operands into as many non-empty *contiguous* segments as the pattern has operands, each rebuilt
   left-associated; a pattern operand that is not a law variable can only take one operand, since the
   pattern was flattened too. A variant can now match in several ways and each way is a suggestion, so
   `a ∧ b ⇒ a` offers both `x` and `x ∧ y` from `x ∧ y ∧ z`, `a ∧ a ≡ a` folds `x ∧ y ∧ x ∧ y`, and the
   same holds at the number level for `+` and `×`. The matcher is fuelled (fuel = the pattern's size,
   one unit per level of the pattern) *deliberately*: structural recursion is what lets `decide` run a
   whole session in Lean's kernel, which is how `Netty/Replay.lean` checks the replays.
   Witnessed in Lean (`specialization_reads_both_ways`, `symmetry_reads_both_ways`, `assoc_proves`,
   `no_match_without_a_law_variable`, all `propext` only) and by `netty --selftest`, which checks that
   every suggestion the whole law list offers for seven associations under all three directions is a
   *sound* step (401 of them) and that specialization reads `x ∧ y ∧ z` both ways.
   Matching went on modulo symmetry and modulo an identity element in item 9.

6. [x] **A law applied to a part of a line** (minimization), 2026-09-23 on main. `Doc.suggestions` now
   generates a suggestion for each *site* of the focused line: the whole line, and each of its **main
   operands** — the parts a single `zoom N` reaches and `Expr.operandTexts` draws as separate pieces.
   A part rewrite writes the line back with that part replaced by the instantiated right side, and its
   margin connective is the one a zoom in, an application and a zoom out would have written
   (`Doc.sites` / `Doc.rewriteAt`): the part's position turns the direction on the way in and back on
   the way out, so a step that is the part's direction inside is the level's direction outside, and a
   neutral position admits only `=`. No new soundness argument, then — the zoom rules are the argument,
   with the two lines the subproof would have added left out. Whole-line suggestions still come first,
   dedup and the identity-rewrite and direction gates are unchanged, and matching is still modulo
   associativity only.
   Witnessed in Lean (`idempotence_misses_the_whole_line`, `minimize_proves`, `minimize_complete`,
   `numberMinimize_proves`, `numberMinimize_is_the_only_successor_step`, all `propext` only): a fold of
   `y ∨ y` inside `x ∧ (y ∨ y)` that no whole-line match can make, and `n - m ≥ n - (m + 1)` from a
   `≤` law on the subtrahend, where the negative position turns the step around without a zoom.
   `netty --demo=minimize` is the same fold as a script, and `netty --selftest` grew the soundness
   sweep to 1388 suggested steps (nine lines, all three directions, positive, negative and neutral
   parts), all sound.
   One consequence: the context law `a ⇒ b` now also applies to parts of the line `a ⇒ b`, so the
   `discharge` demonstration's `apply context` had to name the line it writes (`apply context : = ⊤`).
   Still one level only — deeper positions are reached by zooming in. (Matching went modulo symmetry
   and an identity element in item 9.)

### NEXT, now that the three panes exist

The kernel residual below is what the window makes visible next: highlighting in the proof pane which
part of the line a suggestion would rewrite — `Suggestion.part` carries it since item 13, and the
window does not draw it. (Applying a law to a part of a line, anywhere-focus, the display collapses,
matching modulo symmetry and an identity element, contiguous association segments as sites, zooming
into one, clicking one in the window, ranking the suggestion list, and the gap-on-splice justification
are all done, 2026-09-23/24.) Phase 2e (LoopBridge / concurrency) stays parked.

### Kernel residuals to pick up alongside or after the UI

- Matching is modulo associativity, symmetry and the identity element (2026-09-23, items 5 and 9):
  `x ∧ y` matches `y ∧ x`, and a law written `x + 0` reads the line `n`. It is syntactic otherwise —
  no distributivity, no arithmetic, no normalisation.
- A law applies to the whole line, to each of its *main operands*, and to each contiguous *segment* of
  its association (`y ∧ z` inside `x ∧ y ∧ z`) — 2026-09-23/24, items 6 and 10. That is one level of
  minimization; deeper subterms are still reached by zooming in. Every one of those parts is also a
  level you can work inside (`Cmd.zoomIn` takes a `Part`, item 11): `zoom 1:2` opens a subproof on a
  segment and `out` splices it back, and the window offers every one of them to a click by the kernel's
  own name for it (item 12).
- The suggestion list is *ranked* by a written-down heuristic (`Doc.rank`, items 13 and 14), not
  learned: applicable before unconstrained, fewer unconstrained variables, the shorter line the step
  writes, then the more specific place, then the law file's own order. ML ranking stays out of MVP.
- The focus lands on any line of any *open* level (2026-09-23), the levels below it closing as a run of
  zoom-outs would. A line of a subproof that has already been zoomed out of is still refused —
  re-opening a closed level is not something the kernel does — and the web UI greys its number.
- A gap is carried out of the subproof that holds it (2026-09-24, item 15): zooming out of a level
  that still has a gap marks a gap on the line it was zoomed in from, so the outer step to the spliced
  line draws the document's warning sign. A subproof with no gaps splices as it always did.
- The display collapses are done (2026-09-23, item 8): two zoom-ins matched by two zoom-outs merge
  into one zoom step, and a subproof that is a single law application folds into its parent line with
  the law name moved up. They are a pass over the document, not a change to it.
- No `if … then … else … fi`, quantifiers, bunches, strings, lists, functions, scope (`〈v: d → b〉`),
  function application, hiding, deleting a region, or law query — each is a named section of the
  document and a named chunk of the grammar below.
- A conditional law (`x ≤ x + y ⇐ 0 ≤ y`) cannot yet be used at the number level: that is the
  document's type-checker-and-gap machinery.
- Lake does not track `Netty/laws/boolean.laws` as a build dependency; `netty --selftest` catches a
  stale build, but editing the law file needs the `.olean` deleted (or `Netty/Laws.lean` touched).

7. [x] **Anywhere-focus** (recomputing the zoom stack), 2026-09-23 on main. `Cmd.setFocus n` no longer
   insists that line `n` be in the innermost open level. `Doc.canFocus` says which lines a click may
   land on — any line of any *open* level — and `Doc.closeToDepth` does the recompute by running
   `Doc.zoomOut` (factored out of `Doc.step`) until the line's level is the innermost one again. So the
   state a click reaches is exactly the state the user could have reached by closing those levels
   themselves: each abandoned subproof still puts its bottom line back into the line it was zoomed in
   from, and the direction, type and context that come with the focus are the ones that level always
   had. The fuel is the number of open levels.
   Refused, and greyed in the window: a line of a subproof that has already been zoomed out of — deeper
   than the innermost open level, or before the first line of the open level at its own depth (an
   earlier, *closed* subproof at that depth). Re-opening a closed level is not something the kernel
   does.
   `Api`'s `focusable` is now just `Doc.canFocus`, so `netty-web/`'s line numbers became clickable for
   outer lines with no client logic added — only the gutter's tooltip, which now says whether a click
   would close a subproof.
   Witnessed in Lean, all by `decide`, all `propext` only: `anywhere_closes_the_stack`,
   `anywhere_leaves_the_subproof_closed`, `anywhere_proves` and `anywhere_is_discharge` — the
   `discharge` proof with `focus 0` in place of `out` writes *the very same document* — plus
   `nested_closes_both_levels` / `nested_puts_the_subproofs_back` (one click closes two levels) and
   `reopen_keeps_the_first_subproof_closed`. `netty --selftest` gained `focusTest`, which drives the
   request service the way the web client does: zoom in, check the outer line is reported `focusable`,
   `focus 0`, and check the subproof closed and its lines are refused.

8. [x] **Display collapses**, 2026-09-23 on main. A proof written by zooming keeps lines a reader does
   not need, and the document collapses two such patterns. `Doc.shownLines` is that collapse, as a
   *pass over* the document rather than a change to it: it says which lines a display draws, at what
   depth, and with what law name at the end of them. `Doc.lines` is untouched, so a saved proof is
   still the whole proof, the script language still calls a line by its index in `Doc.lines`, and a
   click still means what it meant.
   **Fold** (`Doc.foldHere`): a subproof that is a single law application is drawn as the line it was
   zoomed in from, with the law's name moved up onto that line; the two scaffolding lines are not
   drawn. What is left is exactly what applying that law to a *part* of the line would have drawn, so
   the long way round and the short way round are drawn alike.
   **Merge** (`Doc.mergeHere`): a level whose only two lines are the one a zoom in wrote and the one a
   zoom out wrote has held nothing of its own, so the subproof it held is drawn one level further out
   and its two lines are not drawn — the document's "two zoom-ins matched by two zoom-outs merge into
   one zoom step".
   `Doc.collapseStep` scans the drawn lines from the top and tries a merge before a fold, because a
   merge can expose a fold and not the other way round; `shownLines` runs it to a fixpoint with the
   number of lines for fuel, so a threefold zoom merges twice and then folds. A collapse fires only
   where the matching zoom out has already been written, so a level still being worked in is never
   collapsed, and `Doc.mayHide` refuses to hide the focus or a line a gap follows.
   `Doc.renderProof` and `Api.lineView` / `Api.stateView` draw `Doc.shownLines`, so the text pane and
   the three web panes show the collapses with no client logic added: a hidden line simply does not
   arrive and a lifted one arrives with a smaller `depth`. `Doc.note` moved from `Netty/Render.lean`
   to `Netty/Doc.lean`, where the pass needs it.
   Witnessed in Lean, all by `decide`, all `propext` only: `fold_keeps_its_four_lines`,
   `fold_collapses`, `fold_shows_what_minimize_shows` (drawn line for line as `minimize`),
   `merge_keeps_its_seven_lines`, `merge_collapses`, `mergeThenFold_collapses`,
   `merge_waits_for_the_zoom_out` and `gapInside_is_not_collapsed`. `netty --demo=fold` and
   `--demo=merge` print the pane before and after the zoom out that closes the level, so each collapse
   can be seen happening, and `netty --selftest` gained `collapseTest`, which checks the same through
   the request service. `focusTest`'s line count changed from four to two: the subproof a click closes
   there is a single law application, and now folds.
   Not done here: re-opening a closed level, and collapsing anything a law name or a warning sign
   hangs on.

9. [x] **Matching modulo symmetry and the identity element**, 2026-09-23 on main. `Netty/Law.lean`'s
   matcher now reads a line modulo all three of the things the document says a user should not have to
   spend a step on. `BinOp.comm` names the operators its `symmetry` laws are about (`∧ ∨ = ⧧` and
   `+ ×`) and `BinOp.identity` the units it names for them (`⊤` for `∧`, `⊥` for `∨`, `0` for `+`,
   `1` for `×`), both in `Netty/Expr.lean`.
   **Symmetry.** The group of line operands a pattern operand takes no longer has to be contiguous:
   `Expr.shares` offers every sub-list of what is left, each keeping the line's own order inside it.
   So `a ∧ b ⇒ a` reads `x ∧ y ∧ z` as `y ∧ (x ∧ z)` and offers every sub-conjunction, and `x ∧ y`
   matches `y ∧ x`. A symmetric operator that is *not* an association — `=` and `⧧` — is matched by
   trying its two operands both ways round instead.
   **Identity.** A pattern operand that *is* the unit may take no operands at all, so a law written
   `x + 0` reads the bare line `n`; and a unit the line writes may be struck out of it
   (`Expr.lineForms`), so `a ∧ a` reads `x ∧ ⊤ ∧ x`. Only a pattern operand that is *literally* the
   unit may take nothing — a law variable never quietly binds to a unit the line does not mention,
   which is what keeps `a ∧ b ⇒ a` from matching every line there is.
   Readings that need no rearrangement come first, so the old order is a prefix of the new one, and
   `Expr.matchAll` deduplicates, since symmetry and the identity can reach one substitution by more
   than one route. A line that is not an association of the pattern's operator is still rejected
   before any sharing out begins unless the pattern mentions that operator's unit, so the common
   reject path costs what it did: `Netty.Replay` went from 86s to 105s to check.
   No new soundness argument: the line and the matched left side differ only by an associativity, a
   symmetry or a unit, all of which are equalities. `netty --selftest`'s sweep says so by evaluation —
   2976 suggested steps now (up from 1388), over eleven lines including two that write a unit
   (`x ∧ ⊤ ∧ y`, `x ∨ ⊥ ∨ y`), all sound.
   Witnessed in Lean, all by `decide`, all `propext` only: `specialization_reads_every_way` and
   `symmetry_reads_every_way` (every sub-conjunction of `x ∧ y ∧ z`, the two associativity gives
   first), `swap_proves` (`x ∧ y ⇒ y` in one step, which no cut into contiguous segments can make),
   `symmetry_matches_a_swap`, `identity_is_elided`, `identity_is_struck_out`, `equality_is_symmetric`,
   `a_variable_does_not_take_the_unit` and `no_match_without_a_law_variable` (the two negative ones),
   and `numberUnit_elides_the_zero` / `numberUnit_proves` — `x + 0 ≤ x + 1` reading the bare line `n`
   and proving `n ≤ n + 1`, the one shape only the identity can reach. `netty --selftest`'s
   `matchTest` checks the same three readings through the compiled kernel.
   One consequence for a user: the suggestion list is longer, because a law reads a line every way the
   three allow and each way is a suggestion of its own.
   Not done here: distributivity, arithmetic, or any normalisation; the identities the document states
   for `⇒` and `=` (`⊤ ⇒ a ≡ a`, `⊤ = a ≡ a`) stay ordinary laws, since neither operator is an
   association a line is read apart into.

10. [x] **Contiguous association segments as sites**, 2026-09-24 on main. The document reads
   `x ∧ y ∧ z` as having the part `y ∧ z` just as it has the part `y`, so `Doc.sites` now offers, after
   the whole line and the single main operands, every contiguous run of two or more operands of an
   associative main operator that is shorter than the whole line. `Netty/Expr.lean` gained
   `segments` (the `(start, length)` pairs), `segmentExpr` (the run, rebuilt left-associated as
   `rebuildOp` writes an association), `replaceSegment` (the run put back), `segmentPos` and
   `segmentTy`; `Netty/Doc.lean` replaced `Site.operand : Option Nat` with `Site.part : Part`, where
   `Part` is `whole | operand i | segment start len`, and `Doc.rewriteAt` puts a part back through
   `Part.replace`.
   No new soundness argument. An associative operator puts every one of its operands in the same
   position, so a run of them is in that same position, and the type, the direction inside and the
   connective the step writes outside are word for word those of a single main operand — the story
   item 6 already had, read for a run instead of for one. `×` is the interesting case: it is
   associative but its operands are neutral (a factor is monotonic only for a nonnegative other), so a
   segment of it admits only `=`, which `times_segments_are_neutral` witnesses.
   What it buys: a law that matches two of several operands folds them where they stand. `a ∧ a ≡ a`
   takes `x ∧ y ∧ y ∧ z` to `x ∧ y ∧ z` in one step — a step no site the kernel had before could make,
   since idempotence matches neither the whole line (no sharing out of four conjuncts makes two equal
   halves) nor any single main operand (they are the bare identifiers `x`, `y`, `y`, `z`).
   Witnessed in Lean, all by `decide`, all `propext` only: `segmentLine_segments` (the five runs of a
   four-operand association), `a_pair_has_no_segments`, `idempotence_misses_the_whole_association` and
   `idempotence_misses_every_operand` (the two negative ones), `segmentFold_proves` /
   `segmentFold_complete` / `segmentFold_is_the_only_fold`, `times_segments_are_neutral`, and
   `symmetry_reads_every_way`, whose list grew by the two swaps the segment sites of `x ∧ y ∧ z` make.
   `netty --demo=segment` shows the step; `netty --selftest` checks the same reading through the
   compiled kernel and sweeps 4565 suggested steps (up from 2976), over twelve lines, all sound.
   One consequence for a user: the suggestion list is longer again. Ranking it is still out of MVP.
   Not done here: the gap-on-splice justification, re-opening closed levels, conditional laws at the
   number level, distributivity, arithmetic or normalisation. (Segment *zoom* was the next chunk,
   item 11.)

11. [x] **Segment zoom** (`Cmd.zoomIn` on a part), 2026-09-24 on main. A part was a place a law is
   applied to; it is now also a level you can work *inside*. `Cmd.zoomIn` takes a `Part` instead of a
   main-operand number, so `Part` — `whole | operand i | segment start len` — is the one place that
   says what a part is, for both a site rewrite and a zoom. `Part` gained `exprOf`, `posOf`, `tyOf`,
   `contextOf`, `render` and `zoomable` in `Netty/Doc.lean`, and `Doc.sites` is now one `filterMap`
   over `Doc.parts` that reads every field off those, so a site and a zoom in *cannot* disagree about
   a part's expression, type, direction or position — that was two code paths before and is one now.
   `Frame.operand : Nat` became `Frame.part : Part`, and `Doc.zoomOut` splices through
   `Part.replace`, the same function `Doc.rewriteAt` uses. `Expr.contextOf` was generalized to
   `Expr.contextOfRange e start len` (the operands *outside* the run become the context;
   `contextOf e i` is the run of one at `i`), so zooming into `y ∧ y` inside `x ∧ y ∧ y ∧ z` gains `x`
   and `z` exactly as zooming into one operand gains the other three. `⇒` and `⇐`, whose context
   depends on which operand was chosen, are not associations, so for them a run is always one operand
   and nothing changed. `Part.whole` is refused as a zoom target: it is the level one is already on.
   Surface: `zoom S:L` in the script language beside `zoom N` (`zoom 1:1` is refused with the advice
   to write `zoom 1`). The save format went to 2, since a level now records a `Part` where it recorded
   an operand number, and a format 1 file is refused rather than read with its zooms mistaken for
   zooms into the whole line.
   Nothing new is claimed. The subproof's first line is `Expr.segmentExpr start len`, its type and
   direction are `Expr.segmentTy` and `Dir.zoom (Expr.segmentPos …)` — the very numbers the segment
   *site* already carried, and item 10's argument for them — and the zoom out writes `=` when the
   position is neutral or the subproof proved an equality and the parent's direction otherwise, which
   is the rule `Doc.zoomOut` already had.
   Witnessed in Lean, all by `decide`, all `propext` only: `segmentZoom_opens_the_segment` and
   `segmentZoom_remembers_the_run` (the level's first line, and the frame that lets the splice
   happen), `segmentZoom_gains_the_others` (`x` and `z` as context), `times_segment_zoom_is_neutral`
   (a `×` segment flattens the direction to `=`, the site's rule read off the level),
   `the_whole_line_is_not_a_zoom_target`, `segmentZoom_proves` / `segmentZoom_complete`,
   `segmentZoom_splices_what_the_site_writes` (the spliced line is, connective and formula, the line
   `segmentFold` writes in one step), and `segmentZoom_collapses` /
   `segmentZoom_shows_what_segmentFold_shows` — the display draws the long way round as the short way
   round, with nothing added to the collapses. Every existing operand-zoom replay, collapse,
   anywhere-focus and segment-site witness is unchanged but for `.zoomIn 1` now reading
   `.zoomIn (.operand 1)`.
   `netty --demo=segfold` shows it: `zoom 1:2`, the context pane with `x` and `z`, the fold, and the
   splice, printed before and after the zoom out. `netty --selftest` gained a `collapseTest` check
   that `segfold` draws what `segment` draws, which is the segment zoom driven end to end through the
   request service the web client talks to.
   Not done here: a *click* on a segment in `netty-web/` — the script language has `zoom S:L`, the
   window still offers only the single main operands — the gap-on-splice justification, re-opening
   closed levels, conditional laws at the number level, distributivity, arithmetic or normalisation.

12. [x] **Segment clicking in the window**, 2026-09-24 on main. `zoom S:L` existed in the script
   language from item 11, but `netty-web/` drew only the single main operands as click targets. Now the
   window offers every part the kernel does, and it offers them *by the kernel's own name for them*.
   `Api.LineView` gained `zooms : List PartView`, one entry per zoomable part of the line before the
   focus in `Doc.parts` order — each main operand, then each contiguous segment — carrying `name` (what
   `zoom` calls it: `Part.render`, so `1` or `1:2`), `text` (the part as it stands in the line:
   `Part.textIn`), and `start` / `len` (`Part.span`). `Part` gained `span` and `textIn` in
   `Netty/Doc.lean`, so the naming and the rendering of a part live where the part does.
   `LineView.zoomable` is now just `!zooms.isEmpty`, which is the same predicate it was, computed once.
   The client sends `zoom ${z.name}` and composes no name itself, which is the point: a click cannot
   mean a different part from the one a suggestion's site or a script zoom means, because there is one
   string and the kernel wrote it. A run of two or more operands has nowhere in the line to be clicked
   — its operands are not adjacent to any one button — so the runs are offered on a `runs:` line under
   the line they belong to, as dashed buttons labelled with the run. Single operands are clicked in the
   line as before. `Part.whole` is never offered: `Part.zoomable` filters it, as the kernel's own
   `Cmd.zoomIn` refuses it.
   `netty --selftest` gained `zoomTest`, which drives the click path through the request service the
   client talks to: for `x ∧ y ∧ y ∧ z` the answer must offer exactly
   `0 1 2 3 0:2 0:3 1:2 1:3 2:2` with the texts `x y y z`, `x ∧ y`, `x ∧ y ∧ y`, `y ∧ y`, `y ∧ y ∧ z`,
   `y ∧ z`; every one of the nine must be a name the kernel accepts and must open a level whose first
   line is the part the button was labelled with; clicking the run `1:2` must gain `x` and `z` as
   context; and the outer line must then offer nothing, since it is no longer the line before the
   focus. Non-associations offer no runs (`⇒` gets none), `×` gets both of its (it is associative
   though neutral), and an atom offers nothing at all.
   Not done here: highlighting the site a suggestion came from, ranking the suggestion list, the
   gap-on-splice justification, re-opening closed levels, conditional laws at the number level,
   distributivity, arithmetic or normalisation.

13. [x] **Deterministic suggestion ranking**, 2026-09-24 on main. Every widening of matching had made
   the list longer — modulo associativity, symmetry and the identity element, then every main operand
   and every association segment as a place a law may be applied to — and it was the loudest thing the
   window showed: 227 steps for `x ∧ y ∧ y ∧ z` under the shipped law list, in the order they happened
   to be generated. `Doc.rank` is now the order, and it is a heuristic *written down* rather than
   learned (ML ranking stays out of MVP). Most important key first:
   (1) applicable before unconstrained — a suggestion with a free law variable cannot be taken, so
   every one that can comes first, which is the split the pane already drew as greyed rows;
   (2) the more specific place, `Part.rank` — the whole line `0`, a single main operand `1`, a run of
   operands its own length — so the whole line, then the operands, then the shorter runs before the
   longer;
   (3) fewer unconstrained variables, among those that cannot yet be taken;
   (4) the shorter line it writes, since a calculation is usually after the step that folds and every
   law that can fold has a variant that can pad; and
   (5) the order the suggestions were made in — the context's laws, then the law list's own order, then
   the variants, then `Expr.matchAll`'s readings — so the last word belongs to the law file, the one
   part of the order a user writes themselves.
   `Suggestion` gained `part : Part`, which is what key (2) reads; `dedup` became `dedupBy` on
   `(law, op, result)`, so two places that write one and the same line are still offered once — one
   step, not two — credited to the first place that made it, which is the one key (2) prefers.
   The sort is `stableBy`, one bucket pass per distinct key value, composed least-important key first:
   stable by construction, and structurally recursive rather than well-founded, which is what keeps
   `decide` able to run a whole session in Lean's kernel. `Netty.Replay` went from 166s to 192s.
   Witnessed in Lean, by `decide`, `propext` only: `suggestions_are_ranked` — for `x ∧ y ∧ z` under the
   whole law list the keys never go backwards, and ranking the ranked list is the ranked list, which is
   what it means for the order to be total and the sort stable. `specialization_reads_every_way` now
   reads `x, z, y, x ∧ y, y ∧ z, x ∧ z` — the same six sub-conjunctions, the single conjuncts first
   because key (4) puts the shorter line first; `symmetry_reads_every_way` is unchanged, its seven
   results being all of one size.
   `netty --selftest` gained `rankTest`, on the 227-step line: the keys never go backwards, ranking the
   ranked list changes nothing, asking twice gives the same list, all 207 applicable steps come before
   all 20 unconstrained ones, and `x ∧ y ∧ z` — the fold neither the whole line nor a single operand
   can make — leads the steps offered on a run of operands, ahead of the two longer runs that overlap
   it. The window and `SuggestionView` are untouched: the client draws the kernel's order and does not
   re-sort, so `apply #N` and the keys `0`–`9` are the ranked positions.
   Measured effect: the first suggestion for `x ∧ y ∧ y ∧ z` went from `¬¬(x ∧ y ∧ y ∧ z)` (a pure
   padding) to `y ∧ (x ∧ z)` (a real contraction), and `x ∧ y ∧ z` from position 163 to 124.
   **Worth knowing:** key (2) outranked key (4) here, as that task specified, so all ~120 whole-line
   rearrangements came before any step on a part and the segment fold could not rise above them. That
   was swapped in item 14.
   Not done here: highlighting in the proof pane which part a suggestion would rewrite (the field is
   there now), ML ranking, the gap-on-splice justification, re-opening closed levels, conditional laws
   at the number level, distributivity, arithmetic or normalisation.

14. [x] **The shorter line outranks the place**, 2026-09-24 on main (Michal's call, on the measurement
   item 13 reported). Item 13's order put the place of a step above the length of the line it writes,
   and the measurement showed what that costs: on `x ∧ y ∧ y ∧ z` under the shipped law list,
   `x ∧ y ∧ y ∧ z = x ∧ y ∧ z` — the fold that neither the whole line nor any single operand can make —
   was the 124th of 227 suggestions, behind some hundred rearrangements of the whole line, because every
   whole-line step outranked every step on a part. The two `stableBy` passes in `Doc.rank` are swapped,
   so the order is now: applicable before unconstrained; fewer unconstrained variables; **the shorter
   line the step writes**; then the more specific place (whole line, single operands, shorter runs,
   longer runs); then the law file's own order. That fold is now the **3rd** of the 227, and the only
   two ahead of it write a line just as short — `distributive` contracting the whole line.
   The place still does real work: it is what separates steps that write lines of the same length, which
   is why `symmetry_reads_every_way`'s seven results — all of one size — are unchanged, five whole-line
   swaps before two segment swaps. `specialization_reads_every_way` is unchanged too: all six of its
   readings are whole-line, so the length key already ordered them.
   `Netty/Api.lean` and `netty-web/` are still untouched — the client draws the kernel's order and does
   not re-sort. `Replay.key` and `rankTest`'s key list are the new order, and `rankTest` now checks the
   point head on: the fold is the third step offered, the two ahead of it write a line no longer than
   it does, and it is still the first step offered on a run of operands.
   Not done here: highlighting in the proof pane which part a suggestion would rewrite, ML ranking, the
   gap-on-splice justification, re-opening closed levels, conditional laws at the number level,
   distributivity, arithmetic or normalisation.

15. [x] **The gap-on-splice justification**, 2026-09-24 on main. `Doc.zoomOut` spliced every subproof
   back the same way — `why := "zoom out"`, no gap — so after a direct entry *inside* a level, the
   outer line before the splice drew neither a law name nor `!`, and a reader of the outer level saw a
   step with nothing said about it. But a zoom out justifies the outer step *by the subproof*, and a
   subproof with a hole in it does not justify anything; the Netty document puts a warning on the line
   just before every logical gap, and after the splice that line is the one the zoom was made from.
   So `Doc.zoomOut` now marks a gap on `Frame.zoomLine` when the level being closed still holds one
   (`Doc.openGaps`: the gaps at or after the level's first line — every line from there on is this
   level's or a subproof's of it, and a subproof already left its own gap on a line of this level, so
   the carrying is transitive by construction and needs no recursion). The undo branch — zooming out of
   a level of one line — marks nothing: no step has been taken there, and only a step leaves a gap.
   A level with no gaps splices exactly as before: a single law application still folds with its name
   lifted (item 8), and a longer justified subproof still leaves the outer step unannotated, its
   justification being the lines inside. Nothing else moved: `Doc.note` already drew `!` for a gap,
   `Doc.mayHide` already refused to collapse a line a gap follows, `Doc.outcome` already refused a
   document with a gap in it, and `Api.LineView` already carried `gap` and `note` — so the window shows
   the warning with no client change, and an abandoned gappy subproof carries its gap out through a
   *click* too, since `Doc.closeToDepth` closes levels by running `Doc.zoomOut`.
   Witnessed in Lean, all by `decide`, all `propext` only: `gapInside_gaps_the_line_before_the_splice`
   and `gapInside_proves_nothing` (the direct entry inside a closed subproof),
   `fold_splices_without_a_gap` and `merge_splices_without_a_gap` (the negative ones — a one-step and a
   two-step justified subproof leave the outer line clean), `gapCarries_carries_it_all_the_way_out` and
   `gapCarries_is_not_collapsed` (two levels down, a gap at each level and no collapse over any of
   them), and `gapCarries_is_the_same_by_clicking` (`focus 0` writes the very same lines as the two
   zoom-outs). `gapInside_is_not_collapsed` now reads `["!", "!", "", ""]` where it read
   `["", "!", "", ""]` — that second warning sign is the whole change, seen from the display.
   `netty --selftest` gained `gapTest`, which drives it through the request service the window talks
   to: the same three commands with the subproof's step typed in and with it taken from `idempotent`,
   the first leaving four lines with warnings on lines 0 and 1 and claiming nothing, the second leaving
   the two folded lines with `idempotent` lifted and a proof. It is not a `--demo=`, because a proof
   that keeps a gap never proves anything and `--demo=` runs only proofs that do.
   Not done here: highlighting in the proof pane which part a suggestion would rewrite, re-opening
   closed levels, conditional laws at the number level, ML ranking, distributivity, arithmetic or
   normalisation.

## Then grow language ↔ Netty grammar

Use Netty’s LR/LL grammar as the roadmap for surface syntax and Prog constructs (var/ivar/chan/frame, `||`, `!`/`?`, quantifiers, functions, …), tying each chunk to existing LaPToP theory modules where they already exist (`Concurrency`, `Interaction`, …) and to `interp` where execution suggestions apply.

## Non-goals

- First UI inside Lean Infoview
- Rewriting an old Netty desktop binary as the starting point
- Claiming full aPToP surface before the kernel can host boolean/number calculations

## Kick when ready

When status-line is READY after 2d (or Michal asks earlier): write `.sci/task.md` for “Netty kernel MVP” (or a new repo if Michal prefers a separate project), kick Claude / start implementation, and keep laptop interpreter maintenance on the no-idle queue only if NEXT still has interpreter residuals.
