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

Everything the window made visible is done (2026-09-23/24): applying a law to a part of a line,
anywhere-focus, the display collapses, matching modulo symmetry and an identity element, contiguous
association segments as sites, zooming into one, clicking one in the window, ranking the suggestion
list, the gap-on-splice justification, highlighting the site a suggestion would rewrite, and going
back into a closed level, conditional laws at both levels, and the small dialog box that supplies a law
variable by hand. What is left is the named chunks of the grammar below, and the one thing the kernel
still says out loud that it cannot do: check a number law by anything better than small integers. Phase
2e (LoopBridge / concurrency) stays parked.

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
- A suggestion says *where* it would rewrite, and the window draws it (item 16): `Suggestion.part`
  reaches the client as `SuggestionView.site`, in the same shape and under the same name as a zoom
  target, so pointing at a suggestion lights up that part of the line before the focus.
- The suggestion list is *ranked* by a written-down heuristic (`Doc.rank`, items 13 and 14), not
  learned: applicable before unconstrained, fewer unconstrained variables, the shorter line the step
  writes, then the more specific place, then the law file's own order. ML ranking stays out of MVP.
- The focus lands on any line of the proof (2026-09-23, item 7; 2026-09-24, item 17): levels that start
  after it close as a run of zoom-outs would, and a subproof that was zoomed out of re-opens as the
  exact inverse of that zoom-out. What is refused, and greyed in the window, is a subproof closed
  *before* later work was written: going back in would take that work with it.
- A gap is carried out of the subproof that holds it (2026-09-24, item 15): zooming out of a level
  that still has a gap marks a gap on the line it was zoomed in from, so the outer step to the spliced
  line draws the document's warning sign. A subproof with no gaps splices as it always did.
- The display collapses are done (2026-09-23, item 8): two zoom-ins matched by two zoom-outs merge
  into one zoom step, and a subproof that is a single law application folds into its parent line with
  the law name moved up. They are a pass over the document, not a change to it.
- No `if … then … else … fi`, quantifiers, bunches, strings, lists, functions, scope (`〈v: d → b〉`),
  function application, hiding, deleting a region, or law query — each is a named section of the
  document and a named chunk of the grammar below.
- A law of the form `Q ⇒ P` whose consequent is a relation is read with `P` in the margin and `Q` as a
  premise, at both types (2026-09-24, items 18 and 19): `x ≤ x + y ⇐ 0 ≤ y` is a step a number line can
  take and `(a ⇒ b) ⇒ (a ∧ c ⇒ b ∧ c)` one a boolean line can. The premise is settled by the laws in
  force — the `context` a zoom in supplies is how a domain condition or a hypothesis gets in force — or
  it is not, in which case the step leaves the document's warning sign with the premise recorded beside
  it. Nothing that needs nothing is buried: conditional readings come last in `Law.variants`, so a
  dedup keeps the reading with no premise, and `Doc.rank` puts every step that needs nothing first.
- A suggestion that leaves a law variable free is taken by *supplying* it, and only by supplying it
  (2026-09-24, item 20): `Cmd.apply` and `Cmd.applyNamed` carry a `Subst`, the script says
  `apply … with b := y`, and the window opens one field per free variable when the greyed row is
  clicked. The kernel never guesses: a missing binding is refused as before, a binding for a variable
  the suggestion has not got is refused too, and the premise is asked again after the bindings, because
  supplying a variable can turn a premise nothing could settle into one the context settles. That is
  what makes monotonicity and transitivity — which relate the line to a third formula the line does not
  determine — usable at all.
- `Netty/laws/number.laws` is a small example list, not §11.3.2, and it is not *decided* the way the
  boolean list is: `Law.holdsOnInts` checks each law on the integers `-2 … 2`, which a law false in
  general can pass. Number laws are trusted as transcribed; arithmetic stays out of scope.
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
   `anywhere_proves` and `anywhere_is_discharge` — the `discharge` proof with `focus 0` in place of
   `out` writes *the very same document* — plus `nested_closes_both_levels` /
   `nested_puts_the_subproofs_back` (one click closes two levels). `netty --selftest` gained
   `focusTest`, which drives the request service the way the web client does: zoom in, check the outer
   line is reported `focusable`, `focus 0`, and check the subproof closed.
   Superseded in part by item 17, which re-opens a closed level: the two witnesses that recorded the
   refusal as final (`anywhere_leaves_the_subproof_closed` and
   `reopen_keeps_the_first_subproof_closed`) are gone, and their successors say the opposite. What is
   still refused there is narrower — a subproof closed before later work — and still greyed.

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

16. [x] **Highlighting the site a suggestion would rewrite**, 2026-09-24 on main. `Suggestion.part` has
   carried the place a step rewrites since the ranking (item 13), and the window drew none of it: the
   answer's `SuggestionView` had `law`, `op`, `result` and `holes` and nothing about *where*, so the
   document's minimization story — a law applied to a part of a line — was invisible in the pane that
   offers it. Now `SuggestionView.site : PartView` carries it, and pointing at a suggestion lights that
   part up in the proof pane.
   The site travels in the *same shape and under the same name* as a zoom target. `Api.partView` is one
   function — `name := Part.render`, `text := Part.textIn`, `start`/`len := Part.span` — and both
   `LineView.zooms` and `SuggestionView.site` are built by it, so a suggestion's site and a click's zoom
   target cannot disagree about what a part is called or how it reads. The whole line is a part too, and
   a client tells it from a run by `len = 0` (`Part.span` counts no operands for it); it never appears
   among the zoom targets, `Part.zoomable` refusing it as `Cmd.zoomIn` does.
   In `netty-web/`, `formula` now marks each operand `data-operand=i` and each operator written between
   two of them `data-op-before=i`, and `showSite` writes a `site` class over the run the pointer's
   suggestion names — the whole formula for a whole-line step, one operand for a step on one, a run of
   operands with the operators between for a step on a run, and that run's dashed button below the line
   with it. It writes classes rather than redrawing, because a redraw under the pointer takes the row
   being pointed at out of the document. `pointerenter`/`pointerleave` and `focus`/`blur` drive it, so
   the keyboard lights the same part the pointer does. No new layout and no new request: the three panes
   are what they were.
   Witnessed in Lean, by `decide`, `propext` only: `segmentFold_is_credited_to_the_run` — on
   `x ∧ y ∧ y ∧ z` the fold that only a run can make is credited to `.segment 1 2` and the padding by
   `double negation` to `.whole`. `netty --selftest` gained `siteTest`, which reads it off the request
   service the client talks to: that fold's site is `1:2` reading `y ∧ y`, the padding's site is the
   whole line with `len = 0`, and all 227 sites on that line are parts the same answer offers as zoom
   targets, each reading letter for letter as the part it names — so a highlight can always be drawn,
   and it cannot name a part the line does not have.
   Not done here: re-opening closed levels, conditional laws at the number level, ML ranking,
   distributivity, arithmetic or normalisation.

17. [x] **Going back into a closed level**, 2026-09-24 on main. Until now a click could land on any line
   of an *open* level and nowhere else: a subproof that had been zoomed out of was closed for good, the
   window greyed its number, and two witnesses recorded that as intentional. The Netty document lets
   you go back in and keep working, so now so does the kernel.
   The move is made of two steps and nothing else, which is what makes the state it reaches one the user
   could have reached by zooming and never left. `Doc.closeToDepth` closes levels, as before.
   `Doc.reopenStep` is new and is the **exact inverse of `Doc.zoomOut`**: the line that zoom-out wrote
   goes away again, and the frame is rebuilt from what the level's first line carries — its type, its
   direction and (new field `Line.part`) the part of the line above that the zoom in opened it on — with
   the position and the context recomputed from that part off a line the zoom-out did not change. So the
   frame is the one that level always had, down to its context laws, and `reopen_undoes_the_zoom_out`
   witnesses the round trip as an equality of whole documents, stack and focus included.
   The gap the zoom-out may have carried out is taken back with it. That is exactly the flag the
   zoom-out wrote: the last line of a level never carries a gap — a gap marks the step to the *next*
   line and there is none — so the line was clean when the zoom in left it. Going in and out of a
   subproof that holds a gap therefore changes nothing at all
   (`reopen_then_zoom_out_is_the_same_document`).
   `Doc.refocus` is the whole of `focus N`: close the levels that start after the line, re-open the
   closed levels it is inside (one `reopenStep` each, outermost first), then close anything still open
   below it. Each phase is bounded — closing spends a level, re-opening spends a line. `Doc.canFocus`
   is now *defined* as `refocus` succeeding, so the predicate the window greys by and the move a click
   makes cannot disagree; the old structural test survives as `Doc.inOpenLevel`, which is what
   `refocus` uses inside and what `Doc.reopensOn` subtracts to say which of the two moves a click would
   make.
   What is refused is narrow and honest: a subproof closed *before* later work was written. Taking its
   zoom-out back would take that work with it, so the kernel says so and the window greys it with a
   tooltip that says why. A collapsed subproof is not drawn at all, so there is nothing to click on it
   — re-opening reaches the subproofs a display draws, which is every subproof of more than one step;
   and the other direction takes care of itself, a re-opened level holding the focus never being
   collapsed.
   In `netty-web/`, `LineView` gained `reopens` and the gutter tooltip now says which of the three
   things a click would do (stay, close subproofs, or go back into one) and, when it is greyed, why.
   No layout and no new request.
   Witnessed in Lean, all by `decide`, all `propext` (two also `Quot.sound`, for the document
   equalities): `anywhere_leaves_every_line_open_to_a_click` and `anywhere_says_which_clicks_reopen`
   (every line of that proof is reachable, and exactly the three of the closed subproof re-open it),
   `click_reopens_the_subproof` (focus, depth, one line fewer, and the zoom in's context in force
   again), `reopen_undoes_the_zoom_out`, `work_after_keeps_the_subproof_closed` (the refusal),
   `reopen_reaches_the_first_subproof` and `reopen_closes_the_new_level_first` (a new level at the same
   depth is closed first, as the undo the document says it is), `nested_reopens_both_levels` (two
   levels back in, two contexts), `reopen_takes_the_carried_gap_back` and
   `reopen_then_zoom_out_is_the_same_document`. `netty --selftest`'s `focusTest` now goes back into the
   subproof it closed, checks all three of its lines are drawn again, and checks that the same click is
   refused once a line has been written after the zoom-out.
   Not done here: conditional laws at the number level, ML ranking, distributivity, arithmetic or
   normalisation.

18. [x] **Conditional laws at the number level**, 2026-09-24 on main. A law such as
   `x ≤ x + y ⇐ 0 ≤ y` was unusable where it is most wanted. Its own main operator is `⇐`, and a law's
   readings put its own operator in the margin, so the tool offered it only to a boolean line; a number
   line, whose margin wants `≤`, was never offered it at all.
   `Law.conditional` is the reading that fixes that: for a law of the form `Q ⇒ P` or `P ⇐ Q` whose
   consequent `P` is a relation that stands in a *number* margin, the consequent goes in the margin and
   `Q` is left over as a premise — both ways round, as `Law.forms` offers both directions of a law. The
   reading is generated only for the number directions `≤ < ≥ >`, and the reason is written down: a
   boolean conditional law already stands in a boolean margin as it is, so reading it conditionally as
   well would offer every such law a second time with a premise attached and bury the steps that need
   nothing. Doing it for booleans too — so that `(a ⇒ b) ⇒ (a ∧ c ⇒ b ∧ c)` could rewrite `a ∧ c` under
   the premise `a ⇒ b` — is a later round; the ranking key it needs is already here.
   The premise is not a new kind of obligation, which is the whole of the design. `Doc.suggestions`
   instantiates it with the same match and asks `Law.settles` whether the laws in force settle it —
   which is the same match the pane would make on a line holding the premise, one step and by an
   unconditional reading, so the question cannot recur. A settled premise is no premise and the step is
   an ordinary step; an unsettled one is carried on the suggestion, and taking it leaves the gap direct
   entry leaves, with the premise recorded beside it on the line (`Line.premise`) as what would close
   it. `Doc.outcome` refuses to say what such a proof proves, exactly as for any other gap. `Doc.rank`
   gained one key, under applicability and over everything else: a step that needs nothing before a
   step that leaves a gap. The premise's own free variables count as holes, because a premise one
   cannot even state is not an obligation one can take on.
   Where a domain condition comes from is the document's answer: the context. Zooming in to the
   consequent of `0 ≤ m ⇒ n ≤ n + m` puts `0 ≤ m` in force, and from there the reading that needs it
   carries no premise while the one that needs `0 ≤ n` says so — one law, one line, one pane, the two
   side by side.
   `Netty/laws/number.laws` is a new example law list — six laws, not §11.3.2 — with `Laws.number`
   reading it at compile time as `Laws.boolean` is read. It is checked by `Law.holdsOnInts` on the
   integers `-2 … 2` (`number_holdsOnInts`, by `decide`), and the limit is stated rather than glossed:
   that is a test a law false in general can pass, where `boolean_isTautology` decides a boolean law.
   `Expr.evalInt` / `Expr.evalProp` exist for that check and for nothing else — no suggestion does
   arithmetic.
   In the panes: `renderSuggestions` writes "leaves a gap: 0 ≤ m" against a row that would leave one,
   `SuggestionView.premise` and `LineView.premise` carry it to the window, and `netty-web/` marks such
   a row and says in the gutter's tooltip what a gap is for. A step that leaves a gap is never offered
   as though it did not.
   Witnessed in Lean, all by `decide`, all `propext` only: `context_settles_the_premise`,
   `a_law_settles_a_ground_premise` and `nothing_settles_zero_le_m` (the three ways the question can
   go); `bound_proves` and `bound_complete` — the proof of `0 ≤ m ⇒ n ≤ n + m` through a number level,
   no gaps, fully zoomed out; `bound_offers_discharged_and_gapped` (the two readings on the same number
   line, one carrying a premise and one not); `bound_reads_the_boolean_line_three_ways` (the
   unconditional reading on the whole boolean line, and the conditional one on its number *operand*,
   rewriting the line in place — the short way round of the two zoom-ins); and
   `gapped_leaves_the_premise_as_a_gap`, `gapped_proves_nothing`, `gapped_writes_the_law_s_line` for
   the undischarged case. `netty --selftest` gained `conditionalTest`, which reads all of that off the
   request service the client talks to, and a staleness check for the new law file beside the old one.
   Not done here: the boolean conditional reading, a better check for number laws, ML ranking,
   distributivity, arithmetic or normalisation.

19. [x] **The conditional reading at the boolean level**, 2026-09-24 on main. Item 18 read a law
   conditionally only where its consequent was a *number* relation, and said why: a boolean conditional
   law's own `⇒` already stands in a boolean margin, so a second reading might bury the readings that
   need nothing. That limit is lifted — `Law.conditional` now takes any margin connective — and the two
   things that kept it honest are written down in the law's own comment, because they are what replaces
   it: the conditional readings come **last** in `Law.variants`, so when a law can write one and the
   same line both with a premise and without, the dedup in `Doc.suggestions` keeps the one that needs
   nothing; and `Doc.rank` puts every step that needs nothing before every step that leaves a gap. No
   new machinery: the premise, the settling and the gap are item 18's.
   Measured, on `x ∧ y ∧ y ∧ z`: the suggestion list goes from 227 rows to 247, and the **applicable**
   list is unchanged at 207. Every one of the 20 new rows is greyed, and that is not an accident of the
   line — a monotonicity or transitivity law relates the line to a third formula the line does not
   determine (`(a ⇒ b) ⇒ (a ∧ c ⇒ b ∧ c)` read from `a ∧ c` must be told what `b` is), so matching
   always leaves a variable free and the kernel will not apply it. Those rows say what the law would do
   and what it would need; taking them needs the document's small dialog box, which this kernel has
   not got. That is now the named next thing rather than a silent limit.
   What the lift *does* buy at the boolean level is the context. A context law is ground — a zoom in
   supplies a fact, not a schema — so when the fact is itself an implication whose consequent is a
   relation, its conditional reading has nothing left unconstrained and is a step that can be taken,
   licensed by another fact in force. `Netty.Replay.ponens` is that: `a ⇒ ((a ⇒ (b ⇒ c)) ⇒ (b ⇒ c))`,
   two zoom-ins putting `a ⇒ (b ⇒ c)` and `a` in force, and then the context rewriting the operand `b`
   of `b ⇒ c` to `c` with `a` as the premise it needs — modus ponens as the document would have a user
   do it. Drop the outer `a ⇒ …` and the goal stops being a theorem: the same reading is then offered
   *with* its premise, and taking it leaves the warning sign and claims nothing.
   The selftest's soundness check was the one thing that had to change, and it changed for the better.
   `matchTest` built `line op result` and required a tautology; a conditional reading is a sound step
   *given its premise*, so it now requires `premise ⇒ (line op result)`. That is the justification the
   feature wanted all along, and it holds for every row: **5353 suggested steps are sound**, the
   conditional ones checked as conditionals. `Netty.Replay.key`, the ranking key the witness sorts by,
   had been left without the premise key when item 18 added it to `Doc.rank` — it passed then because
   no boolean line had a conditional row, and it does not pass now; it is fixed, and
   `suggestions_are_ranked` checks the whole order again.
   Witnessed in Lean, all by `decide`, all `propext` only: `conditional_variants_come_last` (the dedup
   guard, over both shipped law lists), `shipped_boolean_conditional_readings_are_all_greyed` (there are
   some, and every one is greyed), `ponens_proves` and `ponens_complete`,
   `ponens_offers_discharged_boolean_steps` (the three readings of the context that can be taken there,
   none carrying a premise), and `ponensGappy_offers_them_with_the_premise`,
   `ponensGappy_leaves_the_premise_as_a_gap`, `ponensGappy_proves_nothing` for the undischarged case.
   `netty --selftest`'s `conditionalTest` now drives the boolean half through the request service as
   well as the number half. `netty-web/` needed nothing: the premise travels in the fields item 18
   added, and a boolean premise reads as a boolean formula.
   The cost is worth writing down: `lake build netty` goes from about 4m20 to about 6m, because every
   `decide` that computes a suggestion list now computes twenty-odd more rows, and one replay needed
   `maxHeartbeats` raised. If that grows again, the witnesses to shrink are the ones that replay a whole
   proof under the full law list.
   Not done here: supplying a law variable by hand, a better check for number laws, ML ranking,
   distributivity, arithmetic or normalisation.

20. [x] **The small dialog box: supplying a law variable by hand**, 2026-09-24 on main. Item 19 measured
   that every conditional reading of the shipped *boolean* laws is greyed, because a monotonicity or
   transitivity law relates the line to a third formula the line does not determine:
   `(a ⇒ b) ⇒ (a ∧ c ⇒ b ∧ c)` read from `a ∧ c` must be told what `b` is. The document's answer is a
   small dialog box, and this round is it — as a command, as a script clause, and as a form in the
   window.
   `Cmd.apply` and `Cmd.applyNamed` carry a `Subst`, and `Doc.applySuggestion` takes one and
   instantiates the reading with it before taking the step. There is no new kind of suggestion and no
   new argument for soundness: matching pinned some of the law's variables, the law holds for *every*
   instantiation of the rest, so any expression may stand in their place. What the bindings change is
   which line the step writes and which premise it needs — and **the premise is asked again after
   them**, because supplying a variable can turn a premise the laws in force could not settle into one
   they can. That is what makes the worked example work.
   The kernel still never guesses. A hole left unbound is refused as it always was; a binding for a
   variable the suggestion has not got is refused rather than ignored, because that is a typo and not a
   step; and `apply NAME : …` with bindings matches on the line the suggestion writes *after* they are
   supplied, which is the line a user would name.
   The script clause is `apply #N with x := E, y := F`, and `apply NAME : CONN E with …` too. `with` is
   a word of the `apply` command, so a proof about a variable actually named `with` cannot use the
   clause; the clause is taken off before the `:` of `apply NAME : …` is looked for, so a binding's
   `:=` is never mistaken for that colon. The bindings are separated by `,`, which no expression
   contains. It is one line, so the window sends it as `{"op":"cmd","arg":"…"}` and no request changed.
   In `netty-web/`, clicking a greyed row opens `holeDialog`: one field per free variable, `apply` and
   `cancel`, Escape to close, and the same dialog on the number-key shortcut. The row **stays greyed**
   until the fields are filled, because the step is not takeable until then; the form is a sibling of
   the row rather than a child, a form inside a button being no form at all. One CSS block, no new
   request, no change to the three panes.
   The worked example is monotonicity proving itself, which is the honest one to reach for: inside
   `(x ⇒ y) ⇒ (x ∧ z ⇒ y ∧ z)`, zooming in puts `x ⇒ y` in the context; the monotonicity reading of the
   operand `x ∧ z` is offered and greyed, waiting for `b`; supplying `b := y` writes
   `y ∧ z ⇒ y ∧ z`, and the premise it then needs is `x ⇒ y`, which the context settles — so the step
   leaves no gap and the proof goes through. On a bare line, where nothing settles it, the same law and
   the same binding still leave the warning sign with the premise recorded beside it, and the proof
   still claims nothing.
   Witnessed in Lean, all by `decide`, all `propext` only: `dialog_rows_are_greyed_until_bound` (both
   readings at that operand, each naming the variable it waits for and the premise it would then need,
   with `b` still in it), `dialog_proves` and `dialog_complete`, `dialog_needs_the_binding` (the same
   command without the binding finds nothing), `dialog_refuses_a_stray_binding`, and
   `dialogGappy_leaves_the_premise_as_a_gap` / `dialogGappy_proves_nothing` for the undischarged case.
   `netty --selftest` gained `dialogTest`, which drives all five of those through the request service
   the window talks to, and the `/api` path was smoke tested against the running server.
   Not done here: a better check for number laws, ML ranking, distributivity, arithmetic or
   normalisation, and the named grammar chunks.

## Then grow language ↔ Netty grammar

Use Netty’s LR/LL grammar as the roadmap for surface syntax and Prog constructs (var/ivar/chan/frame, `||`, `!`/`?`, quantifiers, functions, …), tying each chunk to existing LaPToP theory modules where they already exist (`Concurrency`, `Interaction`, …) and to `interp` where execution suggestions apply.

## Non-goals

- First UI inside Lean Infoview
- Rewriting an old Netty desktop binary as the starting point
- Claiming full aPToP surface before the kernel can host boolean/number calculations

## Kick when ready

When status-line is READY after 2d (or Michal asks earlier): write `.sci/task.md` for “Netty kernel MVP” (or a new repo if Michal prefers a separate project), kick Claude / start implementation, and keep laptop interpreter maintenance on the no-idle queue only if NEXT still has interpreter residuals.
