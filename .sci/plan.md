# Plan (chapter order follows the Blueprint, content follows the book)

## Basic Theories chapter (`LaPToP/Chapters/BasicTheories.lean`)
- [x] §2.0 Bunch Theory axioms + null laws + derived laws — `LaPToP/BasicTheories/Bunch.lean` (2026-09-14)
- [x] §2.1 Set Theory axioms (`HSet`, `pack`, `contents`, `power`, `card`) — same module
- [x] §2.0 useful bunches and the interval `x,..y`: `nat`, `int`, `bin`, `xnat`/`xint`,
      `Bunch.interval`, `¢(x,..y) = y–x`, nat construction/induction axioms — `LaPToP/BasicTheories/Numbers.lean` (2026-09-14)
- [x] §2.0 operators distributing over bunch union (`–A`, `A+B` via pointwise `Set.neg`/`Set.add`) — same module
- [x] §1.1 Number Theory laws (§11.3.2 "Numbers") on `EReal`, deviations recorded; `nat_add_zero` linked — `LaPToP/BasicTheories/NumberLaws.lean` (2026-09-14)
- [ ] `calculation_style`: one worked calculation-style proof (Lean `calc`) attached to the node

## Data Structures chapter
- [x] §2.2 String Theory (`nil`, join, `↔` length, indexing, `n*S`, `S⊲n⊳i`, order, `x;..y`) on `List` — `LaPToP/DataStructures/Strings.lean` (2026-09-14)
- [x] §2.3 List Theory (`HList` packaging strings; `~L`, `#L`, `☐L`, `;;`, composition, `n→i | L`, order, inclusion; derived laws; examples) — `LaPToP/DataStructures/Lists.lean` (2026-09-14)
- [x] §2.3.0 Multidimensional structures — `LaPToP/DataStructures/Multidimensional.lean`, node `multidimensional_structures` (2026-09-17)
- [ ] §2.2/2.3 "strings of bunches = bunches of strings": join/brackets distributing over bunch union — needs `Str (Bunch α)` vs `Bunch (Str α)` bridge; defer

## Prelude / Binary Theory (§1.0; laws in §11.3.1 "Binary")
- [x] Binary laws §11.3.1 on `Bool` (all 101 laws under the book's headings) — `LaPToP/BasicTheories/Binary.lean` (2026-09-14)

## Function Theory (§3) — prerequisite for Program Theory
- [x] §3.0 Functions with explicit domain (`Fn α β`), Domain/Application/Extension/Renaming, selective union,
      predicates/relations; §3.1 ∀ ∃ § axioms, Specialization/Generalization, One-Point — `LaPToP/FunctionTheory/Functions.lean`,
      new chapter `Chapters/FunctionTheory.lean` (2026-09-14)
- [x] §3.1 ⇑ ⇓ (sSup/sInf), Σ Π (finite domains), numeric axioms + laws; §11.3.8 ∀ ∃ § law table
      (Identity … Domain Change, Change of Variable) — `LaPToP/FunctionTheory/Quantifiers.lean` (2026-09-14)
- [ ] §11.3.8 distributive laws of `+ – × ↑ ↓` over ⇑ ⇓ (need `D ≠ null` and finiteness; `sSup` of shifted sets) — deferred
- [x] §3.2 Function Fine Points (functions on bunches, partial/total/deterministic, Function Inclusion Law, `A→B`,
      Arrow laws (one corrected), `suc: nat→nat` …) + §3.3 List as Function — `LaPToP/FunctionTheory/FinePoints.lean` (2026-09-14)
- [x] §3.4 Limits and Reals — `LaPToP/FunctionTheory/Limits.lean` (2026-09-17)

## Program Theory (§4) — the book's core
- [x] §4.0 Specifications (`Spec σ := σ → σ → Prop`), satisfiable/deterministic/implementable, `ok`, `x:= e`, `if`,
      `P. Q`, refinement; §4.0.1 Specification Laws incl. Substitution; §4.0.2 refinement laws + the book's examples;
      Prelude `state_as_variables` formalized — `LaPToP/ProgramTheory/Specifications.lean` (2026-09-14)
- [x] §4.0.3 Programs (`Spec.IsProgram`, every program implementable) + §4.1.0 Refinement by Steps / Parts / Cases
      + §4.1.1 List Summation (four refinements, compiler's view) — `LaPToP/ProgramTheory/Programs.lean` (2026-09-14)
- [x] §4.2 Time: `TSt` with `t : ℕ∞`, `ImplementableT`, `tick`, recursive/real-time example, §4.2.2 Termination (a)–(d)
      — `LaPToP/ProgramTheory/Time.lean` (2026-09-14)
- [x] §5.2.0 While-Loop as the refinement notation `WhileRefines`, timed list summation, Exercise 320 — `LaPToP/ProgramTheory/WhileLoop.lean`,
      new chapter `Chapters/ProgrammingLanguage.lean` (2026-09-14; on main)
- [x] §5.2.3 For-Loop (`ForRefines` + unrolling + invariant rule), Exercise 179, loop timing, Exercise 326 — `LaPToP/ProgramTheory/ForLoop.lean` (2026-09-14; on main)
- [x] §5.0.0 Variable Declaration (`newVar`, `newVarInit`, lifting, examples) + §5.0.1 Variable Suspension (`frame` + laws,
      `ok = frame· ⊤`, `x:= e = frame x· x′=e`, `s:= ΣL = frame s· new n· s′=ΣL`) — `LaPToP/ProgramTheory/Scope.lean` (2026-09-15; on main)
- [x] §5.4 Assertions (`assert` with the screen!/wait-until-∞ caveat) + §5.4.0 Backtracking (`ensure`, `or`, the example)
      — `LaPToP/ProgramTheory/Assertions.lean` (2026-09-15; on main)
- [x] §5.2.1 Exit-Loop, §5.5 Subprograms, §5.2.2 Two-Dimensional Search — done 2026-09-16 (see the entries below), §5.3 Time and Space Dependence — done 2026-09-16

## Recursive Definition (§6)
- [x] §6.0.0 predicate forms of nat induction/construction, bunch⟺predicate derivations, six equivalent versions;
      §6.0.1 `IsFixedPoint`/`IsLeastFixedPoint`, `nat = 0, nat+1`, fixed-point induction — `LaPToP/RecursiveDefinition/Nat.lean` (2026-09-15; on main)
- [x] §6.1 zap: six solutions as fixed points, refinement order + incomparabilities, implementability/determinism, weakest fixed point
      via fixed-point induction; §6.1.0 zapₙ construction; §6.1.1 WhileAxioms, fixed-point theorems, consistency/uniqueness, §5.2 contrast
      — `LaPToP/RecursiveDefinition/Programs.lean` (2026-09-15; on main)
- [x] §6.0.2 Recursive Data Construction: general monotone-constructor procedure, `pow = 2^nat`, the `bad` inconsistency
      — `LaPToP/RecursiveDefinition/DataConstruction.lean` (2026-09-15; on main). Chapter 6 of this edition ends at §6.1.1.

## Theory Design and Implementation (§7)
- [x] §7.0.0 `DataStackTheory` structure (+ weak axioms one-element model), §7.0.1 list implementation, incompleteness via two models
      — `LaPToP/TheoryDesign/Stack.lean`, new chapter `Chapters/TheoryDesign.lean` (2026-09-15; on main)
- [x] §7.0.2 SimpleStackTheory (+ stream model with no empty stack), §7.0.3 DataQueueTheory + list model (Ex. 426),
      §7.0.4–7.0.5 DataTreeTheory/SimpleTreeTheory + `BinTree` model — `LaPToP/TheoryDesign/{SimpleStack,Queue,Tree}.lean` (2026-09-15; on main)
- [x] §7.1.0–7.1.3 ProgramStackTheory (+ balanced pushes/pops, top after balanced blocks), list implementation (Ex. 429),
      Fancy (mkempty/isempty), Weak (balance) + strong⇒weak — `LaPToP/TheoryDesign/ProgramStack.lean` (2026-09-15; on main)
- [x] §7.2 Data Transformation (`IsTransformer`, `transform`, monotonicity, bijective-case implementability, the totality caveat
      by counterexample) + Exercises 454(a), 455(a) — `LaPToP/TheoryDesign/DataTransformation.lean` (2026-09-15; on main)
- [ ] §7.1.4 Program-Queue, §7.1.5 Program-Tree, §7.2.0–7.2.3 further data-transformation examples — later

## Concurrency (§8)
- [x] §8.0 `par`/`parWith`/`parT`, the six examples, §8.0.0 laws (substitution, symmetry/associativity up to reshuffling, distributivity ×3,
      Steps/Parts) — `LaPToP/Concurrency/Composition.lean`; `concurrent_composition` node formalized (2026-09-15; on main)
- [x] §8.0.1 List Concurrency (Exercise 172): `LaPToP/Concurrency/ListConcurrency.lean` — `LS` (t, L : ℕ → ℤ), `parSeg` (segment-partitioned ||,
      t′ = max), `segSup : WithBot ℤ` (⇑ of a segment, −∞ on empty) with singleton/split/congr, `clog_two_split`, `findmax_refines` proving
      `findmax i j ⇐ if j–i = 1 then ok else t:= t+1. (findmax i m || findmax m j). L i:= L i ↑ L m` with exact time `ceil(log(j–i))`
      (`Nat.clog 2`); nodes `list_concurrency`, `findmax` (2026-09-16; on main). Deviations: L total ℕ → ℤ, recursive calls are specs.
- [x] §8.1 Sequential to Concurrent Transformation + §8.1.0 Buffer — `LaPToP/Concurrency/Transformation.lean`: `liftL/liftR/liftLWith/liftRWith`,
      laws `seq (liftL P) (liftR Q) = par P Q`, `seq (liftRWith Q) (liftL P) = parWith (fun _ => P) Q` (copy = parWith initial-value parameter),
      absorption laws, the x/y/z example (three forms equal, result `x′=y+1 ∧ z′=y`), Buffer produce/consume/copy, `consume. produce = consume || produce`,
      source-level `c:= b` form agrees on b, x; control/newcontrol as fixed-point equations + unrolling; nodes `sequential_to_concurrent`, `buffer`
      (2026-09-16; on main). Left informal: time remark, w/r and cyclic buffers (Chapter 9).
- [x] §8.1.1 Insertion Sort (Exercise 209) — `LaPToP/Concurrency/InsertionSort.lean`: `sorted`, `IsPermBelow` (perm fixing indices ≥ n),
      `swap i j = L ∘ (i ↔ j)` with item-level `||` reading, `sortStep_refines` (the book's recursive refinement), `sortLoop_forRefines`
      (for-loop via `ForRefines`), `sortLoop_zero`, commuting swaps `S_comm`/`S_preserves_C`; node `insertion_sort` (2026-09-16; on main).
      Deviation: the informal permutation conjunct is carried in the spec (needed for provability); time ignored as in the book.
- [x] §7.2.0 Security Switch (Exercise 460) — `LaPToP/TheoryDesign/SecuritySwitch.lean` + `Spec.transformU`/`IsTransformerU` (transformer
      may mention the user's variables; `transform` is the special case) in `DataTransformation.lean`; `transformU_switchStep` proves the
      book's chain `= c:= (a⧧c ∧ b⧧c) ⧧ c` as one equation, `transformU_opA/opB`, majority + circuit remarks by `decide`; node
      `security_switch`, `data_transformation` node extended (2026-09-16; on main).
- [x] §7.2.1 Take a Number (Exercise 462) — `LaPToP/TheoryDesign/TakeANumber.lean`: `Dbelow f` (s ⊆ {0,..f new}), transformed start/take/give
      as equalities (omitted steps filled in), refinements `⇐ ok`, `⇐ n:= m. m:= m+1`, `⇐ ok`; two machines `take_refines₂`; even/odd
      `take_refinesEO` under `Even i`, `Odd j`; node `take_a_number` (2026-09-16; on main). **Finding**: the book's transformed `give` lacks the
      guard `n<m` — for `m ≤ n` the transformed spec is ⊤; book's line is a refinement, not an equality (`transform_give_ne_book`).
- [x] §7.1.4 Program-Queue Theory + §7.1.5 Program-Tree axioms — `LaPToP/TheoryDesign/ProgramQueue.lean`: `ProgramQueueTheory` (five axioms,
      `b ⇒ (P = Q)` stated pointwise), derived `¬isemptyq′ ⇐ join x`, FIFO `join x. join y. leave = join x. leave. join y`, list implementation
      `PQ X` proved; `ProgramTreeTheory` (first definition, axioms only, derived `go. node:= x. go`); nodes `program_queue_theory`,
      `program_tree_theory` (2026-09-16; on main). Not done: tree implementation / T,p definition.
- [x] §5.5 Subprograms — `LaPToP/ProgramTheory/Subprograms.lean`: `Spec.value` (ε over final states) + `ValueDetermined` (the hypothesis the
      book's axiom assumes), `value_axiom`, `value_assign`, implementation `value_impl` via local copy, examples + `side_effect_ne`; `bexp_eq :
      bexp n = 2^n` (assembled from parts, `iterSeq_implementable`); procedures: `P (a+1)`, refinement, translation law `procedure_eq_newVarInit`,
      variable parameters `body₁ a ≠ body₂ a`; nodes `value_expression`, `function_and_procedure` (2026-09-16; on main).
- [x] §5.2.1 Exit-Loop — `LaPToP/ProgramTheory/ExitLoop.lean`: `ExitLoopRefines` (= the book's alternative notation), while relation, mono,
      unroll, `DeepExitRefines`/`DeepShallowRefines` (exit n by naming the inner loop), flag translation `ExitLoopRefines.flag` +
      `newVarInit_flagLoop`, example `count_up`; node `exit_loop` (2026-09-16; on main).
- [x] §5.2.2 Two-Dimensional Search (Exercise 191) — `LaPToP/ProgramTheory/TwoDimSearch.lean`: `memRows`/`memFrom`, `P/Q/R`, the five
      refinements, compiler's view `compiled₀–₂`; timing: **book's bounds off by one** (`book_timed_R_fails`, n=1 m=0) — corrected bounds
      `n×(m+1)`, `(n−i)×(m+1) − j` (before) / `− j − 1` (after the tick) proved `timed₁–₅`; node `two_dimensional_search` (2026-09-16; on main).
- [x] §5.3 Time and Space Dependence — `LaPToP/ProgramTheory/TimeDependence.lean`: `RespectsClock` (deadline:= t+5, tick, cond, seq, wait
      until respect it; `t:= 5` does not), `waitUntil w = t:= t↑w`, busy-wait refinement by the book's two cases + as a while-loop; node
      `time_dependence` (2026-09-16; on main). Prose-only: Exercise 333(b), the space variable.
- [x] §7.2.3 Limited Queue (Exercise 464), part 1 — `LaPToP/TheoryDesign/LimitedQueue.lean`: `Inside`/`Outside`, `D₀`, `D` (mode bit),
      transformer property under the typing, `not_implementable_isemptyq₀` ("f=b is missing!"), `mkemptyq/isemptyq/isfullq_refines`,
      `implementable_isemptyqT`; node `limited_queue` (2026-09-16; on main).
- [x] §7.2.3 part 2 — `join/leave/front` with `joinT/leaveT/frontT`, refinements under the "not full"/"not empty" checks (`guardT`), wrap-around
      via `outside_index_lt`; `limited_queue` node completed (2026-09-16; on main).
- [x] §7.2.2 Parsing (Exercise 451) — `LaPToP/TheoryDesign/Parsing.lean`: `Tok`, inductive `E`, `Cands` (c with x ↦ E, eog ↦ eos), LL(1)
      lemmas, sentinels `SentC`/`SentS`, `R_refines` (book's final program refines `R`), `parse_refines`/`parse_program_refines`
      (`q′ = (s : E) ⇐ c:= [x];[eog]. n:= 0. R`); node `parsing` (2026-09-16; on main). Not formalized: informal A→b→c transformers.
      Reading note: printed `…;[“fi”]c` taken as `…;[“fi”];c1;..↔c`.
- [x] §9.0 Interactive Variables — `LaPToP/Interaction/InteractiveVariables.lean` (new chapter `Interaction`, registered): `ISpec := IVar → IVar →
      Spec BT`, `newX`, `ok`, `assignA`, `assignX` (duration), process-local `assignXP/assignYQ`, `seq`, `par`, surviving laws,
      `not_substitution_law`, `exercise_496` proved as stated (finite initial time); nodes `interactive_variables`, `exercise_496`
      (2026-09-16; on main).
- [x] §9.1 + §9.1.0 + §9.1.1 — `LaPToP/Interaction/Communication.lean`: `Scripts`, `CS`, `CSpec`, `c! e`/`c?`/`c`/`√c` with Substitution Laws,
      `Increasing` (every-computation law), `ImplementableC` literal + output/input implementable, two-channel examples `evenSpec_refines`,
      `doubling_refines`; nodes `communication`, `communication_implementability`, `input_output_examples` (2026-09-16; on main).
      Thermostat (§9.0.0) deferred.
- [x] §9.1.2 + §9.1.3 — `LaPToP/Interaction/CommunicationTiming.lean`: `inputT`/`checkT`, Exercise 516(a) `inputT_refines`; `dblBody`,
      `dblW` fixed point, `fixedPoint_refines_dblW`, `bot_fixedPoint`, `dblSeq_eq`, `dblW_iff_forall`; nodes `communication_timing`,
      `recursive_communication` (2026-09-16; on main). Not stated: strongest implementable solution (needs xnat cursors).
- [x] §9.1.4 Merge + §9.1.5 Monitor — `LaPToP/Interaction/Merge.lean`: `mergeBody_step` (all and only the messages read), `timemergeBody` with
      waits/tick, `implBody`, guarded step refinements `step_refines_c/d`, **`not_step_refines`** (book's implementation asserted without
      proof; step-wise refinement fails with two inputs; fixed-point refinement not formalized); monitor definitions + 4 guarded step lemmas;
      nodes `merge`, `monitor` (2026-09-16; on main).
- [x] §9.1.6 + §9.1.7 — `LaPToP/Interaction/ChannelDeclaration.lean`: `not_last_written` (+ par form), `newChannel` (one-point applied),
      `newChannel_liftChan`, buffer example `x′=7 ∧ t′=t+1`, general theorem `newChannel_outParIn = x:= e` (+ transit `t′=t+1`);
      synchronizer definitions, `inputReq_outputRep_comm`, `synchronizerBody_step`; nodes `channel_declaration`, `reaction_controller`
      (2026-09-16; on main). Model: `c! e || (c?. x:= c)` as the book's expansion.
- [x] §9.1.8 + §9.1.9 — `LaPToP/Interaction/Deadlock.lean`: xnat lemmas, `newChannel_readThenWrite` (528(a)), `newChannel2` + `mutualWait`
      (528(b)) both `= x′=x ∧ t′=∞`; broadcast `BS k` with per-reader cursors, `parReaders` (max of finals), `parReaders_input`; nodes
      `deadlock`, `broadcast` (2026-09-16; on main). Maintainer's site-UX enhancer (scripts/enhance-site-ux.py) verified on a copy.
- [x] §9.1.10 Power Series Multiplication — `LaPToP/Interaction/PowerSeries.lean`: `conv` + `conv_zero/one/succ_succ` (the algebraic heart),
      `P`/`Loop` predicates, `loop_step`/`main_step` (the book's post-substitution lines), program-level `loop_refines`; node
      `power_series_multiplication` (2026-09-16; on main). Not modelled: the substitution step with `new d?!`/`P d ||` process generation.
      **Chapter 9 complete (§9.0–9.1.10).**
- [x] Gaps pass 1 — `LaPToP/Interaction/MergeInterleave.lean` (`Interleave` invariant `Inv` preserved by merge/timemerge/impl steps,
      `stepsInv_impl`, `implBody_c/d_arrived`; literal first-available fixed-point refinement still unproved, recorded) and
      `LaPToP/Interaction/Thermostat.lean` (§9.0.0 definitional + step-time bounds); node `thermostat`, `merge` node extended (2026-09-16; on main).
- [x] Gaps pass 2 — `LaPToP/ProgramTheory/Space.lean`: Towers of Hanoi `movePile_n`, `time_refines` (2^n−1), `space_refines` (s′=s),
      `longLine_refines`, `maxSpace_refines` (s ≤ m ≤ s+n ⇒ (m:= s+n)), `MS_m_le`; node `space` (2026-09-16; on main).
- [x] Gaps pass 3a — `Space.lean` extended: `Avg.avg_refines` (integer model, recorded), `Avg.average_space` identity, combined
      `Full.MovePile` + `Full.movePile_refines`; `space` node extended (2026-09-16; on main). **§4.3 complete.**
- [x] Gaps pass 3b — `LaPToP/ProgramTheory/Arrays.lean`: `assignElem_eq_assignA` (A i:= e = A:= i→e | A), `orElse_arrow_apply`, the two
      Substitution-Law failures made precise (`example₁/₁_naive`, `example₂/₂_naive`), 2-D arrays, records; node `data_structures`
      (2026-09-16; on main). **§5 Programming Language complete (§5.0–5.5; §5.6 Alias optional).**
- [x] Gaps pass 3c — `LaPToP/Interaction/GrowSlow.lean`: `discharge_iff` (the missing initialization `x ≥ 2^s`), `growSlow₀_not_refines`
      (counterexample), `growSlow_refines` by the two cases; node `interactive_space` (2026-09-16; on main). **Chapter 9 complete incl. §9.0.0–9.0.1.**
- [x] Gaps pass 4 — group intros list every module in book order; Blueprint intro maps chapters to book sections + honesty policy; README
      layout/policy updated; full-site KaTeX strict 0/2416 (2026-09-16; on main). Prose only.
- [ ] Book sections not yet formalized (survey 2026-09-16): §4.2.0 Real Time (remark), §4.2.3 Soundness & Completeness (opt.), **§4.2.4 Linear
      Search, §4.2.5 Binary Search, §4.2.6 Fast Exponentiation, §4.2.7 Fibonacci Numbers**, §4.4 Old Program Theory (opt.), §5.2.4 Go To,
      §5.6 Alias (opt.), §5.7 Probabilistic Programming (+5.7.0 random number generators, 5.7.1 information, opt.), §7.2.4 Soundness & Completeness (opt.), §8.1.2 Dining Philosophers.
- [x] §4.2.4 Linear Search + §4.2.5 Binary Search — `LaPToP/ProgramTheory/Search.lean`: linear `refine₁–₃`, `time₁–₃`, `combined₁–₂`,
      nonempty variant, sentinel (`sentinel_loop/top`); binary `R` read via continuing operators (`p′ = x ∈ L(h,..j)`, then `L h′ = x`),
      `refine₁–₄` with `occurs_right/left` from sortedness, `time₁–₃` with `Nat.clog 2` via `clog_two_split`; nodes `linear_search`,
      `binary_search` (2026-09-16; on main).
- [x] §4.2.6 Fast Exponentiation — `LaPToP/ProgramTheory/FastExp.lean`: simple + six fast refinements, `T` timing ×6 with `Nat.log 2`;
      §4.2.7 Fibonacci (linear) — `LaPToP/ProgramTheory/Fibonacci.lean`: `P_refines`, `shift_refines`, linear timing; nodes
      `fast_exponentiation`, `fibonacci` (2026-09-16; on main).
- [x] §4.2.7 logarithmic Fibonacci (`P_log`, `odd/even_refines`, `sq₁/sq₂`, `TLog` timing) + Exercise 255 Collatz time function
      (`LaPToP/ProgramTheory/CollatzTime.lean`: `goal_refines`, `IsCollatzTime`, `time_refines`; node `collatz_time` in the Collatz chapter;
      `collatz_conjecture` stays intentionally open) (2026-09-16; on main). **§4.2 complete (except optional §4.2.3).**
- [x] §5.2.4 Go To — `LaPToP/ProgramTheory/GoTo.lean` (labels A–E as specs, four refinements; node `go_to`); §8.1.2 Dining Philosophers —
      `LaPToP/Concurrency/DiningPhilosophers.lean` (variable sets ↔ book's side conditions via `decide`, ten commutation equalities,
      `up_down_not_comm`, one-at-a-time `life`, totality = no deadlock; node `dining_philosophers`) (2026-09-17; on main). **§8 complete.**
- [x] §5.8 Functional Programming + §5.8.0 Function Refinement — `LaPToP/ProgramTheory/Functional.lean`: `sumFn` with `domain_split`,
      `orElse_lam_lam` (selective union ↔ `if`), `sumFn_orElse`/`left_part`/`right_part`/`recursion`, `timeFn` both measures; `FSpec`
      with `Unsat/Sat/Det/Nondet`, `Implementable ↔ ≠ null`, `Refines P S := Incl S P`; `search₀` unimplementable (empty list),
      `search` implementable, `search_apply_eq`, `search_step_refines`, `time_top`/`time_step` (domain `0,..#L+1`, recorded); node
      `functional_programming` (2026-09-17; on main). 155 nodes.
- [x] §5.7 Probabilistic Programming (pp. 85–87) — `LaPToP/ProgramTheory/Probabilistic.lean`: `PSpec σ := σ → σ → ℝ`, `ind` (⊤=1, ⊥=0)
      with ¬/∧/∨ laws, `ofSpec`, `IsDistribution` (HasSum 1), `pcond`/`pseq`/`avg`; one-point distributions, `tsum_succ_eq_one`,
      `not_summable_succ` ("= ∞"), geometric 2⁻ⁿ; `isDistribution_pcond`, `isDistribution_pseq` (finite support only — recorded);
      `ofSpec_ok/assign/cond`, `passign_pseq` (Substitution Law), `ofSpec_assign_seq`; examples `ex₁` (1/3, 2/3, 0), `ex₂_eq`,
      `isDistribution_ex₂`, `avg_ex₂_x = 4 + 2/3`, `prob_ex₂_gt_three = 2/3`; node `probabilistic_programming` (2026-09-17; on main).
      Not proved: general pseq closure; Σ n²/2ⁿ = 6. 156 nodes.
- [x] §5.7.0 Random Number Generators — `LaPToP/ProgramTheory/RandomNumbers.lean`: `urand`/`randAssign`/`randAssign_id`, both computations
      of `x:= rand 2. x:= x + rand 3` (`freshForm_eq`, `twoRand_eq`), `pcond_rand_two`, `randLt_eq/eq'` (5/8 – b/4); dice Exercise 351 in
      two layers (`prob_dice_eq/ne`; `diceBody`, `tdist`, `diceBody_tdist` fixed point, `isDistribution_tdist`, `avg_tdist = t+5`);
      generic `pdet`/`pdet_pseq`; node `random_number_generators` (2026-09-17; on main). Not formalized: blackjack Exercise 344;
      recorded: the book drops u′, v′ from the final state. 157 nodes.
- [x] §5.7.1 Information — `LaPToP/ProgramTheory/Information.lean`: `info`, `entro`, rand-8 test probabilities, exact values, bounds
      `0.19 < info (7/8) < 0.2`, `0.54 < entro (1/8) < 0.55`, `entro = binEntropy / log 2`, `entro_le_one`, `entro_eq_one_iff`; node
      `information`. §5.6 Alias — `LaPToP/ProgramTheory/Alias.lean`: `Memory` (addr, store), `read/assign/retarget/Aliased`,
      `read_assign_alias`, `aliased_retarget`, `no_alias_iff_injective`, two-name one-cell counterexamples `assign_law_fails`,
      `substitution_law_fails`, alias-free `toMemory` = `State Name Val` with `assign_iff`/`assign_seq`; node `alias`
      (2026-09-17; on main). **§5 complete.** 159 nodes.
- [x] §4.4 Old Program Theory — `LaPToP/ProgramTheory/OldTheory.lean`: `prePost` + three non-decomposable specs, `exactPre`/`exactPost`
      (+ refinement iff, weakening refinements), Sufficient/Necessary pre/post, the one-variable computations and six examples,
      Exercise 301(c) (`abs_sq_gt_iff`, `exactPre_farther`, `exactPost_farther`), `IsInvariant` (+ two equivalent forms, Exercise
      304(f)), `IsVariant`, `backward_clock`, `timeBound_refines`; node `old_program_theory` (2026-09-17; on main). **§4 complete
      except §4.2.3 (meta-claims, prose).** 160 nodes.
- [x] §7.2.4 Soundness and Completeness — `LaPToP/TheoryDesign/Incompleteness.lean`: `init`/`step` on `Fin 3 × Fin 3`, `init_refines`,
      transformer `Dz` (j=0, new type Unit) with `transform_initZero` (= i:= 0) and `transform_step` (= ok), and `no_transformer` (no
      D in i, j, b gives i′=0 and if b ∧ i<2 then i′=i+1 else ok); node `data_transformation_incompleteness`. §4.2.3 recorded as a prose
      paragraph in the Program Theory group intro (meta-statements, not formalized) (2026-09-17; on main). **§7 complete.** 161 nodes.
- [x] Blackjack Exercise 344 — `LaPToP/ProgramTheory/Blackjack.lean`: `deal`/`secondCard` (= randAssign, distributions via
      `hasSum_uniform`), `game7` distribution with `game7_eq_sum` and the closed form `game7_eq` (case analysis on x′), two-player
      reductions `xWins_iff`/`yWins_iff`/`tie_iff`, counts `probXWins_eq` (n–1)/169, `probYWins_eq` (14–n)/169, `probTie_eq` 12/13,
      `probs_sum`, `under_succ_beats`, `under_beats_succ`, `under_eight_best`; node `blackjack` (2026-09-17; on main). 162 nodes.
      Recorded: four-variable PSpec program not built (count is what the book proves).
- [x] Probabilistic loose ends — `LaPToP/ProgramTheory/ProbabilisticSums.lean`: `isDistribution_pseq'` (general P.Q closure via
      `summable_prod_of_nonneg` + `Summable.tsum_comm`), `geomDist` distribution, `hasSum_sq_geometric`, `avg_geomDist_sq = 6`; the
      `probabilistic_programming` node and Probabilistic.lean docstring no longer list unproved claims (2026-09-17; on main).
      **All book sections §1–§9 covered; no "not proved" claims remain except the intentional collatz_conjecture.** 162 nodes.
- [x] §11.3 law-table survey — `.sci/laws-survey.md` (committed; README points at it): per-table mapping law → Lean theorem or
      MISSING, with counts. Missing after this round: Numbers Counting (notation, 10), Bunches 8 (¢nat = ∞, (A,B)–,C form,
      nat = 0,..∞, division by 0, exponents), Sets 2, Strings 7 (bunch strings, ** , S{A}, (S⊲n⊳i)m), Lists 9 (@ indexing, L{A},
      L[S], #L = ¢☐L, (S;T)→i|L), Functions 7 (f|f, |-assoc, (g|h) f, function bunches, if-distribution, ‘-arrow), Quantifiers 14
      (⇑⇓ Distributive with ↑↓+–×, n×Σ, Πⁿ, real Extreme), Limits 3 (§3.4 not formalized), Specs 1 (P. if b then Q else R),
      Assertions 8 (whole table). Generic table formalized: `LaPToP/BasicTheories/GenericLaws.lean`, node `generic_laws`
      (2026-09-17; on main). 163 nodes.
- [x] §11.3.12 Assertions table (8 laws) + `P. if b then Q else R` (`det_seq_cond`, general `seq_cond_eq_or`) —
      `LaPToP/ProgramTheory/AssertionLaws.lean`, node `assertion_laws`; small gaps closed: `Bunch.size_nat`, `Bunch.union_remove`,
      `HList.length_eq_size_domain`, `Fn.orElse_self/assoc/comp` (added to existing nodes); survey updated: Assertions and Specs
      tables complete (2026-09-17; on main). 164 nodes.
- [x] §3.4 Limits and Reals — `LaPToP/FunctionTheory/Limits.lean`: `lowerLimit`/`upperLimit` (= liminf/limsup), `IsLimit` (the
      Limit Axiom, underdetermined as in the book), existence/consistency/uniqueness, `⇓f ≤ ⇕f ≤ ⇑f` (+ `sup_toFn`/`inf_toFn`),
      monotone/antitone, examples `1/(n+1) → 0`, `(–1)^n` values = [–1,1], `n → ∞`; `IsPredLimit` between eventually/frequently,
      one-sided forms, `¬⇕(1/(n+1) = 0)`; every xreal is a rational-sequence limit; `real = xreal –, (∞, –∞)`; node `limits`
      (2026-09-17; on main). **Every book section §1–§9 is now formalized** (the `(1+1/n)^n = e` remark is prose). §11.3.9
      complete. 165 nodes.
- [x] §11.3.8 ⇑⇓ Distributive laws + real Extreme — `LaPToP/FunctionTheory/QuantifierDistribution.lean`: 4 lattice laws, 10
      arithmetic laws for finite n via `monotone_sup/inf`, `antitone_sup/inf` (continuity on EReal), `mul_sum` (finite D,
      0 ≤ n < ∞), `prod_pow`, `inf_real`/`sup_real`; node `quantifier_distributive_laws`; survey: Quantifiers table complete
      (2026-09-17; on main). 166 nodes.
- [x] Remaining small survey gaps — `Str.at_update`, `copies_add/copies_copies/copies_mem_star`, `HList.toFn_applyBunch`, `HList.comp_pack`,
      `Fn.apply_ite/ite_apply`, `Bunch.nat_eq_Ici`; every not-statable law (decimal Counting, `{A}⧧A`/`[S]⧧S`, bunch-valued
      division/exponentiation/function bunches/strings of bunches, multi-dimensional `@`) explained in its node; survey complete with
      final counts and closing paragraph (2026-09-17; on main). **§11.3 done.** 166 nodes.
- [x] Site consistency pass — two stale claims fixed (`while_loop`: fixed-point account is in `loop_definition`; `time_dependence`:
      space is modelled); identifier check: every declaration named in node prose is in a `lean :=` list, no unlinked module
      declarations; `Blueprint.lean` intro refreshed (full §1–§9 + §11.3 survey + honesty policy); README coverage table and
      per-directory layout; proving-guide §5 lessons (incl.: a `uses` back-edge makes the graph cyclic → generator timeout)
      (2026-09-17; on main). 166 nodes.
- [x] Extension (a): `Str`/`HList` linear orders (`Str.lt_iff_lex`, `HList` lifted `LinearOrder`, `lt_iff_contents_lt`,
      `le_iff_not_lt` ×2); `generic_laws` now covers strings and lists as the book states; survey updated (2026-09-17; on main).
- [x] Extension (b): `Limits.eSeq`, `isLimit_eSeq_iff` (⇕n· (1+1/n)^n = e via `Real.tendsto_one_add_div_pow_exp`); `limits` node
      updated — no unformalized example remains in §3.4 (2026-09-17; on main).
- [x] Extension (c): Exercise 333(b) — `TimeDependence.RealTime` (ℝ≥0∞ clock, operation time δ): redefined `waitUntil` (first test
      after w, `w ≤ t′ ≤ w + δ`), `waitUntil_refines`, `waitUntil_of_max`, `not_exact_refines`; `time_dependence` node updated
      (2026-09-17; on main).
- [x] Extension (d): Blackjack four-variable program — `BJ`, `randDeal` + Substitution Law `pseq_randDeal`, `dealC/dealD/setX/setY`,
      `game`, `game_eq`, `avg_game`, `prob_xWins_game = (n–1)/169`; `blackjack` node updated (2026-09-17; on main).
- [x] Extension (e): §2.3.0 Multidimensional Structures — `Multidimensional.lean` (`HList (HList α)` arrays; `Nested α` with `idx`/
      `modify` and the four `@`/`→` axioms as theorems; both examples); node `multidimensional_structures`; survey Lists 20/21; the
      not-statable classes are now three (2026-09-17; on main). 167 nodes.
- [x] Extension (f): §5.3 space dependence — `TimeDependence.SpaceDependence` (`SD`, `grow`/`shrink`, inductive `RespectsSpace`,
      `RespectsSpace.bounded`, `not_respectsSpace_const`, read examples); `time_dependence` node's last "Not formalized" gone
      (2026-09-17; on main). **(a)–(f) all done.**
- [x] Residual §7.1.5: the T, p implementation — `LaPToP/TheoryDesign/ProgramTreeImpl.lean` (rootless `Pos`, moves, `Below`/`beyond`,
      `impl : ProgramTreeTheory`); `work ⇐ ok` added to the axiom structure (had been omitted); node updated (2026-09-17; on main).
- [ ] Maintenance mode: pull maintainer pushes; rebuild and fix if needed; extend only on request. Residual honesty notes that remain
      by design (all explained in their nodes): §4.2.3 meta-statements (prose); §11.3 not-statable laws (notation, type distinctions,
      bunch-valued operators); the weak-stack "garbage" remark (§7.1.1); the parsing transformers given informally by the book
      (§7.2.2); the time remark of §8.0.1's transformation node; `screen!` output in `assert` (Chapter 9 notation); Merge's literal
      fixed-point refinement (Interleave invariant proved instead); the "strongest implementable solution" in communication
      timing.

## Interpreter (Michal 2026-09-22)
- [x] Phase 1: core AST + fuelled `run` + denote→`Spec` soundness — `LaPToP/ProgramTheory/Interpreter.lean`
      (2026-09-22; on main): `Spec.whileRel` (the terminating-run relation of a loop) with `whileRel_unfold`,
      `whileRefines_whileRel`, **`refines_whileRel`** (it is the strongest solution of the book's while-refinement,
      so a §5.2.0 development transfers to a run); `Interpreter.Prog` (ok / assign / seq / cond / whileDo),
      `run` (fuel = depth of the execution tree, hence structurally recursive and kernel-reducible), `denote`
      into the Chapter 4 notations, `isProgram_denote` for loop-free programs; `denote_of_run` (soundness),
      `exists_run_of_denote` (completeness), `run_le`, `deterministic_denote`, `run_sound`, `run_while_sound`.
      `Demo`: first-order `Exp`/`Bexp` over three integer variables so example programs are data; `sumTo_ten`
      (55), `sumTo_twenty` (210), `sumTo_no_fuel`, and the counting loop `count` with `whileRefines_W` +
      `count_sound`. Nodes `interpreter`, `interpreter_soundness`. 168 nodes.
      Deviations recorded in the node: expressions are Lean functions of the prestate (as `Spec.assign` is);
      fuel is a depth budget; no concurrency, time, channels, scope, assertions, surface syntax or CLI.
- [x] Phase 2a: fuel-free / partial-correctness execution + the §6.1.1 lfp bridge (2026-09-23; on main):
      `Interpreter.Eval`, the big-step operational semantics of `Prog` with no fuel budget — nontermination is
      the absence of a derivation, not a failure value — with `eval_of_run`, `denote_of_eval`, `eval_of_denote`,
      **`eval_eq_denote`** (running, evaluating and specifying a program are one relation),
      `eval_iff_exists_run`, `eval_unique`, `eval_sound`, `eval_while_sound`, and the loop invariant rule
      **`eval_while_invariant`** (no fuel, no variant: partial correctness only); `Diverges` with `diverges_iff`
      (a divergent computation makes `run` fail for every fuel) and `diverges_whileDo`. In `Spec`:
      `whileRel_invariant`, `whileRel_of_always`. `Demo`: `count_partial` (the counting loop again, by the
      invariant `s = i`, with no termination argument) and a loop proved to diverge.
      `LaPToP/RecursiveDefinition/LoopBridge.lean` joins `Spec.whileRel` to §6.1.1: with the recursive timing
      the axioms use, `whileRun b P = whileRel b (P. t:= t+1)` is a fixed point of `whileC` (`whileC_whileRun`)
      and the strongest pre-fixed point (`whileRun_refines_of_prefixed`) for any body that does not decrease
      time, so **`refines_whileRun`** — every `Wh` satisfying `WhileAxioms` is refined by the terminating runs.
      The converse is proved false (`not_refines_whileRun`): `while ⊤ do t:= t+1 od` has no terminating runs
      while the axioms admit every final state at time ∞, so the bridge is a partial-correctness bridge.
      Nodes `interpreter_partial_correctness`, `loop_definition_terminating_runs`. 170 nodes.
      Residual gaps recorded in the nodes: no termination/variant reasoning; the interpreter's state has no
      time variable, so the bridge is stated at the level of `Spec.whileRel` rather than over `Prog` itself.
- [x] Phase 2b (i): variable declaration + framing as `Prog` syntax (2026-09-23; on main):
      in `Scope.lean`, `Spec.newLocal x e P` declares a local on the flat state `State Var Val` by borrowing
      the slot `x`, initializing it to `e` and restoring it; **`Spec.newLocal_eq`** proves it *is* the book's
      `new x: Val := e· P` on the pair state (`Spec.inScope`) under the §5.0.1 frame `{x}ᶜ` — no new notation,
      the two are combined. `newVar_refines_newVarInit` (fixing the arbitrary initial value is a refinement)
      and `newLocal_refines_newVar` (what a machine executes refines `new x: Val· P`).
      In `Interpreter.lean`: `Prog.newLocal` with `run` / `Eval` / `denote` in lockstep — soundness,
      completeness, determinism, `run_le` and the fuel-free triad all extend, because the executed
      declaration is the initializing one. Frames are discharged statically: `writes p` (a local hides its
      own variable), `unchanged_of_eval`, **`frame_denote`** (`writes p ⊆ xs → frame xs· denote p = denote p`)
      and `refines_frame_denote`; `eval_newLocal_self` is leak-freedom. Demo `withLocal`
      (`new i: int := 5· s:= s+i`): kernel run, no-leak theorem, `writes = {s}`, framed specification.
      Node `interpreter_scope`; `variable_declaration` extended. 171 nodes.
      Residual gaps in the node: a declaration is not claimed to be a *program* in the §4.0.3 sense (restoring
      a borrowed slot is not one of the four notations, so `LoopFree` has no case for it); arrays and
      assertions are still specifications only, not `Prog` syntax.
- [x] Phase 2b (ii): array element assignment as `Prog` syntax (2026-09-23; on main):
      §5.1.0's point is that `A i:= e` has no name fixed by the syntax — it writes the slot the index names
      in the prestate — so `Prog.assignAt x e` (assignment to a *computed* name) is the construct, with
      `Spec.assignAt` its denotation, `Spec.assignAt_seq` the substitution that does work ("change `A i:= e`
      to `A:= i→e | A` first"), and `Spec.assignAt_const` showing `Prog.assign` is the constant-name case.
      An array on a flat state is the family of slots it indexes: `Spec.assignArr arr idx e` is the book's
      definition read that way, **`Spec.assignArr_eq_assignAt`** is its `A:= i→e | A` (needs only injectivity
      of `arr`), and **`Arrays.assignElem_iff_assignArr`** ties it back to `Arrays.assignElem` on the book's
      record state with the scalars framed — no duplicated theory. `run` / `Eval` / `denote` in lockstep;
      `writes (.assignAt x e) = Set.range x`, so frames cover arrays unchanged (`writes_assignAt_arr`).
      Demo `ArrayDemo`: the book's two examples *executed* — `A 2:= 3. i:= 2. A i:= 4` ends `i = 2, A 2 = 4`
      (test holds) against the naive `4 = A 2`; `A 2:= 2. A(A 2):= 3` ends `A 2 = 3` from any prestate
      (`ex₂_result`, test fails, ⊥) against the naive `A 2:= 2`. Node `interpreter_arrays`. 172 nodes.
      Residual gaps in the node: an array is a family of slots, not one variable holding a list (a flat state
      has no room for a list value); 2-D arrays and records get no syntax of their own.
- [x] Phase 2b (iii): assertions + backtracking choice as `Prog` syntax (2026-09-23; on main):
      `Prog.ensure b` succeeds unchanged when `b` holds and has no poststate otherwise (§5.4.0's "when `b` is
      false … this is unimplementable"); `Interpreter.assert b` is the *same* program, justified by
      **`Assertions.assert_finite`** — from a state at finite time the finite-time behaviours of `assert b`
      are exactly `ensure b`, so the whole difference (an assertion is implementable by waiting forever)
      lives in the time variable this state has not got. `Prog.or p q` is §5.4.0's choice; since no
      deterministic interpreter can be complete for it, `exists_run_of_denote` / `deterministic_denote` /
      `eval_unique` / `exists_run_of_eval` / `eval_iff_exists_run` / `diverges_iff` now carry `Det p` (the
      fragment without a choice), and `run` resolves a choice by the left branch
      (`refines_denote_or_left`, the book's "normally this choice is made as a refinement").
      **`runAll`** is the searching interpreter — every poststate reachable within the fuel, a choice
      branching and an `ensure` filtering — with `runAll_le`, `eval_of_mem_runAll`,
      `exists_mem_runAll_of_eval` and **`mem_runAll_iff_eval` / `mem_runAll_iff_denote`**: sound *and*
      complete for the whole language. `Diverges` restated as "no poststate" (nontermination for a loop,
      unimplementability for a false `ensure`); `run_eq_none_of_diverges` split out with no hypothesis.
      Demo: `s:= 0 or s:= 1. ensure s=1 = s:= 1` — proved from the §5.4.0 laws, found by `runAll` (one
      poststate, kernel-checked), missed by `run`, and `eval_backtrack` for every prestate.
      Node `interpreter_assertions`; `interpreter_soundness` prose kept honest about `Det`. 173 nodes.
      Residual gaps in the node: assert and ensure are one program here (no time variable, no output
      channel); the error message is not modelled.
- [x] Phase 2c: concrete syntax + `lake exe interp` (2026-09-23; on main):
      `LaPToP/ProgramTheory/InterpreterSyntax.lean` — `Tok`, `tokenize`, and a recursive-descent parser
      (`parseExp`/`parseCond`/`parseProg`/`parseStmt`, all structurally recursive on a fuel read off the
      input, every failure a message) from text into the *same* `Demo.P`, so a parsed program is run by the
      same `run`/`runAll` and denotes the same `Spec`. Grammar is the book's where it can be: `.` is
      sequential composition and binds loosest, so `s:= 0 or s:= 1. ensure s = 1` is the choice then the
      ensure. **`parseToks_sumTo` / `parseToks_count` / `parseToks_backtrack` / `parseToks_withLocal`**:
      the parser produces the very Lean terms the earlier phases proved things about.
      `InterpMain.lean` + `lean_exe interp` in `lakefile.lean` (`LaPToPMain`/Verso untouched): file or stdin
      or `--demo=`, `--n/--i/--s`, `--fuel`, `--all` (runAll), `--selftest`, `--grammar`; prints the final
      state; exit 1 on parse error, 2 on no poststate. Smoked: `--demo=sumTo --n=10` → `s = 55`,
      piped sumTo `--n=20` → `s = 210`, backtracking `--all` → one poststate `s = 1` (and exit 2 without
      `--all`), `new i := 5 in s:= s + i end` → `i` unchanged, failed `assert` → exit 2.
      Node `interpreter_cli`. 174 nodes.
      Residual gaps in the node: the parse theorems are stated of the token lists, because reducing a string
      literal in the kernel costs minutes per example — that the tokenizer takes each source to those tokens
      is checked by `interp --selftest` at run time, not proved; and the syntax is the demonstrations', not
      the book's (three fixed variable names, no array syntax, no output).
- [x] Phase 2d: a clock in the interpreter (2026-09-23; on main):
      `Prog.tick` and `Prog.assert` become constructors, with `run`/`runAll`/`Eval`/`denote`/`writes`/`Det`
      extended in lockstep and `tick` added to the concrete syntax; untimed, `denote_assert_eq_ensure` states
      plainly that an assertion *is* an `ensure` without a clock.
      `LaPToP/ProgramTheory/InterpreterTime.lean`: `TState` (memory + `t : ℕ∞`), `denoteT`, `runT` (sound
      always, complete on `Det`), `EvalT` with `evalT_iff_denoteT`. Time is charged only where the program
      says `tick`. `time_le_of_denoteT` (time does not decrease — §6.1.1's base axiom, for the whole
      language) and `time_top_of_denoteT` (∞ absorbing).
      **`denote_iff_denoteT`**: from a finite starting time, the untimed behaviours are exactly the timed
      ones ending in finite time — the untimed development is this one with the clock forgotten, and
      `Assertions.assert_finite` generalized from one assertion to every program.
      The split: `implementableT_assert` + `runT_assert_of_not` (a false assertion waits forever, its run
      succeeds at `t = ∞`) against `not_implementable_ensure` + `runT_ensure_of_not` (no poststate at all);
      `refines_assertSpec` records that what is implemented refines the book's assertion, which leaves the
      memory unconstrained. For §6.1.1: `denoteT_whileDo_unfold`, `denoteT_whileDo_tick` (a ticking body is
      the axioms' `P. t:= t+1`), `time_le_of_whileDo`.
      Demo: the counting loop with a ticking body ends at `t = 7` from `n = 7`; a false assert ends at ∞
      where a false ensure has no run. CLI gains `--timed`. Node `interpreter_time`; `interpreter_assertions`
      prose updated (its gap is now closed). 175 nodes.
      Residual gaps in the node: a false assertion keeps the memory (a refinement of the book, not an
      equality) and its message is not modelled; no searching timed interpreter, so a choice and a clock
      cannot be combined; the §6.1.1 axioms are still stated over `ZS`.
- [ ] Phase 2e: generalize §6.1.1's `whileC` / `WhileAxioms` from the concrete `ZS` to an arbitrary state
      with a clock, and restate `LoopBridge`'s terminating-runs bridge over timed `Prog` — closing the last
      gap recorded in `interpreter_time`; `runAllT` (a searching timed interpreter, so a choice and a clock
      can be combined) is the small add-on. After that the remaining book gaps are concurrency-as-`Prog` and
      channels — NEXT

## Netty (after interpreter core; see `.sci/netty-plan.md`)
- [x] Netty kernel MVP (2026-09-23; on main) — a separate Lean library `Netty/` and a headless
      `lake exe netty`, independent of Mathlib and of `LaPToP` so it builds in seconds.
      `Netty/Expr.lean`: the boolean and number fragment of the aPToP grammar, with the document's
      operand-position table (positive / neutral / negative), crude types (boolean / number), and
      associative flattening so `a ∧ b ∧ c` has three main operands.
      `Netty/Parser.lean`: tokenizer and recursive-descent parser at the book's precedences (`¬` looser
      than `=`), including the book's *large* `≡ ⟹ ⟸`, which a law file needs because it has no margin;
      ASCII spelling for every operator; number literals.
      `Netty/Law.lean`: laws (optional name, quantified variables, statement), the document's six
      variants per law, one-way matching, and a tautology checker.
      `Netty/laws/boolean.laws` + `Netty/Laws.lean`: the 71 Binary laws of §11.3.1 as a plain text law
      file, read at *compile* time by a `lawFile%` elaborator, so the text is the single definition;
      `Netty.boolean_isTautology` checks in Lean's kernel that all 71 are tautologies.
      `Netty/Doc.lean`: the proof document — lines with depth, the zoom stack, gaps, the focus, the
      context the document's table gains on a zoom in, the suggestion engine, `Cmd` as pure transitions
      (start / apply / applyNamed / direct / zoomIn / zoomOut / setFocus), and `Doc.outcome` reading off
      what the connectives prove (with `a = ⊤` / `a ⇐ ⊤` read as proving `a`).
      `Netty/Render.lean`: the three panes as text. `Netty/Json.lean`: save and load, versioned.
      `Netty/Script.lean`: a `Session` with undo, the script language, and the three demonstrations.
      `Netty/Replay.lean`: the document's own example replayed *in Lean* — `portation_proves`,
      `portation_lines`, `portation_complete` (no gaps, fully zoomed out), and the same for the
      zoom/context proof, the gap proof, and a number-direction proof, all by `decide`, all `propext`
      only. `netty --selftest` ties the shipped law file, the demo scripts and those command lists
      together so they cannot drift.
      Known limits, all documented in the modules: matching was syntactic, not modulo associativity
      (lifted 2026-09-23, below); laws applied to a whole line only (lifted 2026-09-23, below: a main
      operand is a site too); the focus moved only within the innermost level (lifted 2026-09-23,
      below); the document's display collapses
      (nested zooms merged, a one-law subproof folded into its parent line) were not done (lifted
      2026-09-23, below); `if … then …
      else … fi`, quantifiers, bunches, strings, lists, functions and programs are not in the grammar;
      Lake does not track `boolean.laws` as a build dependency, which `--selftest` catches.
- [x] Netty three-pane web UI (2026-09-23; on main) — `Netty/Api.lean` and `netty-web/`.
      `Netty/Api.lean`: the session as one JSON request and one JSON answer — `state`, `cmd` (one line
      of the *existing* script language), `demo`, `reset`, `save`, `load` — answering with the whole
      state: every line with its depth, margin connective, main operands (each rendered with the
      parentheses it carries in the line, `Expr.operandTexts`) and whether it is focusable or
      zoomable; the context laws; the numbered suggestions with their unconstrained variables; the
      outcome; and the three text panes as well. `NettyMain --serve` is the reading and writing loop
      around it, and nothing else. The file commands (`laws`/`load`/`save` with a path) are refused
      over that channel: a proof file travels as text.
      `netty-web/`: a Node server (no dependency but `typescript` and `@types/node`) that spawns
      `lake exe netty --serve`, numbers the requests and forwards `POST /api`, listening on loopback
      only; and a TypeScript client drawing the three panes — the proof as structured lines (gutter,
      direction box or margin connective, the formula as clickable main operands, the law name or the
      gap's `!`), the context, and the suggestions, with direct entry at the focus, undo, zoom out,
      save/load, a text view of the same panes, and keys `0`–`9` / `u` / `o`.
      The document model is *not* duplicated in TypeScript: a click is a script line (`apply #N`,
      `zoom N`, `focus N`, `direct = …`) and every change still goes through `Netty.Doc.step`.
      `netty --selftest` now also replays each demonstration through the request service and saves and
      loads the result, so the protocol cannot drift from the kernel.
      Known limits: the kernel's residuals show through (the display collapses came later, below);
      a saved proof carries the law list,
      so a proof file is ~30 KB; laws are added by `NETTY_CMD`, not from the window; no ML ranking of
      suggestions and no VS Code webview.
- [x] Netty matching modulo associativity (2026-09-23; on main) — `Expr.matchAll` in `Netty/Law.lean`.
      When a law's pattern and the line are associations of the same `BinOp.assoc` operator, both are
      flattened (`flattenOp`) and every cut of the line's operands into as many non-empty *contiguous*
      segments as the pattern has operands is tried, each segment rebuilt left-associated
      (`rebuildOp`). A pattern operand that is not a law variable can only take a single operand — the
      pattern was flattened too, so no operand of it is an association of that operator, which is all a
      longer segment can be — so the search is over segmentations only, not over parses.
      Matching therefore succeeds in several ways: `Expr.matchAll` returns all of them (shortest first
      segment first) and `Doc.suggestions` makes one suggestion of each, so `a ∧ b ⇒ a` offers `x` as
      well as `x ∧ y` from `x ∧ y ∧ z`, `a ∧ a ≡ a` folds `x ∧ y ∧ x ∧ y` to `x ∧ y`, and `+`/`×` read
      the same way at the number type. `Expr.matchWith` is now the first of those matches.
      The recursion is *fuelled* on purpose — fuel is the pattern's size, one unit per level of the
      pattern, so it cannot run out — because a structurally recursive matcher is what lets `decide`
      evaluate a whole session in Lean's kernel, which is how `Netty/Replay.lean` checks its replays.
      Witnessed in Lean: `specialization_reads_both_ways`, `symmetry_reads_both_ways`, `assoc_proves`,
      `assoc_complete` and `no_match_without_a_law_variable`, all by `decide`, all `propext` only.
      `netty --selftest` adds a soundness sweep: every suggestion the whole law list offers for seven
      associations under all three directions (401 steps) is checked to be a tautology, and
      specialization is checked to read `x ∧ y ∧ z` both ways.
      Matching went on modulo symmetry and an identity element in a later chunk, below.
- [x] Netty: a law applied to a part of a line (2026-09-23; on main) — `Doc.sites`, `Doc.rewriteAt` and
      `Doc.suggestions` in `Netty/Doc.lean`. The document applies a law "to a part, as a result of
      minimization", and a suggestion is now generated for each *site* of the line before the focus: the
      whole line, and each of its **main operands** — the parts a single `zoom N` reaches and
      `Expr.operandTexts` draws as separate clickable pieces. A part rewrite writes the line back with
      that part replaced by the instantiated right side; its margin connective is exactly the one a zoom
      in, a single application and a zoom out would have written, because a site carries the numbers the
      zoom stack would compute (`Expr.operandTy` for its type, `Dir.zoom` for its direction) and the
      connective follows the zoom-out rule — `=` when the rewrite was an equality or the position is
      neutral, the level's own direction otherwise. So the position turns the direction on the way in and
      turns it back on the way out, and no new soundness argument is needed: it is the zoom rules with
      the two lines the subproof would have added left out.
      Whole-line suggestions still come first, then the parts in order; dedup, the dropping of identity
      rewrites and the direction/`allows` gate are unchanged; matching is still modulo associativity and
      nothing more; and `apply` / `applyNamed` / `applySuggestion` needed no change, since a suggestion
      is still just a whole new line. Only one level is a site — deeper positions are still reached by
      zooming in.
      Witnessed in Lean, all by `decide`, all `propext` only: `idempotence_misses_the_whole_line` and
      `minimize_proves` / `minimize_complete` (idempotence cannot match `x ∧ (y ∨ y)` as a whole, but
      folds its second main operand to give `x ∧ (y ∨ y) = x ∧ y` in one step), and
      `numberMinimize_proves` / `numberMinimize_is_the_only_successor_step` at the number level (the `≤`
      law `x ≤ x + 1` on the subtrahend of `n - m`, a negative position, is the only `successor` step
      there and writes `n - m ≥ n - (m + 1)` — the turning `number` makes with a zoom in and a zoom out,
      in one step on the outer line).
      `netty --demo=minimize` and `netty-web`'s demonstration menu carry the same fold as a script, and
      `netty --selftest` grew its soundness sweep to nine lines (positive, negative and neutral parts)
      and 1388 suggested steps, all tautologies, plus a named check that idempotence folds `y ∨ y`
      inside `x ∧ (y ∨ y)` in exactly one way.
      One consequence: the context law `a ⇒ b` now applies to parts of the line `a ⇒ b` as well as to
      the whole of it, so the `discharge` demonstration's `apply context` names the line it writes
      (`apply context : = ⊤`) in both the script and `Netty.Replay`.
      A contiguous *segment* of an association (`y ∧ z` inside `x ∧ y ∧ z`) was not yet a site of its
      own; it is, from a later chunk below. (Matching went modulo symmetry and an identity element in a
      later chunk too.)
- [x] Netty anywhere-focus, by recomputing the zoom stack (2026-09-23; on main) — `Doc.canFocus`,
      `Doc.closeToDepth` and `Doc.zoomOut` in `Netty/Doc.lean`. Real Netty lets a click land on any line
      of the proof, and `Cmd.setFocus n` no longer insists that line `n` be in the innermost open level.
      `Doc.canFocus` is the predicate: any line of any *open* level will do. `Doc.closeToDepth` does the
      recompute by running `Doc.zoomOut` — factored out of `Doc.step` so both can call it — until the
      line's level is the innermost one again, spending one unit of fuel (the number of open levels) per
      level closed. Because the zoom-outs are the document's own transition, the state a click reaches is
      exactly the state the user could have reached by closing those levels themselves: each abandoned
      subproof still puts its bottom line back into the line it was zoomed in from, and the direction,
      type and context that come with the focus are the ones that level always had. Zooming out reads a
      level's bottom line and refuses unless the focus is on it, so the recompute moves the focus there
      first — no loss, since the focus is leaving that level in any case. A surviving frame is never
      rebuilt, so `canFocus`, asked before the recompute, still holds after it.
      Refused: a line of a subproof that has already been zoomed out of — one deeper than the innermost
      open level, or one before the first line of the open level at its own depth, which is an earlier
      *closed* subproof at that depth. Re-opening a closed level is a different feature and is not done.
      `Api.lineView`'s `focusable` is now just `Doc.canFocus`, so `netty-web/`'s clickable line numbers
      work for outer lines with no client logic added — only the gutter's tooltip changed, to say whether
      a click would close a subproof, and to say why a greyed number is greyed.
      Witnessed in Lean, all by `decide`, all `propext` only: `anywhere_closes_the_stack`,
      `anywhere_leaves_the_subproof_closed`, `anywhere_proves` and `anywhere_is_discharge` — the
      `discharge` replay with `focus 0` in place of `out`, which writes *the very same document*, so the
      click did precisely what `Cmd.zoomOut` does; `nested_closes_both_levels` and
      `nested_puts_the_subproofs_back`, where one click closes two levels and both subproofs go back into
      their lines; and `reopen_keeps_the_first_subproof_closed`, where a closed subproof stays closed even
      with a new level open at its own depth.
      `netty --selftest` gained `focusTest`, which drives the request service the way the web client
      does: zoom in, take a step, check the outer line comes back `focusable`, send `focus 0`, and check
      that the subproof closed, the focus is there, and the closed subproof's lines are refused.
      Left parked: phase 2e. (Display collapses, matching modulo symmetry and an identity element and
      contiguous association segments as sites were the next three chunks, below.)

- [x] Netty display collapses (2026-09-23; on main) — `Doc.shownLines` and its helpers in
      `Netty/Doc.lean`. A proof written by zooming keeps lines a reader does not need, and the Netty
      document collapses two such patterns. Both are now done, as a *pass over* the document rather
      than a change to it: `Doc.shownLines` says which lines a display draws, at what depth, and with
      what law name at the end of them. `Doc.lines` is untouched, so a saved proof is still the whole
      proof, the script language still calls a line by its index in `Doc.lines`, and a click still
      means what it meant.
      The two collapses: **fold** — a subproof that is a single law application is drawn as the line it
      was zoomed in from, with the law's name moved up onto that line and the two scaffolding lines not
      drawn (`Doc.foldHere`); **merge** — a level whose only two lines are the one a zoom in wrote and
      the one a zoom out wrote has held nothing of its own, so the subproof it held is drawn one level
      further out and its two lines are not drawn (`Doc.mergeHere`), which is the document's "two
      zoom-ins matched by two zoom-outs merge into one zoom step".
      `Doc.collapseStep` scans the drawn lines from the top and tries a merge before a fold, because a
      merge can expose a fold and not the other way round; `Doc.shownLines` runs it to a fixpoint with
      the number of lines for fuel, so a threefold zoom merges twice and then folds. A collapse fires
      only where the matching zoom out has already been written, so a level still being worked in is
      never collapsed, and `Doc.mayHide` refuses to hide the focus or a line a gap follows — no warning
      sign and no place a user is working can vanish.
      `Doc.renderProof` and `Api.lineView`/`stateView` draw `Doc.shownLines`, so the text pane, the
      three web panes and `netty --serve` all show the collapses with no client logic added: the lines
      a collapse hides simply do not arrive, and a line it lifts arrives with a smaller `depth`.
      `Doc.note` moved from `Netty/Render.lean` to `Netty/Doc.lean`, where the collapse pass needs it.
      Witnessed in Lean, all by `decide`, all `propext` only: `fold_keeps_its_four_lines` /
      `fold_collapses` (four lines in the document, two drawn, `idempotent` moved up),
      `fold_shows_what_minimize_shows` (the long way round is drawn line for line as the short way
      round — the same step taken by applying a law to a *part*), `merge_keeps_its_seven_lines` /
      `merge_collapses` (seven lines, five drawn, one level of nesting rather than two),
      `mergeThenFold_collapses` (a merge exposing a fold collapses all the way to two lines),
      `merge_waits_for_the_zoom_out` (nothing is collapsed while the level is still open) and
      `gapInside_is_not_collapsed` (a gap and its warning sign survive).
      Two demonstrations, `netty --demo=fold` and `--demo=merge`, print the pane before and after the
      zoom out that closes the level, so each collapse can be seen happening; `netty --selftest` gained
      `collapseTest`, which checks all of that through the request service the web client talks to.
      `focusTest`'s line count changed from four to two, because the subproof a click closes there is a
      single law application and now folds.
      Left parked: re-opening closed levels, the gap-on-splice justification, and phase 2e. (Matching
      modulo symmetry and an identity element, and then contiguous association segments as sites, were
      the next two chunks, below.)

- [x] Netty matching modulo symmetry and the identity element (2026-09-23; on main) — `Expr.shares`,
      `Expr.lineForms`, `Expr.matchSegment(s)` and `Expr.matchFuel` in `Netty/Law.lean`, with
      `BinOp.comm` and `BinOp.identity` in `Netty/Expr.lean`. The matcher now reads a line modulo all
      three of the things the document says a user should not have to spend a proof step on.
      `BinOp.comm` names the operators the document's `symmetry` laws are about — `∧ ∨ = ⧧` at the
      boolean type, `+ ×` at the number type — and `BinOp.identity` the units it names for them: `⊤`
      for `∧`, `⊥` for `∨`, `0` for `+`, `1` for `×`.
      Symmetry: the group of line operands a pattern operand takes no longer has to be contiguous.
      `Expr.shares` offers every sub-list of what is left, each keeping the line's own order inside it,
      so `a ∧ b ⇒ a` reads `x ∧ y ∧ z` as `y ∧ (x ∧ z)` and offers every sub-conjunction, and `x ∧ y`
      matches `y ∧ x`. A symmetric operator that is not an association — `=` and `⧧` — is matched by
      trying its two operands both ways round instead.
      Identity: a pattern operand that *is* the unit may take no operands at all, so a law written
      `x + 0` reads the bare line `n`; and a unit the line writes may be struck out of it
      (`Expr.lineForms`), so `a ∧ a` reads `x ∧ ⊤ ∧ x`. Only a pattern operand that is *literally* the
      unit may take nothing — a law variable never quietly binds to a unit the line does not mention,
      which is what keeps `a ∧ b ⇒ a` from matching every line there is.
      Readings that need no rearrangement come first, so the old order is a prefix of the new one, and
      `Expr.matchAll` deduplicates, since symmetry and the identity can reach one substitution by more
      than one route. The matcher is still fuelled by the pattern's size, so `decide` still runs whole
      sessions in Lean's kernel; a line that is not an association of the pattern's operator is still
      rejected before any sharing out begins unless the pattern mentions that operator's unit, so
      `Netty.Replay` went only from 86s to 105s.
      No new soundness argument is needed: the line and the matched left side differ only by an
      associativity, a symmetry or a unit, all of which are equalities. `netty --selftest`'s sweep says
      so by evaluation — 2976 suggested steps (up from 1388), over eleven lines including two that
      write a unit (`x ∧ ⊤ ∧ y`, `x ∨ ⊥ ∨ y`), all sound — and its `matchTest` checks the three
      readings by name.
      Witnessed in Lean, all by `decide`, all `propext` only: `specialization_reads_every_way` and
      `symmetry_reads_every_way`; `swap_proves` / `swap_complete`, which prove `x ∧ y ⇒ y` in one step
      where no cut into contiguous segments can; `symmetry_matches_a_swap`, `identity_is_elided`,
      `identity_is_struck_out` and `equality_is_symmetric` at the matcher; the two negative ones,
      `a_variable_does_not_take_the_unit` and `no_match_without_a_law_variable`; and
      `numberUnit_elides_the_zero` / `numberUnit_proves`, where `x + 0 ≤ x + 1` reads the bare line `n`
      and proves `n ≤ n + 1` — the one shape only the identity can reach.
      One consequence for a user: the suggestion list is longer, because a law reads a line every way
      the three allow and each way is a suggestion of its own.
      Left parked: distributivity, arithmetic and any normalisation; the identities the document states
      for `⇒` and `=` (`⊤ ⇒ a ≡ a`, `⊤ = a ≡ a`), since neither is an association a line is read apart
      into; re-opening closed levels; the gap-on-splice justification; and phase 2e. (Contiguous
      association segments as sites were the next chunk, below.)

- [x] Netty contiguous association segments as sites (2026-09-24; on main) — `Expr.segments`,
      `Expr.segmentExpr`, `Expr.replaceSegment`, `Expr.segmentPos` and `Expr.segmentTy` in
      `Netty/Expr.lean`, and `Doc.Part` with `Doc.sites` / `Doc.rewriteAt` in `Netty/Doc.lean`. The
      Netty document reads `x ∧ y ∧ z` as having the part `y ∧ z` just as it has the part `y`, so a
      contiguous run of the operands of an association is now a place a law may be applied to.
      `Doc.sites` offers, after the whole line and the single main operands, every contiguous run of
      two or more operands of an *associative* main operator that is shorter than the whole line;
      `Site.operand : Option Nat` became `Site.part : Part`, where `Part` is
      `whole | operand i | segment start len`, and `Doc.rewriteAt` puts a part back through
      `Part.replace`. A segment goes back left-associated, exactly as `Expr.rebuildOp` writes an
      association.
      No new soundness argument. An associative operator puts every one of its operands in the same
      position, so a run of them is in that same position: the type, the direction that holds inside
      and the connective the step writes in the outer margin are word for word those of a single main
      operand — the argument the minimization chunk already had, read for a run instead of for one. `×`
      is the case that shows the machinery is doing work: it is associative but its operands are
      neutral (a factor is monotonic only for a nonnegative other), so a segment of it is a neutral
      site and admits only `=` whatever the level's direction.
      What it buys: a law that matches two of several operands folds them where they stand and leaves
      the rest alone. `a ∧ a ≡ a` takes `x ∧ y ∧ y ∧ z` to `x ∧ y ∧ z` in one step — a step no site the
      kernel had before could make, since idempotence matches neither the whole line (no sharing out of
      four conjuncts makes two equal halves) nor any single main operand (they are the bare identifiers
      `x`, `y`, `y`, `z`).
      Witnessed in Lean, all by `decide`, all `propext` only: `segmentLine_segments` (the five runs of
      a four-operand association) and `a_pair_has_no_segments`;
      `idempotence_misses_the_whole_association` and `idempotence_misses_every_operand`, the two
      negative ones; `segmentFold_proves` / `segmentFold_complete` / `segmentFold_is_the_only_fold`;
      `times_segments_are_neutral`, the neutral-position site read off `Doc.sites` itself; and
      `symmetry_reads_every_way`, whose list grew by the two swaps the segment sites of `x ∧ y ∧ z`
      make. `netty --demo=segment` carries the fold as a script, and `netty --selftest` checks the same
      reading through the compiled kernel and grew its soundness sweep to twelve lines and 4565
      suggested steps (up from 2976), all tautologies.
      One consequence for a user: the suggestion list is longer again, since each segment is a place of
      its own. Ranking it is still out of MVP.
      Left parked: re-opening closed levels, the gap-on-splice justification, conditional laws at the
      number level, distributivity, arithmetic and normalisation, and phase 2e. (Segment *zoom* was the
      next chunk, below.)

- [x] Netty segment zoom — `Cmd.zoomIn` on a part (2026-09-24; on main) — `Part` and its accessors,
      `Doc.parts`, `Doc.sites`, `Doc.zoomOut` and `Doc.step` in `Netty/Doc.lean`. A part was a place a
      law is applied to; it is now also a level you can work *inside*, as the Netty document treats it.
      `Cmd.zoomIn` takes a `Part` instead of a main-operand number, so `Part` —
      `whole | operand i | segment start len` — is the one place that says what a part is, for a site
      rewrite and for a zoom alike. `Part` gained `exprOf`, `posOf`, `tyOf`, `contextOf`, `render` and
      `zoomable`, and `Doc.sites` became one `filterMap` over `Doc.parts` that reads every field off
      those, so a site and a zoom in cannot disagree about a part's expression, type, direction or
      position — two code paths before, one now. `Frame.operand : Nat` became `Frame.part : Part`, and
      `Doc.zoomOut` splices through `Part.replace`, the same function `Doc.rewriteAt` uses, so a
      segment goes back left-associated as `Expr.rebuildOp` writes an association.
      `Expr.contextOf` was generalized to `Expr.contextOfRange e start len`: the operands *outside* the
      run become the context, and `contextOf e i` is the run of one at `i`. So zooming into `y ∧ y`
      inside `x ∧ y ∧ y ∧ z` gains `x` and `z`, exactly as zooming into one operand gains the other
      three. `⇒` and `⇐`, the two operators whose context depends on which operand was chosen, are not
      associations, so for them a run is always one operand and nothing changed. `Part.whole` is
      refused as a zoom target: it is the level one is already on.
      Nothing new is claimed. The subproof's first line is `Expr.segmentExpr start len`, its type and
      direction are `Expr.segmentTy` and `Dir.zoom (Expr.segmentPos …)` — the numbers the segment
      *site* already carried, on the argument the previous chunk made — and the zoom out writes `=`
      when the position is neutral or the subproof proved an equality and the parent's direction
      otherwise, which is the rule `Doc.zoomOut` already had. The display collapses needed nothing
      added.
      Surface: `zoom S:L` in the script language beside `zoom N`, with `zoom 1:1` refused and the
      advice to write `zoom 1`. The save format went to 2, since a level now records a `Part` where it
      recorded an operand number; a format 1 file is refused rather than read with its zooms mistaken
      for zooms into the whole line.
      Witnessed in Lean, all by `decide`, all `propext` only: `segmentZoom_opens_the_segment` and
      `segmentZoom_remembers_the_run`; `segmentZoom_gains_the_others` (`x` and `z` as context);
      `times_segment_zoom_is_neutral`, where a `×` segment flattens the direction to `=` — the site's
      rule read off the level; `the_whole_line_is_not_a_zoom_target`; `segmentZoom_proves` /
      `segmentZoom_complete`; `segmentZoom_splices_what_the_site_writes`, where the spliced line is,
      connective and formula, the line the one-step segment rewrite writes; and
      `segmentZoom_collapses` / `segmentZoom_shows_what_segmentFold_shows`, where the display draws the
      long way round as the short way round. Every existing operand-zoom replay, collapse,
      anywhere-focus and segment-site witness is unchanged but for `.zoomIn 1` now reading
      `.zoomIn (.operand 1)`.
      `netty --demo=segfold` shows it — `zoom 1:2`, the context pane with `x` and `z`, the fold, the
      splice — and `netty --selftest`'s `collapseTest` checks that `segfold` draws what `segment`
      draws, which is the segment zoom driven end to end through the request service the web client
      talks to.
      Left parked: re-opening closed levels, the gap-on-splice justification, conditional laws at the
      number level, distributivity, arithmetic and normalisation, and phase 2e. (A *click* on a segment
      in `netty-web/` was the next chunk, below.)

- [x] Netty segment clicking in `netty-web/` (2026-09-24; on main) — `Api.PartView` and
      `Api.LineView.zooms` in `Netty/Api.lean`, `Part.span` / `Part.textIn` in `Netty/Doc.lean`, and
      `formula` / `segmentsRow` in `netty-web/src/client.ts`. `zoom S:L` existed in the script language
      from the previous chunk, but the window drew only the single main operands as click targets. Now
      it offers every part the kernel does, and offers them by the kernel's own name for them.
      `LineView.zooms` is one entry per zoomable part of the line before the focus, in `Doc.parts`
      order — each main operand, then each contiguous segment — carrying `name` (what `zoom` calls it:
      `Part.render`, so `1` or `1:2`), `text` (the part as it stands in the line: `Part.textIn`) and
      `start` / `len` (`Part.span`). `Part` gained `span` and `textIn`, so the naming and the rendering
      of a part live where the part does; `LineView.zoomable` became `!zooms.isEmpty`, the same
      predicate computed once instead of twice.
      The client sends `zoom ${z.name}` and composes no name itself, which is the point of the shape: a
      click cannot mean a different part from the one a suggestion's site or a script zoom means,
      because there is one string and the kernel wrote it. A run of two or more operands has nowhere in
      the line to be clicked — its operands are not adjacent to any one button — so the runs are drawn
      on a `runs:` line under the line they belong to, as dashed buttons labelled with the run; single
      operands are clicked in the line as before. `Part.whole` is never offered, as `Cmd.zoomIn`
      refuses it.
      `netty --selftest` gained `zoomTest`, which drives the click path through the request service the
      client talks to: for `x ∧ y ∧ y ∧ z` the answer must offer exactly `0 1 2 3 0:2 0:3 1:2 1:3 2:2`
      with the texts the buttons carry; every one of the nine must be a name the kernel accepts and must
      open a level whose first line is the part its button was labelled with; clicking the run `1:2`
      must gain `x` and `z` as context; and the outer line must then offer nothing, being no longer the
      line before the focus. By hand over the wire: a non-association (`⇒`) offers no runs, `×` offers
      both of its, and an atom offers nothing.
      Left parked: highlighting the site a suggestion came from, re-opening closed levels, the
      gap-on-splice justification, conditional laws at the number level, distributivity, arithmetic and
      normalisation, and phase 2e. (Ranking the suggestion list was the next chunk, below.)

- [x] Netty deterministic suggestion ranking (2026-09-24; on main) — `Doc.rank`, `Part.rank`,
      `dedupBy` / `stableBy` and `Suggestion.part` in `Netty/Doc.lean`. Every widening of matching had
      made the suggestion list longer — modulo associativity, symmetry and the identity element, then
      every main operand and every association segment as a place a law may be applied to — and it was
      the loudest thing the window showed: 227 steps for `x ∧ y ∧ y ∧ z` under the shipped law list, in
      whatever order they happened to be generated. `Doc.rank` is now the order, a heuristic written
      down rather than learned (ML ranking stays out of MVP), most important key first:
      (1) applicable before unconstrained, which is the split the pane already drew as greyed rows;
      (2) the more specific place — `Part.rank`: the whole line `0`, a single main operand `1`, a run of
      operands its own length — so the whole line, then the operands, then the shorter runs;
      (3) fewer unconstrained variables, among the ones that cannot yet be taken;
      (4) the shorter line it writes, since a calculation is usually after the step that folds and every
      law that can fold a line has a variant that can pad it; and
      (5) the order the suggestions were made in — the context's laws, the law list's own order, the
      variants, then `Expr.matchAll`'s readings — so the last word belongs to the law file, the one part
      of the order a user writes themselves.
      `Suggestion` gained `part : Part`, which key (2) reads, and `dedup` became `dedupBy` on
      `(law, op, result)` so that two places writing one and the same line are still offered once — one
      step, not two — credited to the first place that made it, which is the one key (2) prefers. The
      sort is `stableBy`, one bucket pass per distinct key value, composed least-important key first:
      stable by construction, and structurally recursive rather than well-founded, which is what keeps
      `decide` able to run a whole session in Lean's kernel. `Netty.Replay` went from 166s to 192s.
      Witnessed in Lean, by `decide`, `propext` only: `suggestions_are_ranked` — for `x ∧ y ∧ z` under
      the whole law list the keys never go backwards, and ranking the ranked list is the ranked list,
      which is what it means for the order to be total and the sort stable.
      `specialization_reads_every_way` now reads `x, z, y, x ∧ y, y ∧ z, x ∧ z`: the same six
      sub-conjunctions, the single conjuncts first because key (4) puts the shorter line first.
      `symmetry_reads_every_way` is unchanged, its seven results being all of one size.
      `netty --selftest` gained `rankTest`, on the 227-step line: the keys never go backwards, ranking
      the ranked list changes nothing, asking twice gives the same list, all 207 applicable steps come
      before all 20 unconstrained ones, and `x ∧ y ∧ z` — the fold neither the whole line nor a single
      operand can make — leads the steps offered on a run of operands, ahead of the two longer runs that
      overlap it. `Netty/Api.lean` and `netty-web/` are untouched: the client draws the kernel's order
      and does not re-sort, so `apply #N` and the keys `0`–`9` are the ranked positions.
      Measured: the first suggestion for `x ∧ y ∧ y ∧ z` went from `¬¬(x ∧ y ∧ y ∧ z)`, a pure padding,
      to `y ∧ (x ∧ z)`, a real contraction; `x ∧ y ∧ z` went from position 163 to 124. Key (2) outranked
      key (4) as that task specified, so all ~120 whole-line rearrangements still came before any step on
      a part; that was swapped in the next chunk, below.
      Left parked: highlighting in the proof pane which part a suggestion would rewrite (the field is
      there now), ML ranking, re-opening closed levels, the gap-on-splice justification, conditional
      laws at the number level, distributivity, arithmetic and normalisation, and phase 2e.

- [x] Netty ranking: the shorter line outranks the place (2026-09-24; on main) — the `stableBy`
      composition in `Doc.rank`. Michal's call, on the measurement the previous chunk reported: with the
      place above the length, every whole-line rearrangement came before every step on a part, so
      `x ∧ y ∧ y ∧ z = x ∧ y ∧ z` — the fold that neither the whole line nor any single operand can
      make — was the 124th of 227 suggestions, behind some hundred ways of reassociating and commuting
      the whole line. The two passes are swapped, so the order is now: applicable before unconstrained;
      fewer unconstrained variables; **the shorter line the step writes**; then the more specific place
      (whole line, single operands, shorter runs, longer runs); then the law file's own order. That fold
      is now the 3rd of the 227, and the only two ahead of it write a line just as short —
      `distributive` contracting the whole line.
      The place still does real work: it separates steps that write lines of the same length. That is
      why `symmetry_reads_every_way`'s seven results, all of one size, are unchanged — five whole-line
      swaps before two segment swaps — and why `specialization_reads_every_way` is unchanged too, its
      six readings all being whole-line and already ordered by length.
      `Netty/Api.lean` and `netty-web/` are still untouched: the client draws the kernel's order and does
      not re-sort. `Replay.key` and `rankTest`'s key list carry the new order, and `rankTest` now checks
      the point head on — the fold is the third step offered, the two ahead of it write a line no longer
      than it does, and it is still the first step offered on a run of operands — besides the checks it
      already had: the keys never go backwards, ranking the ranked list changes nothing, asking twice
      gives the same list, and all 207 applicable steps come before all 20 unconstrained ones.
      Left parked: highlighting in the proof pane which part a suggestion would rewrite, ML ranking,
      re-opening closed levels, the gap-on-splice justification, conditional laws at the number level,
      distributivity, arithmetic and normalisation, and phase 2e.

- [x] Netty: a gap is carried out of the subproof that holds it (2026-09-24; on main) — `Doc.zoomOut`
      and `Doc.openGaps` in `Netty/Doc.lean`. Every subproof used to splice back the same way —
      `why := "zoom out"`, no gap — so after a direct entry *inside* a level, the outer line before the
      splice drew neither a law name nor `!`: a reader of the outer level saw a step with nothing said
      about it. But a zoom out justifies the outer step *by the subproof*, and a subproof with a hole in
      it justifies nothing; the Netty document puts a warning on the line just before every logical gap,
      and after the splice that line is the one the zoom was made from. So `Doc.zoomOut` now marks a gap
      on `Frame.zoomLine` when the level being closed still holds one. `Doc.openGaps` is the test: the
      gaps at or after the level's first line. Every line from there on belongs to this level or to a
      subproof of it, and a subproof that was zoomed out of has already left its own gap on a line of
      this level, so the carrying is transitive by construction and needs no recursion. The undo branch —
      zooming out of a level of one line — marks nothing: no step has been taken there, and only a step
      leaves a gap.
      A level with no gaps splices exactly as before: a single law application still folds with its name
      lifted, and a longer justified subproof still leaves the outer step unannotated, its justification
      being the lines inside. Nothing else moved: `Doc.note` already drew `!` for a gap, `Doc.mayHide`
      already refused to collapse a line a gap follows, `Doc.outcome` already refused a document with a
      gap in it, and `Api.LineView` already carried `gap` and `note` — so the window shows the warning
      with no client change, and an abandoned gappy subproof carries its gap out through a *click* too,
      since `Doc.closeToDepth` closes levels by running `Doc.zoomOut`.
      Witnessed in `Netty/Replay.lean`, all by `decide`, all `propext` only:
      `gapInside_gaps_the_line_before_the_splice` and `gapInside_proves_nothing`;
      `fold_splices_without_a_gap` and `merge_splices_without_a_gap`, the negative ones, where a
      one-step and a two-step justified subproof leave the outer line clean;
      `gapCarries_carries_it_all_the_way_out` and `gapCarries_is_not_collapsed`, two levels down, a gap
      at each level and no collapse over any of them; and `gapCarries_is_the_same_by_clicking`, where
      `focus 0` writes the very same lines as the two zoom-outs. `gapInside_is_not_collapsed` now reads
      `["!", "!", "", ""]` where it read `["", "!", "", ""]` — that second warning sign is the whole
      change, seen from the display. `netty --selftest` gained `gapTest`, which drives it through the
      request service: the same three commands with the subproof's step typed in and with it taken from
      `idempotent`, the first leaving four lines with warnings on lines 0 and 1 and claiming nothing,
      the second leaving the two folded lines with `idempotent` lifted and a proof. It is not a
      `--demo=`, because a proof that keeps a gap never proves anything and `--demo=` runs only proofs
      that do.
      Left parked: highlighting in the proof pane which part a suggestion would rewrite, ML ranking,
      re-opening closed levels, conditional laws at the number level, distributivity, arithmetic and
      normalisation, and phase 2e.

- [x] Netty: highlighting the site a suggestion would rewrite (2026-09-24; on main) —
      `Api.partView` and `SuggestionView.site` in `Netty/Api.lean`, `showSite` in
      `netty-web/src/client.ts`. `Suggestion.part` had carried the place a step rewrites since the
      ranking, and the window drew none of it: the answer's `SuggestionView` had `law`, `op`, `result`
      and `holes` and nothing about *where*, so the document's minimization story — a law applied to a
      part of a line — was invisible in the very pane that offers it.
      The site travels in the same shape and under the same name as a zoom target. `Api.partView` is one
      function — `name := Part.render`, `text := Part.textIn`, `start`/`len := Part.span` — and both
      `LineView.zooms` and `SuggestionView.site` are built by it, so a suggestion's site and a click's
      zoom target cannot disagree about what a part is called or how it reads. The whole line is a part
      too, and a client tells it from a run by `len = 0`; it never appears among the zoom targets,
      `Part.zoomable` refusing it as `Cmd.zoomIn` does.
      In `netty-web/`, `formula` marks each operand `data-operand=i` and each operator between two of
      them `data-op-before=i`, and `showSite` writes a `site` class over the run the pointer's
      suggestion names — the whole formula for a whole-line step, one operand for a step on one, a run of
      operands with the operators between for a step on a run, and that run's dashed button below the
      line with it. It writes classes rather than redrawing, because a redraw under the pointer takes
      the row being pointed at out of the document; `pointerenter`/`pointerleave` and `focus`/`blur`
      drive it, so the keyboard lights the same part the pointer does. No new layout, no new request.
      Witnessed in Lean by `decide`, `propext` only: `segmentFold_is_credited_to_the_run` — on
      `x ∧ y ∧ y ∧ z` the fold that only a run can make is credited to `.segment 1 2`, and the padding
      by `double negation` to `.whole`. `netty --selftest` gained `siteTest`, which reads it off the
      request service the client talks to: that fold's site is `1:2` reading `y ∧ y`, the padding's site
      is the whole line with `len = 0`, and all 227 sites on that line are parts the same answer offers
      as zoom targets, each reading letter for letter as the part it names — so a highlight can always
      be drawn, and it cannot name a part the line does not have. The client type checks and builds
      (`npm run check`, `npm run build`), and the page and its `/api` answers were smoke tested against
      the running server.
      Left parked: re-opening closed levels, conditional number-level laws, ML ranking, distributivity,
      arithmetic and normalisation, and phase 2e.
- [x] Netty: going back into a closed level (2026-09-24; on main) — `Netty/Doc.lean`, item 17 of
      `.sci/netty-plan.md`. A click could land on any line of an *open* level and nowhere else; a
      subproof that had been zoomed out of was closed for good. Now `Doc.reopenStep` is the exact
      inverse of `Doc.zoomOut` — the line the zoom-out wrote goes away again and the frame is rebuilt
      from what the level's first line carries, the new `Line.part` among it, with position and context
      recomputed off a line the zoom-out did not change — so the state a click reaches is one the user
      could have reached by zooming. `Doc.refocus` is the whole of `focus N` (close the levels that
      start after the line, re-open the closed ones it is inside, close anything still open below it),
      and **`Doc.canFocus` is now defined as `refocus` succeeding**, so the predicate the window greys
      by cannot disagree with the move a click makes; the old structural test survives as
      `Doc.inOpenLevel`, and `Doc.reopensOn` says which of the two moves a click would make.
      The gap a zoom-out carried out is taken back with it — that is exactly the flag it wrote, since
      the last line of a level never carries a gap — so going in and out of a gappy subproof changes
      nothing (`reopen_then_zoom_out_is_the_same_document`), and `reopen_undoes_the_zoom_out` witnesses
      the round trip as an equality of whole documents.
      Refused, honestly and narrowly: a subproof closed *before* later work, since taking its zoom-out
      back would take that work with it (`work_after_keeps_the_subproof_closed`). Ten witnesses by
      `decide`, `propext` (two also `Quot.sound`); `netty --selftest`'s `focusTest` now goes back in
      through the request service and checks the refusal too; `netty-web/` gained `reopens` on
      `LineView` and a tooltip that says which of the three things a click would do, or why it cannot.
      Left parked: conditional number-level laws, ML ranking, distributivity, arithmetic and
      normalisation, and phase 2e.
- [x] Netty: conditional laws at the number level (2026-09-24; on main) — item 18 of
      `.sci/netty-plan.md`. `x ≤ x + y ⇐ 0 ≤ y` was unusable where it is most wanted: a law's readings
      put its *own* main operator in the margin, and that one is `⇐`, so only a boolean line was ever
      offered it. `Law.conditional` reads such a law with its consequent in the margin and the
      antecedent left over as a premise, for the number directions `≤ < ≥ >` — the deliberate limit is
      that a boolean conditional law already stands in a boolean margin, so reading it that way too
      would offer every such law twice; the reason is written down and lifting it is a later round.
      The premise is no new kind of obligation: `Doc.suggestions` instantiates it and asks
      `Law.settles` — the same match the pane would make on a line holding it, so a `context` law from
      a zoom in settles a domain condition. Settled, the step is ordinary; unsettled, it is offered
      *with* the premise and taking it leaves the gap direct entry leaves, with the premise recorded on
      the line (`Line.premise`). `Doc.rank` gained one key: a step that needs nothing before a step
      that leaves a gap. New example law list `Netty/laws/number.laws` + `Laws.number`, checked by
      `Law.holdsOnInts` on `-2 … 2` (`number_holdsOnInts`) — weaker than `boolean_isTautology`, and
      said so: a test a law false in general can pass. `Expr.evalInt` / `evalProp` exist for that check
      alone; no suggestion does arithmetic.
      Eleven witnesses by `decide`, `propext` only, including the proof of `0 ≤ m ⇒ n ≤ n + m` through
      a number level with its premise discharged by the context, and the same law on the same line
      offered discharged one way and gapped the other. `netty --selftest` gained `conditionalTest` and
      a staleness check for the new law file; the panes and `netty-web/` say of a step that would leave
      a gap what it would leave to prove.
      Left parked: the boolean conditional reading, a better check for number laws, ML ranking,
      distributivity, arithmetic and normalisation, and phase 2e.
- [x] Netty: the conditional reading at the boolean level (2026-09-24; on main) — item 19 of
      `.sci/netty-plan.md`. Item 18's deliberate limit lifted: `Law.conditional` now reads any margin
      connective, so `(a ⇒ b) ⇒ (a ∧ c ⇒ b ∧ c)` offers `a ∧ c ⇒ b ∧ c` with `a ⇒ b` as a premise. No
      new machinery — the premise, `Law.settles` and the gap are item 18's. The guard that replaces the
      limit is written into the law's comment: conditional readings come last in `Law.variants` so the
      dedup keeps the reading that needs nothing, and `Doc.rank` puts steps that need nothing first.
      Measured on `x ∧ y ∧ y ∧ z`: 227 rows → 247, **applicable unchanged at 207**, every new row
      greyed — and not by accident, since monotonicity and transitivity laws relate the line to a third
      formula the line does not determine. Supplying that by hand is the document's small dialog box,
      which the kernel lacks; it is now the named next thing rather than a silent limit. What the lift
      does buy is the *context*, which is ground: `Replay.ponens` proves
      `a ⇒ ((a ⇒ (b ⇒ c)) ⇒ (b ⇒ c))` by the context rewriting `b` to `c` with `a` as the premise it
      needs, and dropping the outer `a ⇒ …` turns the same step into a gap that claims nothing.
      `matchTest`'s soundness check now reads a conditional row as `premise ⇒ (line op result)` — the
      right justification, and 5353 suggested steps pass it. `Replay.key` had been missing the premise
      key since item 18 (it passed only because no boolean line had a conditional row); fixed.
      Ten witnesses by `decide`, `propext` only; `conditionalTest` drives the boolean half through the
      request service; `netty-web/` needed nothing. Cost: `lake build netty` about 4m20 → about 6m, and
      one replay needed `maxHeartbeats` raised.
      Left parked: supplying a law variable by hand, a better check for number laws, ML ranking,
      distributivity, arithmetic and normalisation, and phase 2e.
