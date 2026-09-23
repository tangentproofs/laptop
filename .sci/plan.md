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
- [ ] Phase 2b: more constructs — variable declaration and framing, arrays, assertions as syntax — and
      eventually a CLI binary — NEXT
