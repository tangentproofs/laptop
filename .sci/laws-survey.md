# aPToP §11.3 Laws — survey of Lean coverage (2026-09-17; complete)

One line per law of the Reference chapter (pp. 235–244): the Lean theorem stating it (module in
parentheses; `B.` = `LaPToP.BasicTheories`, `DS.` = `LaPToP.DataStructures`, `FT.` = `LaPToP.FunctionTheory`,
`PT.` = `LaPToP.ProgramTheory`, `C.` = `LaPToP.Concurrency`), or "not modelled: …" with the reason. "(ℤ only)" etc. marks a law
stated for a specific type where the book's is generic; "(def)" marks a book equation that is the Lean
definition itself. Counts: total / covered / missing per table at the end.

## 11.3.0 Generic — `B.GenericLaws` (added 2026-09-17)
- x=x Reflexivity — `eq_refl'`
- x=y = y=x Symmetry — `eq_symm_iff`
- x=y ∧ y=z ⇒ x=z Transitivity — `eq_trans_of`
- x=y ⇒ f x = f y Transparency — `transparency`
- x⧧y = ¬(x=y) Unequality — `ne_iff_not_eq`
- if ⊤ then x else y = x; if ⊥ then x else y = y Case Base — `ite_true_base`, `ite_false_base`
- if a then x else x = x Case Idempotent — `ite_idem`
- if a then x else y = if ¬a then y else x Case Reversal — `ite_reversal`
- x≤y = x = x↓y; x↓y ≤ x ≤ x↑y; x≤y = y = x↑y — `le_iff_eq_min`, `min_le_self_le_max`, `le_iff_eq_max`
- x≤x Reflexivity; ¬ x<x Irreflexivity — `le_refl'`, `not_lt_self`
- Exclusivity ×3 — `not_lt_and_eq`, `not_gt_and_eq`, `not_lt_and_gt`
- x≤y = x<y ∨ x=y Inclusivity — `le_iff_lt_or_eq'`
- Transitivity ×4 (≤≤, <≤, <<, ≤<) — `le_le_trans`, `lt_le_trans`, `lt_lt_trans`, `le_lt_trans`
- x>y = y<x; x≥y = y≤x Mirror — `gt_iff_lt'`, `ge_iff_le'`
- ¬ x<y = x≥y; ¬ x≤y = x>y Totality — `not_lt_iff_ge`, `not_le_iff_gt`
- x≤y ∧ y≤x = x=y Antisymmetry — `le_antisymm_iff'`
- x<y ∨ x=y ∨ x>y Trichotomy — `trichotomy'`
- Idempotence, Symmetry, Associativity of ↑ and ↓ — `max_idem`, `min_idem`, `max_symm`, `min_symm`, `max_assoc'`, `min_assoc'`
- Distributivity ×2 — `max_min_distrib`, `min_max_distrib`
- Connection ×4 — `max_le_iff'`, `min_le_iff'`, `le_max_iff'`, `le_min_iff'`
- x↑y = if x≥y then x else y; x↓y = if x≤y then x else y — `max_eq_ite`, `min_eq_ite`
- Coverage: the order laws are for any `LinearOrder` (ℤ, ℕ, ℚ, ℝ, `Char`, and `ℕ∞`/`XInt` as used in the
  formalization); the book's lexicographic order on strings/lists is `List.lt` (`DS.Strings` `[LT]`,
  `HList` `LT` instance) — a `LinearOrder` on `Str α` is not declared, so the string/list instances of these
  laws are not asserted here.

## 11.3.1 Binary — `B.Binary`
- All laws of the table are theorems of `B.Binary` (101 theorems): ⊤, ¬⊥, ⊤⧧⊥ (`top_eq`, `not_bot`,
  `top_ne_bot`); Mirror `rimp_eq_imp`; Double Negation `not_not`; Excluded Middle `excluded_middle`;
  Noncontradiction `noncontradiction`; Base ×4; Identity ×4; Idempotent ×2; Reflexive ×2; Indirect Proof ×2;
  Specialization; Associative ×5; Symmetry ×4; Antisymmetry `imp_and_imp`; Discharge ×2; Antimonotonic ×2;
  Monotonic ×3; Duality ×2; Exclusion ×2 (`imp_not_comm`, `beq_not`/`bne_eq_not_beq`); Inclusion ×3
  (`imp_eq_not_or`, `imp_eq_and_beq`, `imp_eq_or_beq`); Absorption ×2; Direct Proof ×3 (`modus_ponens`,
  `modus_tollens`, `or_and_not_imp`); Transitive ×5; Distributive ×9; Generalization; Antidistributive ×2;
  Portation ×2; Conflation ×2; Equality and Difference ×2; Resolution (`resolution_left/middle/right`);
  Case Creation ×3; Case Analysis ×2 (`cond_eq_or`, `cond_eq_and`); One Case ×8 (`cond_top_left` …
  `cond_absorb_bne`); Case Absorption ×6; Case Distributive: `not_cond`, `cond_op` (∧ ∨ = ⧧ ⇒ ⇐ via an
  arbitrary binary operator), `cond_op_cond`, `cond_and`, `cond_and_cond`.
- Nothing missing.

## 11.3.2 Numbers — `B.NumberLaws` (extended numbers `XInt`) and `B.Numbers`
- Counting (d0+1 = d1 … d9+1 = (d+1)0) — not modelled: decimal notation, decided by `norm_num` on instances
  (recorded in `number_laws_additive`)
- x+0 = x, x+y = y+x, x+(y+z) = (x+y)+z — `add_zero`, `add_comm`, `add_assoc`
- Cancellation (finite x) — `add_left_cancel_iff`; Absorption ∞+x, –∞+x — `top_add`, `bot_add`
- –x = 0–x, – –x = x, –(x+y), –(x–y) — `neg_eq_zero_sub`, `neg_neg`, `neg_add`, `neg_sub`
- Semi-distributivity –x×y, –x/y — `neg_mul`, `neg_mul_eq_mul_neg`, `neg_div`, `neg_div_eq_div_neg`
- x–0, x–y = x+–y, Addition-Subtraction ×2, Cancellation, Inverse, Absorption ×2 — `sub_zero`, `sub_eq_add_neg`,
  `add_sub`, `sub_add`, `sub_left_cancel_iff`, `sub_self`, `top_sub`, `bot_sub`
- x×0 = 0 (finite), x×1, symmetry, distributivity, associativity, cancellation, absorption ×2 — `mul_zero`,
  `mul_one`, `mul_comm`, `mul_add`, `mul_assoc`, `mul_left_cancel_iff`, `mul_top`, `mul_bot`
- x/1, 0/x, x/x, Multiplication-Division ×4 (incl. (x/y)×y = x), Annihilation x/∞ — `div_one`, `zero_div`,
  `div_self`, `mul_div`, `mul_div_eq_div_mul`, `div_mul_eq_div_div`, `div_div`, `div_mul_cancel`, `div_top`,
  `div_bot`
- x⁰ = 1, x¹ = x — `pow_zero`, `pow_one`
- Direction –∞<0<1<∞ — `direction`; Reflection x<y = –y<–x — `lt_iff_neg_lt_neg`; Cancellation/Translation,
  Scale — `add_lt_add_iff_left`, `coe_mul_lt_coe_mul_iff`, `mul_lt_mul_iff_left`; Trichotomy `trichotomy`;
  Extremes `extremes`; `max_top`, `min_bot`
- Nothing statable missing (Counting is notation).

## 11.3.3 Bunches — `B.Bunch`, `B.Numbers`
- Elementary, Union, Intersection, Removal — `elem_subset_elem`/`elem_subset_iff`, `mem_union`, `mem_inter`,
  `mem_remove`
- Idempotence/Symmetry/Associativity of `,` and `‘` — `union_self`, `union_comm`, `union_assoc`, `inter_self`,
  `inter_comm`, `inter_assoc`
- Antidistributivity, Distributivity, Generalization, Specialization, Reflexivity, Antisymmetry,
  Transitivity, Mirror — `union_subset_iff`, `subset_inter_iff`, `subset_union`, `inter_subset`,
  `subset_refl`, `subset_antisymm_iff`, `subset_trans`, `superset_iff`
- Size: ¢null = 0, ¢x = 1, ¢(A,B)+¢(A‘B) = ¢A+¢B, ¬x:A = ¢(A‘x)=0, A:B ⇒ ¢A≤¢B, ¢A=0 = A=null — `size_null`,
  `size_elem`, `size_union_add_size_inter`, `not_mem_iff_size_inter_elem`, `size_le_size`, `size_eq_zero_iff`;
  ¢nat = ∞ — `size_nat` (`B.Numbers`, added 2026-09-17)
- Absorption ×2, Inclusion ×2, Distributivity ×4 — `union_inter_self`, `inter_union_self`,
  `subset_iff_union_eq`, `union_eq_iff_inter_eq`, `union_union_distrib`, `union_inter_distrib`,
  `inter_union_distrib`, `inter_inter_distrib`
- Union Removal ×2, Intersection Removal — `remove_union`, `remove_remove`, `inter_remove`,
  `inter_remove_comm`, `(A, B)–, C = A–, C , B–, C` — `union_remove` (added 2026-09-17)
- Conflation/Monotonicity ×2 — `union_subset_union`, `inter_subset_inter`
- Induction null: A, Identity, Base — `null_subset`, `union_null`, `inter_null` (the symmetric forms
  `null, A = A`, `null‘A = null` follow by `union_comm`/`inter_comm`; not separately stated)
- Interval ×3 — `mem_interval`, `size_interval_of_le`, `nat_eq_iUnion_interval` (nat = 0,..∞ in the form
  of a union of intervals); `nat = 0,..∞` — `nat_eq_Ici` (`B.Numbers`; the interval notation has ℤ bounds, so ∞ is
  rendered by the unbounded interval; recorded in `bunch_named_bunch_laws`)
- Division by 0 (∞, –∞: x/0; xreal: 0/0) — not modelled: bunch-valued division (division is a function here;
  recorded in `bunch_operator_distribution`)
- Adding/Multiplying Exponents (bunch inclusion of powers) — not modelled: bunch-valued exponentiation
  (recorded in `bunch_operator_distribution`)
- Distribution: –null, –(A,B), A+null, (A,B)+(C,D) — `neg_null`, `neg_union`, `add_null`/`null_add`,
  `union_add_union` (and `add_elem`)

## 11.3.4 Sets — `B.Bunch` (`HSet`)
- {~S} = S, ~{A} = A, {A}⧧A, A ∈ {B} = A: B, {A} ⊆ {B} = A: B — `pack_contents`, `contents_pack`, (`{A}⧧A`:
  type distinction, **not statable** — recorded in `bunch_vs_set`), `mem_pack`, `pack_subset_pack`
- {A}: B = A: B (a set as an element of a bunch of sets) — `pack_mem_power` covers `{A}: 𝒫B`; the general
  form is set membership in this model (recorded in `set_axioms`)
- ${A} = ¢A, {A} ∪ {B} = {A, B}, {A} ∩ {B} = {A‘B}, {A} = {B} = A = B, {A} ⧧ {B} = A ⧧ B — `card_pack`,
  `pack_union_pack`, `pack_inter_pack`, `pack_inj` (the `⧧` form is its negation)

## 11.3.5 Strings — `DS.Strings`
- S; nil = S = nil; S, associativity — `append_nil`, `nil_append`, `append_assoc`
- ↔nil = 0, ↔i = 1, ↔(S;T) = ↔S+↔T — `len_nil`, `len_item`, `len_append`
- ¢nil = 1, ¢(A;B) ≤ ¢A×¢B (bunch strings) — not modelled: strings of bunches (recorded in
  `string_axioms_copies_update`)
- (S;i;T)↔S = i — `at_append_item_append`; S;i;T⊲↔S⊳j = S;j;T — `update_append_item_append`;
  (S⊲n⊳i)m = if n=m then i else Sm — `at_update` (added 2026-09-17; `HList.at_modify_self/ne` are the list
  version)
- 0*S = nil, (n+1)*S = n*S; S, *S = nat*S — `copies_zero`, `copies_succ`, `mem_star`; **S = *S — `copies_mem_star`
  with `copies_copies` (elementwise; the bunch-level `*` on bunches of strings is not modelled — recorded)
- Indexing composition S(T U) = (S T) U, S nil = nil, S(T;U) = ST;SU, S{A} = {SA} — `sub_sub`, `sub_nil`,
  `sub_append`; `S{A}` — not modelled: a string applied to a set of indices (recorded in
  `string_axioms_copies_update`)
- Order: nil ≤ S < S;i;T, S;i;T < S;j;U for i<j — `nil_le`, `lt_append_item_append`, `append_lt_append_of_lt`
- (S;A;T : S;B;T = A: B) — not modelled: bunch strings (recorded); (i=j = S;i;T = S;j;T) — `append_item_append_inj`
- Intervals x;..x = nil, x;..x+1 = x, (x;..y);(y;..z) = x;..z, ↔(x;..y) = y–x — `interval_self`,
  `interval_succ`, `interval_append_interval`, `len_interval`

## 11.3.6 Lists — `DS.Lists`
- [S]⧧S (type distinction, not statable), [~L] = L, [S];;[T] = [S;T], [S]=[T] = S=T, [S]<[T] = S<T,
  #[S] = ↔S — `pack_contents`/`contents_pack`, `pack_join_pack`, `pack_inj`, `pack_lt_pack`, `length_pack`
- [A]: [B] = A: B (bunches of lists) — `image_pack_subset_image_pack`
- ☐L = 0,..#L — `domain_eq`/`image_domain`; #L = ¢☐L — `length_eq_size_domain` (added 2026-09-17)
- nil→i | L = i, n→i | [S] = [S⊲n⊳i], (n→i | L) m = if n=m then i else L m — `modify_pack`,
  `at_modify_self`, `at_modify_ne`; the string-indexed `nil→i | L` and (S;T)→i | L — not modelled: multi-dimensional
  lists (recorded in `list_axioms`)
- [S] T = ST, S[T] = [ST], [S][T] = [ST], L{A} = {LA}, L[S] = [LS], (L M) N = L (M N) — `pack_comp_pack`,
  `comp_assoc`; `L{A} = {LA}` — `HList.toFn_applyBunch`; `L[S] = [LS]` — `HList.comp_pack` (`FT.FinePoints`, added
  2026-09-17)
- L@nil = L, L@i = L i, L@(S;T) = L@S@T — not modelled: multi-dimensional indexing `@` (recorded in `list_axioms`)

## 11.3.7 Functions — `FT.Functions`, `FT.FinePoints`, `FT.HigherOrder`
- Renaming — `renaming_axiom`; Application — `apply_lam`; Domain ☐⟨v: D· b⟩ = D — `domain_lam`
- Function Composition ☐(g f), (g f) x = g (f x) — `comp_domain`, `comp_apply`
- Selective Union ☐(f|g), (f|g)x, f|f = f, f|(g|h) = (f|g)|h, (g|h) f = g f | h f — `domain_orElse`,
  `apply_orElse`, `orElse_self`, `orElse_assoc`, `orElse_comp` (`FT.HigherOrder`, added 2026-09-17)
- Function Union/Intersection (f, g) — `applyFns_union`/`applyFns_elem` (bunches of functions applied);
  ☐(f,g) = ☐f‘☐g and (f‘g) — not modelled: a bunch of functions applied as a function, and function
  intersection (recorded in `function_on_bunches`)
- Distributive f null = null, f (A,B) = f A, f B, f (§g), f if b then x else y, (if b then f else g) x —
  `applyBunch_null`, `applyBunch_union`, `applyBunch_sols`; the two `if` laws — `apply_ite`, `ite_apply` (added
  2026-09-17)
- Function Inclusion and Equality f: g, f = g, f: A→B — `Incl` (def), `eq_iff`, `incl_arrowB`
- Arrow: f: null→A, A→B : C→D = A::C ∧ B:D, (A,B)→(C‘D) : A→C : (A‘B)→(C,D), (A,B)→C = A→C | B→C = A→C ‘ B→C —
  `incl_arrowB_null`, `arrowB_incl_arrowB`, `arrowB_union_inter_incl`/`arrowB_incl_inter_union`,
  `arrowB_union_eq_orElse`; the `‘` form — not modelled: function intersection (recorded in `function_inclusion`)
- Size #f = ¢☐f — `size_eq`; Extension f = ⟨v: ☐f· f v⟩ — `extension`

## 11.3.8 Quantifiers — `FT.Functions`, `FT.Quantifiers`, `FT.HigherOrder`
- ∀/∃ over null, x, (A,B), (§v: D· b) — `all_null`, `all_elem`, `all_union`, `all_sols`, `not_ex_null`,
  `ex_elem`, `ex_union`, `ex_sols`
- Σ, Π over null, x, (A,B)+(A‘B), (§…) — `sum_null`, `sum_elem`, `sum_union_add_sum_inter`, `sum_sols`,
  `prod_null`, `prod_elem`, `prod_union_mul_prod_inter`, `prod_sols`
- ⇓, ⇑ over null, x, (A,B), (§…) — `inf_null`, `inf_elem`, `inf_union`, `inf_sols`, `sup_null`, `sup_elem`,
  `sup_union`, `sup_sols`
- § over null, x, (A,B), (A‘B), (§…) — `sols_null`, `sols_elem`, `sols_union`, `sols_inter`, `sols_sols`
- Inclusion A: B = ∀x: A· x: B — `subset_iff_all`; Cardinality ¢A = Σ(A→1) — `size_eq_sum_one`
- Change of Variable ×4 — `all_image`, `ex_image`, `sup_image`, `inf_image`
- Identity ∀v· ⊤, ¬∃v· ⊥ — `all_top`, `not_ex_bot`
- Specialize and Generalize ⇓f ≤ f x ≤ ⇑f — `inf_le_apply`, `apply_le_sup`
- Bunch-Element Conversion ×2 — `subset_iff_forall_exists`, `image_subset_image_iff_forall_exists`
- Idempotent ×2 — `all_const`, `ex_const`
- Distributive ×6 (a ∧ ∀, a ∧ ∃, a ∨ ∀, a ∨ ∃, a ⇒ ∀, a ⇒ ∃) — `and_all`, `and_ex`, `or_all`, `or_ex`,
  `imp_all`, `imp_ex`
- Antidistributive ×2 (a ⇐ ∃, a ⇐ ∀) — `ex_imp`, `all_imp`
- Absorption ×4 — `apply_and_ex`, `apply_or_all`, `apply_and_all`, `apply_or_ex`
- Specialization ∀p ⇒ p x, Generalization p x ⇒ ∃p — `all_apply`, `ex_of_apply`
- One-Point ×2 — `all_eq_imp`, `ex_eq_and`
- Duality ¬∀, ¬∃, –⇑, –⇓ — `not_all`, `not_ex`, `neg_sup`, `neg_inf`
- Splitting ×8 — `all_and`, `ex_and`, `all_or`, `ex_or`, `all_imp_all`, `all_imp_ex`, `all_beq_all`,
  `all_beq_ex`
- Commutative ×2, Semicommutative ∃∀ ⇒ ∀∃, ∀x·∃y·p x y = ∃f·∀x·p x (f x) — `forall_forall_comm`,
  `exists_exists_comm`, `exists_forall_imp`, `forall_exists_iff_exists_fun`
- Solution ×7 — `sols_top`, `sols_subset_domain`, `sols_bot`, `sols_subset_sols`, `sols_union_sols`,
  `sols_inter_sols`, `mem_sols`, `all_iff_sols_eq_domain`, `ex_iff_sols_ne_null`
- Domain Change ×4 — `all_of_subset`, `ex_of_subset`, `all_mem_imp`, `ex_mem_and`
- Bounding ×8 — `forall_lt_of_sup_lt`, `forall_lt_of_lt_inf`, `sup_le_iff`, `le_inf_iff`, `inf_le_of_exists`,
  `le_sup_of_exists`, `inf_lt_iff`, `lt_sup_iff`
- Extreme (⇓n: int· n) = –∞, (⇑n: int· n) = ∞ — `inf_int`, `sup_int`; real versions — `inf_real`, `sup_real`
  (`FT.QuantifierDistribution`, added 2026-09-17)
- Connection ×4 — `le_iff_forall_le_imp`, `le_iff_forall_lt_imp`, `le_iff_forall_le_imp'`,
  `le_iff_forall_lt_imp'`
- Distributive (↑↓ with ⇑⇓) — `sup_sup_distrib`, `inf_inf_distrib`, `sup_inf_distrib`, `inf_sup_distrib`; (+ – with ⇑⇓, finite
  n) — `add_sup`, `add_inf`, `sub_sup`, `sub_inf`, `sup_sub`, `inf_sub`; (× with ⇑⇓, finite n) — `mul_sup_of_nonneg`,
  `mul_inf_of_nonneg`, `mul_sup_of_nonpos`, `mul_inf_of_nonpos`; n×Σ (finite D, 0 ≤ n < ∞) — `mul_sum`; (Π)^n (finite D,
  n : ℕ) — `prod_pow` (`FT.QuantifierDistribution`, added 2026-09-17; side conditions recorded in the node)

## 11.3.9 Limits — `FT.Limits` (Section 3.4, added 2026-09-17)
- (⇑m· ⇓n· f(m+n)) ≤ ⇕f ≤ (⇓m· ⇑n· f(m+n)) (Limit Axiom) — `IsLimit` (def: `lowerLimit u ≤ L ∧ L ≤ upperLimit u`,
  the bounds being literally the two quantifications; `lowerLimit_eq_liminf`, `upperLimit_eq_limsup`,
  `exists_isLimit`, `isLimit_iff_of_eq`)
- ∃m·∀n· p(m+n) ⇒ ⇕p ⇒ ∀m·∃n· p(m+n) — `IsPredLimit` (def), `exists_isPredLimit`,
  `exists_forall_add_iff_eventually`, `forall_exists_add_iff_frequently`
- ⇕n· n = ∞ — `isLimit_natSeq_iff`
- The book's ⇕ is underdetermined (an axiom giving bounds); it is modelled as the set of values satisfying the
  axiom rather than as a function. Nothing missing.

## 11.3.10 Specifications and Programs — `PT.Specifications`, `PT.Scope`, `PT.WhileLoop`, `PT.ForLoop`,
`PT.TimeDependence`, `PT.Assertions`, `PT.Subprograms`, `C.Composition`, `LaPToP.TheoryDesign.DataTransformation`,
`LaPToP.Interaction.*`
- ok, x:= e, P. Q, if — `ok` (def), `assign`/`assign_iff`, `seq` (def), `cond`/`cond_eq_or`/`cond_eq_and`
- P||Q with time (∃tP, tQ· … t′ = tP↑tQ) — `parT` (def; `parT_finish`)
- new x: T· P = ∃x, x′: T· P; frame x· P — `newVar` (def, `Scope`), `frame` (def)
- while b do P od = t′≥t ∧ if … (fixed-point equation) and the while proof rule — `WhileRefines`,
  `whileRefines_iff`, `whileRefines_iff_cases` (the loop is modelled by its proof rule; the equation as
  a definition — recorded in `while_loop`)
- for-loop proof rules (F m ⇐ for … with F i ⇐ i: m,..n ∧ (P. F(i+1)), F n ⇐ ok; invariant form) —
  `ForRefines.step`, `ForRefines.exit`, `forRefines_invariant`
- wait until w = t:= t↑w — `waitUntil` (def, `TimeDependence`); assert, ensure — `assert`, `ensure` (defs)
- P. (P value e)=e — `value_spec`/`value_axiom` (`Subprograms`)
- Data transformer ∀new·∃old· D; ∀old· D ⇒ ∃old′· D′ ∧ S — `IsTransformer`, `transform` (defs)
- c?, c, c! e, √c, new x: time→T· S, new c?! T· S — `Channel.input`, `Channel.lastRead`, `Channel.output`,
  `Channel.check`, interactive variable declaration (`InteractiveVariables`), `newChannel` (defs)
- P. ok = P = ok. P, associativity, ∨-distributivity, if-distributivity ×2 — `seq_ok`, `ok_seq`,
  `seq_assoc`, `or_seq_or`, `cond_seq`; `P. if b then Q else R = if P. b then P. Q else P. R` — `det_seq_cond`
  (deterministic `P`) and `seq_cond_eq_or` (general form, the case split on the intermediate state) in
  `PT.AssertionLaws` (added 2026-09-17)
- P||Q = Q||P, associativity, ∨-distributivity, if-distributivity ×2 — `par_comm`, `par_assoc`, `par_or`,
  `par_cond`, `cond_par` (with the product-state relabelling recorded in `concurrent_composition_laws`)
- functional-imperative x:= if b then e else f = if b then x:= e else x:= f — `assign_ite`

## 11.3.11 Substitution — `PT.Specifications`, `C.Composition`
- x:= e. S = (substitute e for x in S) — `assign_seq`
- (x:= e || y:= f). S = (substitute concurrently) — `par_assignF_seq`, `parWith_assignF_seq`

## 11.3.12 Assertions — `PT.AssertionLaws` (added 2026-09-17)
- A ∧ (P. Q) = A∧P. Q — `pre_and_seq`; A ⇒ (P.Q) ⇐ A⇒P. Q — `pre_imp_seq_refines`; (P.Q) ∧ A′ = P. Q∧A′ —
  `seq_and_post`; (P.Q) ⇐ A′ ⇐ P. Q⇐A′ — `seq_post_imp_refines`; P. A∧Q = P∧A′. Q — `seq_pre_and`;
  P. Q ⇐ P∧A′. A⇒Q — `seq_refines_and_post_imp`
- A is a sufficient precondition for P ⇐ S iff A⇒P ⇐ S — `sufficientPre_iff`; sufficient postcondition iff
  A′⇒P ⇐ S — `sufficientPost_iff`

## 11.3.13 Refinement — `PT.Programs`, `C.Composition`
- Refinement by Steps ×4 — `steps_cond`, `steps_seq`, `steps_par`, `steps_trans`
- Refinement by Parts ×4 — `parts_cond`, `parts_seq`, `parts_par`, `parts_and`
- Refinement by Cases — `refines_cond_iff`

## Counts (laws as listed in the tables; "not modelled" = not statable in this typed model, explained in a node)
| table | laws | proved | not modelled |
|---|---|---|---|
| 11.3.0 Generic | 46 | 46 | 0 |
| 11.3.1 Binary | ~110 | ~110 | 0 |
| 11.3.2 Numbers | 61 | 51 | 10 (decimal Counting: notation) |
| 11.3.3 Bunches | 52 | 47 | 5 (bunch-valued division and exponentiation) |
| 11.3.4 Sets | 11 | 10 | 1 (`{A} ⧧ A`: a type distinction) |
| 11.3.5 Strings | 24 | 19 | 5 (strings of bunches, `S{A}`) |
| 11.3.6 Lists | 21 | 16 | 5 (multi-dimensional `@` and `(S;T)→i|L`; `[S] ⧧ S`) |
| 11.3.7 Functions | 26 | 24 | 2 (function bunches as functions, function intersection) |
| 11.3.8 Quantifiers | ~100 | ~100 | 0 |
| 11.3.9 Limits | 3 | 3 | 0 |
| 11.3.10 Specs and Programs | 31 | 31 | 0 |
| 11.3.11 Substitution | 2 | 2 | 0 |
| 11.3.12 Assertions | 8 | 8 | 0 |
| 11.3.13 Refinement | 9 | 9 | 0 |

## Closing remarks
Every law of §11.3 is either a Lean theorem (named above) or is not statable in this typed model for one of
four reasons, each recorded in the Blueprint node of the corresponding theory: (1) *notation* — the decimal
Counting laws; (2) *type distinctions* — `{A} ⧧ A` and `[S] ⧧ S`, which the book states because bunches, sets
and lists share one syntax and Lean separates by type; (3) *bunch-valued operators* — the book's operators
distribute over bunches (`x/0` is the bunch `∞, –∞`, `x^(y+z)` includes `x^y × x^z`, a bunch of functions
applies as a function, a string of bunches is a bunch of strings), whereas here arithmetic, application and
strings are functions of elements and bunches are sets of results (`applyBunch`, `applyFns`, `neg_union`, …
give the bunch equations that *are* statable); (4) *multi-dimensional lists* — `L@(S;T)` and `(S;T)→i|L`,
the lists of lists of Section 2.3, which `HList` does not model. Side conditions added by the model (finite
`n` in the ⇑⇓ arithmetic laws, finite domains for Σ and Π, indices in range) are stated on the theorems and
in the nodes.
Survey complete (2026-09-17).
