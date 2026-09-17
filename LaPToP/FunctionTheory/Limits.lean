import LaPToP.FunctionTheory.Quantifiers
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Limits and reals

This module formalizes Section 3.4 (Limits and Reals) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), pp. 33–34, and with it the
Limits table of the Reference chapter (Section 11.3.9).

"Let `f: nat→rat` so that `f 0; f 1; f 2; ...` is a sequence of rationals. The
limit of the function (limit of the sequence) is expressed as `⇕f`. ... We define
the limit quantifier `⇕` by the following Limit Axiom:
`(⇑m· ⇓n· f (m+n)) ≤ ⇕f ≤ (⇓m· ⇑n· f (m+n))` with all domains being `nat`. This
axiom gives a lower bound (limit inferior) and an upper bound (limit superior)
for `⇕f`. When those bounds are equal, the Limit Axiom tells us `⇕f` exactly.
For example, `⇕n· 1/(n+1) = 0`. For some functions, the Limit Axiom tells us a
little less. For example, `–1 ≤ (⇕n· (–1)^n) ≤ 1`. In general, `⇓f ≤ ⇕f ≤ ⇑f`.
For monotonic (nondecreasing) `f`, `⇕f = ⇑f`. For antimonotonic (nonincreasing)
`f`, `⇕f = ⇓f`. We define the extended real numbers as the limits of all
functions with domain at least `nat` and range at most `rat`. And we define the
reals as the extended reals without `∞` and `–∞`. `x: xreal = ∃f: nat→rat· x = ⇕f`,
`real = xreal–, (∞, –∞)`. ... Let `p: nat→bin` so that `p` is a predicate and
`p 0; p 1; p 2; ...` is a sequence of binary expressions. The limit of predicate
`p` is defined by the axiom `∃m· ∀n· p (m+n) ⇒ ⇕p ⇒ ∀m· ∃n· p (m+n)` with all
domains being `nat`. ... `∃m· ∀i· i≥m ⇒ p i ⇒ ⇕p`, `∃m· ∀i· i≥m ⇒ ¬ p i ⇒ ¬ ⇕p` ...
For example, `¬ ⇕n· 1/(n+1) = 0`. Even though the limit of `1/(n+1)` is `0`, the
limit of `1/(n+1) = 0` is `⊥`. If, for some particular assignment of values to
variables, the sequence never settles on one binary value, then the axiom does
not determine the value of `⇕p` for that assignment of values."

## The model

The book's `⇕f` is *underdetermined*: the Limit Axiom only bounds it. This is
modelled faithfully: a sequence is `u : ℕ → Number` (`Number = EReal`, the
book's `xreal`, so that `⇑` and `⇓` always exist), `lowerLimit u` and
`upperLimit u` are the two bounds of the axiom, and `IsLimit u L` says that `L`
satisfies the axiom. The bounds are Mathlib's `liminf`/`limsup` along `atTop`
(`lowerLimit_eq_liminf`, `upperLimit_eq_limsup`), so a limit value always
exists, and is unique exactly when the two bounds agree. Likewise `⇕p` for a
predicate is any binary value between "eventually `p`" and "frequently `p`"
(`IsPredLimit`). The examples are proved in this reading: every limit value of
`1/(n+1)` is `0`; the limit values of `(–1)^n` are exactly the elements of
`[–1, 1]` (so both `–1` and `1` are limit values — "the Limit Axiom tells us a
little less"); `⇕n· n = ∞`; monotone and antitone sequences have their `⇑`,
resp. `⇓`, as unique limit value. Every extended real is a limit value of a
rational sequence, and the reals are the extended reals other than `±∞`; and
`⇕n· (1+1/n)^n` is `e` (`isLimit_eSeq_iff`).
-/

namespace LaPToP.FunctionTheory

open LaPToP.BasicTheories

namespace Limits

open Filter Topology

/-- A sequence of (extended) numbers, the book's `f: nat→rat` (with range at most `xreal`). -/
abbrev Seq := ℕ → Number

/-- The lower bound of the Limit Axiom, `⇑m· ⇓n· f (m+n)` (the limit inferior). -/
noncomputable def lowerLimit (u : Seq) : Number := ⨆ m : ℕ, ⨅ n : ℕ, u (m + n)

/-- The upper bound of the Limit Axiom, `⇓m· ⇑n· f (m+n)` (the limit superior). -/
noncomputable def upperLimit (u : Seq) : Number := ⨅ m : ℕ, ⨆ n : ℕ, u (m + n)

/-- The Limit Axiom: `L` is a value of `⇕f` iff `(⇑m· ⇓n· f (m+n)) ≤ L ≤ (⇓m· ⇑n· f (m+n))`. -/
def IsLimit (u : Seq) (L : Number) : Prop := lowerLimit u ≤ L ∧ L ≤ upperLimit u

variable (u : Seq)

/-- The lower bound is the limit inferior. -/
theorem lowerLimit_eq_liminf : lowerLimit u = liminf u atTop := by
  rw [liminf_eq_iSup_iInf_of_nat']
  exact iSup_congr fun m => iInf_congr fun n => by rw [add_comm]

/-- The upper bound is the limit superior. -/
theorem upperLimit_eq_limsup : upperLimit u = limsup u atTop := by
  rw [limsup_eq_iInf_iSup_of_nat']
  exact iInf_congr fun m => iSup_congr fun n => by rw [add_comm]

/-- The two bounds are consistent: the limit inferior is at most the limit superior. -/
theorem lowerLimit_le_upperLimit : lowerLimit u ≤ upperLimit u := by
  rw [lowerLimit_eq_liminf, upperLimit_eq_limsup]
  exact liminf_le_limsup

/-- A value of `⇕f` always exists (the limit inferior is one). -/
theorem exists_isLimit : ∃ L, IsLimit u L := ⟨lowerLimit u, le_rfl, lowerLimit_le_upperLimit u⟩

/-- "When those bounds are equal, the Limit Axiom tells us `⇕f` exactly." -/
theorem isLimit_iff_of_eq (h : lowerLimit u = upperLimit u) (L : Number) : IsLimit u L ↔ L = lowerLimit u :=
  ⟨fun ⟨h₁, h₂⟩ => le_antisymm (h ▸ h₂) h₁, fun hL => hL ▸ ⟨le_rfl, h ▸ le_rfl⟩⟩

/-- A convergent sequence has its limit as unique value of `⇕f`. -/
theorem isLimit_iff_of_tendsto {a : Number} (h : Tendsto u atTop (𝓝 a)) (L : Number) : IsLimit u L ↔ L = a := by
  have h₁ : lowerLimit u = a := by rw [lowerLimit_eq_liminf]; exact h.liminf_eq
  have h₂ : upperLimit u = a := by rw [upperLimit_eq_limsup]; exact h.limsup_eq
  rw [isLimit_iff_of_eq u (h₁.trans h₂.symm), h₁]

/-- "In general, `⇓f ≤ ⇕f ≤ ⇑f`." -/
theorem inf_le_isLimit_le_sup {L : Number} (h : IsLimit u L) : (⨅ n, u n) ≤ L ∧ L ≤ ⨆ n, u n :=
  ⟨le_trans (by rw [lowerLimit_eq_liminf]; exact iInf_le_liminf) h.1,
   le_trans h.2 (by rw [upperLimit_eq_limsup]; exact limsup_le_iSup)⟩

/-- The book's `⇓f`, `⇑f` for a sequence read as the function `⟨n: nat· f n⟩` of the quantifier
theory: `⇑⟨n: nat· f n⟩ = ⨆ n, f n`. -/
theorem sup_toFn : Fn.sup (Fn.lam Bunch.nat fun z : ℤ => u z.toNat) = ⨆ n, u n := by
  rw [Fn.sup, Fn.values_lam]
  have : (fun z : ℤ => u z.toNat) '' Bunch.nat = Set.range u := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩; exact ⟨z.toNat, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨n, by simp [Bunch.nat], by simp⟩
  rw [this, sSup_range]

/-- `⇓⟨n: nat· f n⟩ = ⨅ n, f n`. -/
theorem inf_toFn : Fn.inf (Fn.lam Bunch.nat fun z : ℤ => u z.toNat) = ⨅ n, u n := by
  rw [Fn.inf, Fn.values_lam]
  have : (fun z : ℤ => u z.toNat) '' Bunch.nat = Set.range u := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩; exact ⟨z.toNat, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨n, by simp [Bunch.nat], by simp⟩
  rw [this, sInf_range]

/-! ### Monotone and antitone sequences -/

/-- "For monotonic (nondecreasing) `f`, `⇕f = ⇑f`." -/
theorem isLimit_iff_of_monotone (hu : Monotone u) (L : Number) : IsLimit u L ↔ L = ⨆ n, u n := by
  have hlow : lowerLimit u = ⨆ n, u n := by
    unfold lowerLimit
    refine iSup_congr fun m => le_antisymm (iInf_le_of_le 0 (by simp)) (le_iInf fun n => hu (Nat.le_add_right m n))
  have hup : upperLimit u = ⨆ n, u n := by
    unfold upperLimit
    refine le_antisymm (iInf_le_of_le 0 (by simp)) (le_iInf fun m => iSup_le fun n => ?_)
    exact le_trans (hu (Nat.le_add_left n m)) (le_iSup (fun k => u (m + k)) n)
  rw [isLimit_iff_of_eq u (hlow.trans hup.symm), hlow]

/-- "For antimonotonic (nonincreasing) `f`, `⇕f = ⇓f`." -/
theorem isLimit_iff_of_antitone (hu : Antitone u) (L : Number) : IsLimit u L ↔ L = ⨅ n, u n := by
  have hlow : lowerLimit u = ⨅ n, u n := by
    unfold lowerLimit
    refine le_antisymm (iSup_le fun m => le_iInf fun n => ?_) (le_iSup_of_le 0 (by simp))
    exact le_trans (iInf_le (fun k => u (m + k)) n) (hu (Nat.le_add_left n m))
  have hup : upperLimit u = ⨅ n, u n := by
    unfold upperLimit
    refine iInf_congr fun m => le_antisymm (iSup_le fun n => hu (Nat.le_add_right m n)) (le_iSup_of_le 0 (by simp))
  rw [isLimit_iff_of_eq u (hlow.trans hup.symm), hlow]

/-! ### Examples -/

/-- `⟨n: nat· 1/(n+1)⟩`. -/
noncomputable def invSucc : Seq := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : Number)

/-- `⇕n· 1/(n+1) = 0`: every value of the limit is `0`. -/
theorem isLimit_invSucc_iff (L : Number) : IsLimit invSucc L ↔ L = 0 := by
  have h : Tendsto invSucc atTop (𝓝 ((0 : ℝ) : Number)) :=
    EReal.tendsto_coe.2 tendsto_one_div_add_atTop_nhds_zero_nat
  rw [isLimit_iff_of_tendsto invSucc h, EReal.coe_zero]

/-- `⟨n: nat· (1 + 1/n)^n⟩`, "the base of the natural logarithms, often denoted `e`". -/
noncomputable def eSeq : Seq := fun n => (((1 + 1 / (n : ℝ)) ^ n : ℝ) : Number)

/-- `⇕n· (1 + 1/n)^n = e`: every value of the limit is `e` (Mathlib's `Real.exp 1`). -/
theorem isLimit_eSeq_iff (L : Number) : IsLimit eSeq L ↔ L = ((Real.exp 1 : ℝ) : Number) := by
  have h : Tendsto eSeq atTop (𝓝 ((Real.exp 1 : ℝ) : Number)) := by
    refine EReal.tendsto_coe.2 ?_
    have := Real.tendsto_one_add_div_pow_exp 1
    simpa [one_div] using this
  exact isLimit_iff_of_tendsto eSeq h L

/-- `⟨n: nat· (–1)^n⟩`. -/
noncomputable def altSign : Seq := fun n => (((-1 : ℝ) ^ n : ℝ) : Number)

theorem altSign_even {n : ℕ} (h : Even n) : altSign n = 1 := by simp [altSign, h.neg_one_pow]
theorem altSign_odd {n : ℕ} (h : Odd n) : altSign n = -1 := by simp [altSign, h.neg_one_pow]

theorem neg_one_le_one' : (-1 : Number) ≤ 1 := by
  have : ((-1 : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) := EReal.coe_le_coe_iff.2 (by norm_num)
  simpa using this

theorem altSign_bounds (n : ℕ) : -1 ≤ altSign n ∧ altSign n ≤ 1 := by
  rcases Nat.even_or_odd n with h | h
  · rw [altSign_even h]; exact ⟨neg_one_le_one', le_rfl⟩
  · rw [altSign_odd h]; exact ⟨le_rfl, neg_one_le_one'⟩

/-- The lower bound for `(–1)^n` is `–1`: every tail contains an odd index. -/
theorem lowerLimit_altSign : lowerLimit altSign = -1 := by
  unfold lowerLimit
  refine le_antisymm (iSup_le fun m => ?_) (le_iSup_of_le 0 (le_iInf fun n => (altSign_bounds _).1))
  have hodd : Odd (m + (m + 1)) := ⟨m, by ring⟩
  exact iInf_le_of_le (m + 1) (by rw [altSign_odd hodd])

/-- The upper bound for `(–1)^n` is `1`: every tail contains an even index. -/
theorem upperLimit_altSign : upperLimit altSign = 1 := by
  unfold upperLimit
  refine le_antisymm (iInf_le_of_le 0 (iSup_le fun n => (altSign_bounds _).2)) (le_iInf fun m => ?_)
  have heven : Even (m + m) := ⟨m, rfl⟩
  exact le_iSup_of_le m (by rw [altSign_even heven])

/-- "`–1 ≤ (⇕n· (–1)^n) ≤ 1`" — and nothing more: the values of the limit are exactly the numbers in
`[–1, 1]`, so both `–1` and `1` are values ("the Limit Axiom tells us a little less"). -/
theorem isLimit_altSign_iff (L : Number) : IsLimit altSign L ↔ -1 ≤ L ∧ L ≤ 1 := by
  rw [IsLimit, lowerLimit_altSign, upperLimit_altSign]

theorem isLimit_altSign_neg_one : IsLimit altSign (-1) := (isLimit_altSign_iff _).2 ⟨le_rfl, neg_one_le_one'⟩
theorem isLimit_altSign_one : IsLimit altSign 1 := (isLimit_altSign_iff _).2 ⟨neg_one_le_one', le_rfl⟩

/-- `⟨n: nat· n⟩`. -/
noncomputable def natSeq : Seq := fun n => ((n : ℝ) : Number)

/-- `⇕n· n = ∞` (Reference §11.3.9). -/
theorem isLimit_natSeq_iff (L : Number) : IsLimit natSeq L ↔ L = ⊤ := by
  have h : Tendsto natSeq atTop (𝓝 (⊤ : Number)) :=
    EReal.tendsto_coe_nhds_top_iff.2 tendsto_natCast_atTop_atTop
  exact isLimit_iff_of_tendsto natSeq h L

/-! ### Limits of predicates -/

/-- The limit axiom for a predicate `p: nat→bin`: `∃m· ∀n· p (m+n) ⇒ ⇕p ⇒ ∀m· ∃n· p (m+n)`; a binary
`b` is a value of `⇕p` iff it lies between the two bounds. -/
def IsPredLimit (p : ℕ → Prop) (b : Prop) : Prop := ((∃ m, ∀ n, p (m + n)) → b) ∧ (b → ∀ m, ∃ n, p (m + n))

variable (p : ℕ → Prop)

/-- The lower bound is "eventually `p`", `∃m· ∀i· i≥m ⇒ p i`. -/
theorem exists_forall_add_iff_eventually : (∃ m, ∀ n, p (m + n)) ↔ ∀ᶠ i in atTop, p i := by
  rw [eventually_atTop]
  constructor
  · rintro ⟨m, h⟩
    exact ⟨m, fun i hi => by obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi; exact h n⟩
  · rintro ⟨m, h⟩
    exact ⟨m, fun n => h (m + n) (Nat.le_add_right m n)⟩

/-- The upper bound is "frequently `p`", `∀m· ∃i· i≥m ∧ p i`. -/
theorem forall_exists_add_iff_frequently : (∀ m, ∃ n, p (m + n)) ↔ ∃ᶠ i in atTop, p i := by
  rw [frequently_atTop]
  constructor
  · intro h m
    obtain ⟨n, hn⟩ := h m
    exact ⟨m + n, Nat.le_add_right m n, hn⟩
  · intro h m
    obtain ⟨i, hi, hp⟩ := h m
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi
    exact ⟨n, hp⟩

/-- The two bounds are consistent: a value of `⇕p` always exists. -/
theorem exists_isPredLimit : ∃ b, IsPredLimit p b :=
  ⟨∃ m, ∀ n, p (m + n), fun h => h, fun h => by
    rw [exists_forall_add_iff_eventually] at h
    exact (forall_exists_add_iff_frequently p).2 h.frequently⟩

/-- "`∃m· ∀i· i≥m ⇒ p i ⇒ ⇕p`". -/
theorem isPredLimit_of_eventually {b : Prop} (hb : IsPredLimit p b) (h : ∃ m, ∀ i, i ≥ m → p i) : b :=
  hb.1 ((exists_forall_add_iff_eventually p).2 (eventually_atTop.2 h))

/-- "`∃m· ∀i· i≥m ⇒ ¬ p i ⇒ ¬ ⇕p`". -/
theorem not_isPredLimit_of_eventually_not {b : Prop} (hb : IsPredLimit p b) (h : ∃ m, ∀ i, i ≥ m → ¬ p i) : ¬ b :=
  fun hbb => by
    have hfreq := (forall_exists_add_iff_frequently p).1 (hb.2 hbb)
    exact (not_frequently.2 (eventually_atTop.2 h)) hfreq

/-- "`¬ ⇕n· 1/(n+1) = 0`. Even though the limit of `1/(n+1)` is `0`, the limit of `1/(n+1) = 0` is
`⊥`": `1/(n+1) = 0` never holds, so every value of its limit is false. -/
theorem not_isPredLimit_invSucc_eq_zero {b : Prop} (hb : IsPredLimit (fun n => invSucc n = 0) b) : ¬ b :=
  not_isPredLimit_of_eventually_not _ hb ⟨0, fun n _ => by
    simp only [invSucc, EReal.coe_eq_zero]
    positivity⟩

/-! ### Extended reals and reals as limits -/

/-- A rational sequence converging to the real `r`: `⌊r(n+1)⌋/(n+1)`. -/
noncomputable def ratApprox (r : ℝ) (n : ℕ) : ℚ := (⌊r * ((n : ℝ) + 1)⌋ : ℚ) / ((n : ℚ) + 1)

theorem ratApprox_tendsto (r : ℝ) : Tendsto (fun n => ((ratApprox r n : ℚ) : ℝ)) atTop (𝓝 r) := by
  have hlo : Tendsto (fun n : ℕ => r - 1 / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    have := tendsto_const_nhds (x := r) |>.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [sub_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun n => ?_) (fun n => ?_)
  · have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have := Int.lt_floor_add_one (r * ((n : ℝ) + 1))
    simp only [ratApprox]
    push_cast
    rw [le_div_iff₀ hpos, sub_mul, div_mul_cancel₀ (1 : ℝ) hpos.ne']
    linarith
  · have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have := Int.floor_le (r * ((n : ℝ) + 1))
    simp only [ratApprox]
    push_cast
    rw [div_le_iff₀ hpos]
    linarith

/-- "`x: xreal = ∃f: nat→rat· x = ⇕f`": every extended real is a value of the limit of a rational
sequence (`n` for `∞`, `–n` for `–∞`, `⌊x(n+1)⌋/(n+1)` for a real `x`). -/
theorem exists_rat_seq_isLimit (x : Number) : ∃ f : ℕ → ℚ, IsLimit (fun n => ((f n : ℝ) : Number)) x := by
  induction x using EReal.rec with
  | bot =>
    refine ⟨fun n => -(n : ℚ), ?_⟩
    have h : Tendsto (fun n : ℕ => (((-(n : ℚ) : ℚ) : ℝ) : Number)) atTop (𝓝 ⊥) := by
      refine EReal.tendsto_coe_nhds_bot_iff.2 ?_
      simp only [Rat.cast_neg, Rat.cast_natCast]
      exact tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    exact (isLimit_iff_of_tendsto _ h _).2 rfl
  | coe r =>
    refine ⟨ratApprox r, ?_⟩
    have h : Tendsto (fun n => (((ratApprox r n : ℚ) : ℝ) : Number)) atTop (𝓝 (r : Number)) :=
      EReal.tendsto_coe.2 (ratApprox_tendsto r)
    exact (isLimit_iff_of_tendsto _ h _).2 rfl
  | top =>
    refine ⟨fun n => (n : ℚ), ?_⟩
    have h : Tendsto (fun n : ℕ => (((n : ℚ) : ℝ) : Number)) atTop (𝓝 ⊤) := by
      refine EReal.tendsto_coe_nhds_top_iff.2 ?_
      simp only [Rat.cast_natCast]
      exact tendsto_natCast_atTop_atTop
    exact (isLimit_iff_of_tendsto _ h _).2 rfl

/-- "`real = xreal–, (∞, –∞)`": the extended reals other than `∞` and `–∞` are exactly the reals. -/
theorem real_eq_xreal_remove : {x : Number | x ≠ ⊤ ∧ x ≠ ⊥} = Set.range ((↑) : ℝ → Number) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨ht, hb⟩
    induction x using EReal.rec with
    | bot => exact absurd rfl hb
    | coe r => exact ⟨r, rfl⟩
    | top => exact absurd rfl ht
  · rintro ⟨r, rfl⟩
    exact ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩

end Limits

end LaPToP.FunctionTheory
