import LaPToP.ProgramTheory.RandomNumbers
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases

/-!
# Blackjack (Exercise 344)

This module formalizes the blackjack example of Subsection 5.7.0 (Random
Number Generators) of Eric Hehner's *A Practical Theory of Programming*
(aPToP), pp. 88–89.

"Exercise 344 is a simplified version of blackjack. You are dealt a card from
a deck; its value is in the range `1` through `13` inclusive. You may stop with
just one card, or have a second card if you want. Your object is to get a
total as near as possible to `14`, but not over `14`. Your strategy is to take a
second card if the first is under `7`. Assuming each card value has equal
probability (actually, the second card drawn has a diminished probability of
having the same value as the first card drawn, but let's ignore that
complication), we represent a card as `(rand 13) + 1`. In one variable `x`, the
game is `x:= (rand 13) + 1. if x<7 then x:= x + (rand 13) + 1 else ok`
`= (x′: (0,..13)+1)/13. if x<7 then (x′: x+(0,..13)+1)/13 else x′=x`
`= Σx′′· (x′′: 1,..14)/13 × ((x′′<7)×(x′: x′′+1,..x′′+14)/13 + (x′′≥7)×(x′=x′′))`
`= ((2≤x′<7)×(x′–1) + (7≤x′<14)×19 + (14≤x′<20)×(20–x′)) / 169`. That is the
distribution of `x′` if we use the “under 7” strategy. ... To compare two
strategies, we play both of them at once. Player `x` will play “under `n`” and
player `y` will play “under `n+1`” using exactly the same cards `c` and `d` ...
Here is the new game, followed by the assertion that `x` wins:
`c:= (rand 13) + 1. d:= (rand 13) + 1. if c < n then x:= c+d else x:= c.
if c < n+1 then y:= c+d else y:= c. y′<x′≤14 ∨ x′≤14<y′` ...
`= (c′: (0,..13)+1 ∧ d′: (0,..13)+1 ∧ x′=x ∧ y′=y) / 169. c=n ∧ d>14–n`
`= Σd: 1,..14· (d>14–n)/169 = (n–1) / 169`. The probability that `x` wins is
`(n–1) / 169`. By similar calculations we can find that the probability that
`y` wins is `(14–n) / 169`, and the probability of a tie is `12/13`. For `n<8`,
“under `n+1`” beats “under `n`”. For `n≥8`, “under `n`” beats “under `n+1`”. So
“under 8” beats both “under 7” and “under 9”."

## The model

A dealt card `x:= (rand 13) + 1` is the uniform distribution on `1,..14`
(`deal`, equal to `randAssign 13` of the previous module), and the second card
`x:= x + (rand 13) + 1` is `secondCard`. The "under 7" game is the
probabilistic program `game7` and its distribution is computed exactly as the
book states it (the "several omitted steps" are a finite sum over the `13`
first cards and a case analysis on `x′`). For the two-player game, the book's
own last lines reduce the winning assertion to `c=n ∧ d>14–n` and count over
the `169` equiprobable card pairs; the formalization proves that reduction
(`xWins_iff`, `yWins_iff`, `tie_iff`) and the three counts directly, without
building the four-variable probabilistic program (the Functional-Imperative
and Substitution Law steps that only rewrite the program are not repeated).
The equal-probability idealization is the book's.
-/

namespace LaPToP.ProgramTheory

namespace Probabilistic

open scoped Classical
open Finset

/-! ### Cards -/

/-- The bunch `(0,..13)+1 = 1,..14` of card values. -/
noncomputable def card : Finset ℤ := Finset.Ico 1 14

theorem card_card : card.card = 13 := by simp [card]

/-- A uniform distribution on `a,..a+n`. -/
theorem hasSum_uniform (a : ℤ) {n : ℕ} (hn : 0 < n) :
    HasSum (fun x' : ℤ => ind (a ≤ x' ∧ x' < a + n) / n) 1 := by
  have h : ∀ x' ∉ Finset.Ico a (a + n), ind (a ≤ x' ∧ x' < a + n) / (n : ℝ) = 0 := fun x' hx' => by
    rw [Finset.mem_Ico] at hx'
    simp [ind, hx']
  have hsum : ∑ x' ∈ Finset.Ico a (a + n), ind (a ≤ x' ∧ x' < a + n) / (n : ℝ) = 1 := by
    have this : ∀ x' ∈ Finset.Ico a (a + n), ind (a ≤ x' ∧ x' < a + n) / (n : ℝ) = 1 / n := fun x' hx' => by
      rw [Finset.mem_Ico] at hx'
      rw [ind_true hx']
    rw [Finset.sum_congr rfl this, Finset.sum_const, Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast,
      nsmul_eq_mul]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  exact hsum ▸ hasSum_sum_of_ne_finset_zero h

theorem prob_uniform (a x' : ℤ) {n : ℕ} (hn : 0 < n) : Prob (ind (a ≤ x' ∧ x' < a + n) / n) := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold ind Prob
  split_ifs
  · exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact h1⟩
  · simp

/-- `x:= (rand 13) + 1 = (x′: (0,..13)+1)/13`. -/
noncomputable def deal : PSpec ℤ := fun _ x' => ind (1 ≤ x' ∧ x' < 14) / 13

/-- `x:= x + (rand 13) + 1 = (x′: x+(0,..13)+1)/13`. -/
noncomputable def secondCard : PSpec ℤ := fun x x' => ind (x + 1 ≤ x' ∧ x' < x + 14) / 13

/-- The summed indicators of `x′ = e + r` over `r: 0,..n` form the interval indicator. -/
theorem sum_ind_eq_interval (e x' : ℤ) (n : ℤ) :
    ∑ r ∈ Finset.Ico 0 n, ind (x' = e + r) = ind (e ≤ x' ∧ x' < e + n) := by
  by_cases h : e ≤ x' ∧ x' < e + n
  · rw [ind_true h]
    rw [Finset.sum_eq_single_of_mem (x' - e) (by rw [Finset.mem_Ico]; omega)
      (fun r _ hr => ind_false fun heq => hr (by omega))]
    exact ind_true (by ring)
  · rw [ind_false h]
    exact Finset.sum_eq_zero fun r hr => ind_false fun heq => h (by rw [Finset.mem_Ico] at hr; omega)

/-- `deal` is `x:= (rand 13) + 1` with `rand` replaced as in Subsection 5.7.0. -/
theorem randAssign_deal : randAssign 13 (fun _ r => r + 1) = deal := by
  funext x x'
  simp only [randAssign, deal]
  rw [show (fun r : ℤ => ind (x' = r + 1)) = fun r => ind (x' = 1 + r) by funext r; rw [add_comm],
    sum_ind_eq_interval]
  norm_num

/-- `secondCard` is `x:= x + (rand 13) + 1`. -/
theorem randAssign_secondCard : randAssign 13 (fun x r => x + r + 1) = secondCard := by
  funext x x'
  simp only [randAssign, secondCard]
  rw [show (fun r : ℤ => ind (x' = x + r + 1)) = fun r => ind (x' = (x + 1) + r) by
    funext r; congr 1; apply propext; constructor <;> intro h <;> omega, sum_ind_eq_interval]
  norm_num
  congr 2
  apply propext
  omega

theorem isDistribution_deal : IsDistribution deal := fun x => by
  have e : (fun x' : ℤ => ind (1 ≤ x' ∧ x' < 1 + ((13 : ℕ) : ℤ)) / ((13 : ℕ) : ℝ)) = deal x := by
    funext x'; simp [deal]
  refine ⟨fun x' => ?_, ?_⟩
  · have h := prob_uniform 1 x' (n := 13) (by norm_num)
    rw [← e]; exact h
  · have h := hasSum_uniform 1 (n := 13) (by norm_num)
    rw [e] at h; exact h

theorem isDistribution_secondCard : IsDistribution secondCard := fun x => by
  have e : (fun x' : ℤ => ind (x + 1 ≤ x' ∧ x' < x + 1 + ((13 : ℕ) : ℤ)) / ((13 : ℕ) : ℝ)) = secondCard x := by
    funext x'
    simp only [secondCard, Nat.cast_ofNat]
    congr 2
    apply propext
    omega
  refine ⟨fun x' => ?_, ?_⟩
  · have h := prob_uniform (x + 1) x' (n := 13) (by norm_num)
    rw [← e]; exact h
  · have h := hasSum_uniform (x + 1) (n := 13) (by norm_num)
    rw [e] at h; exact h

theorem support_deal (x : ℤ) : (Function.support (deal x)).Finite := by
  apply (Set.toFinite (card : Set ℤ)).subset
  intro x' hx'
  rw [Function.mem_support] at hx'
  by_contra h
  simp only [card, Finset.coe_Ico, Set.mem_Ico, not_and, not_lt] at h
  exact hx' (by simp [deal, ind]; omega)

/-! ### The "under 7" game -/

/-- `if x<7 then x:= x + (rand 13) + 1 else ok`. -/
noncomputable def under7Body : PSpec ℤ := pcond (fun x => ind (x < 7)) secondCard pok

/-- `x:= (rand 13) + 1. if x<7 then x:= x + (rand 13) + 1 else ok`. -/
noncomputable def game7 : PSpec ℤ := pseq deal under7Body

theorem isDistribution_game7 : IsDistribution game7 :=
  isDistribution_pseq isDistribution_deal support_deal
    (isDistribution_pcond (fun _ => prob_ind _) isDistribution_secondCard (isDistribution_ofSpec_det id))

/-- The book's distribution of `x′` under the "under 7" strategy. -/
noncomputable def dist7 (x' : ℤ) : ℝ :=
  (ind (2 ≤ x' ∧ x' < 7) * (x' - 1) + ind (7 ≤ x' ∧ x' < 14) * 19 + ind (14 ≤ x' ∧ x' < 20) * (20 - x')) / 169

theorem Ico_one_fourteen : Finset.Ico (1 : ℤ) 14 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
  ext; simp; omega

/-- `Σx′′· (x′′: 1,..14)/13 × ((x′′<7)×(x′: x′′+1,..x′′+14)/13 + (x′′≥7)×(x′=x′′))`. -/
theorem game7_eq_sum (x x' : ℤ) :
    game7 x x' = ∑ x'' ∈ card, (1 / 13 : ℝ) * (ind (x'' < 7) * (ind (x'' + 1 ≤ x' ∧ x' < x'' + 14) / 13)
      + (1 - ind (x'' < 7)) * ind (x' = x'')) := by
  have hfin := support_deal x
  rw [game7, pseq_eq_sum hfin]
  have hF : hfin.toFinset ⊆ card := by
    intro x'' hx''
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hx''
    by_contra h
    simp only [card, Finset.mem_Ico, not_and, not_lt] at h
    exact hx'' (by simp [deal, ind]; omega)
  rw [Finset.sum_subset hF fun x'' _ hx'' => by
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx''; simp [hx'']]
  refine Finset.sum_congr rfl fun x'' hx'' => ?_
  simp only [card, Finset.mem_Ico] at hx''
  simp only [deal, under7Body, pcond, secondCard, pok]
  rw [ind_true hx'']

/-- "`= ((2≤x′<7)×(x′–1) + (7≤x′<14)×19 + (14≤x′<20)×(20–x′)) / 169`. That is the distribution of
`x′` if we use the “under 7” strategy." -/
theorem game7_eq (x x' : ℤ) : game7 x x' = dist7 x' := by
  rw [game7_eq_sum]
  by_cases hx : 2 ≤ x' ∧ x' < 20
  · obtain ⟨h1, h2⟩ := hx
    rw [card, Ico_one_fourteen]
    interval_cases x' <;> norm_num [dist7, ind, Finset.sum_insert]
  · have hz : ∀ x'' ∈ card, (1 / 13 : ℝ) * (ind (x'' < 7) * (ind (x'' + 1 ≤ x' ∧ x' < x'' + 14) / 13)
        + (1 - ind (x'' < 7)) * ind (x' = x'')) = 0 := fun x'' hx'' => by
      simp only [card, Finset.mem_Ico] at hx''
      unfold ind
      split_ifs <;> first | (exfalso; omega) | norm_num
    rw [Finset.sum_eq_zero hz]
    unfold dist7 ind
    split_ifs <;> first | (exfalso; omega) | norm_num

/-! ### Two players: "under n" against "under n+1" -/

variable (n : ℤ)

/-- Player `x`'s total: `if c < n then c+d else c`. -/
def xHand (c d : ℤ) : ℤ := if c < n then c + d else c
/-- Player `y`'s total: `if c < n+1 then c+d else c`. -/
def yHand (c d : ℤ) : ℤ := if c < n + 1 then c + d else c

/-- "`x` wins": `y′<x′≤14 ∨ x′≤14<y′`. -/
def xWins (c d : ℤ) : Prop := (yHand n c d < xHand n c d ∧ xHand n c d ≤ 14) ∨ (xHand n c d ≤ 14 ∧ 14 < yHand n c d)
/-- "`y` wins": `x′<y′≤14 ∨ y′≤14<x′`. -/
def yWins (c d : ℤ) : Prop := (xHand n c d < yHand n c d ∧ yHand n c d ≤ 14) ∨ (yHand n c d ≤ 14 ∧ 14 < xHand n c d)

/-- The book's reduction of the winning assertion: `… = c=n ∧ d>14–n`. -/
theorem xWins_iff (hn : 1 ≤ n ∧ n ≤ 13) {c d : ℤ} (hc : c ∈ card) (hd : d ∈ card) :
    xWins n c d ↔ c = n ∧ 14 - n < d := by
  simp only [card, Finset.mem_Ico] at hc hd
  unfold xWins xHand yHand
  split_ifs <;> omega

/-- "By similar calculations": `y` wins iff `c=n ∧ d≤14–n`. -/
theorem yWins_iff (_hn : 1 ≤ n ∧ n ≤ 13) {c d : ℤ} (hc : c ∈ card) (hd : d ∈ card) :
    yWins n c d ↔ c = n ∧ d ≤ 14 - n := by
  simp only [card, Finset.mem_Ico] at hc hd
  unfold yWins xHand yHand
  split_ifs <;> omega

/-- A tie: neither player wins. -/
def tie (c d : ℤ) : Prop := ¬ xWins n c d ∧ ¬ yWins n c d

/-- A tie iff the first card is not `n` (the two strategies then agree). -/
theorem tie_iff (hn : 1 ≤ n ∧ n ≤ 13) {c d : ℤ} (hc : c ∈ card) (hd : d ∈ card) :
    tie n c d ↔ c ≠ n := by
  rw [tie, xWins_iff n hn hc hd, yWins_iff n hn hc hd]
  constructor
  · rintro ⟨h1, h2⟩ rfl
    by_cases hd' : 14 - c < d
    · exact h1 ⟨rfl, hd'⟩
    · exact h2 ⟨rfl, by omega⟩
  · intro h
    exact ⟨fun h' => h h'.1, fun h' => h h'.1⟩

/-- A sum of indicators over a finite set counts the elements satisfying the property. -/
theorem sum_ind {α : Type} (s : Finset α) (P : α → Prop) :
    ∑ a ∈ s, ind (P a) = ((s.filter P).card : ℝ) := by
  simp [ind, Finset.sum_boole]

/-- The probability that `x` wins: `(Σc, d: 1,..14· (x wins)) / 169`. -/
noncomputable def probXWins : ℝ := (∑ p ∈ card ×ˢ card, ind (xWins n p.1 p.2)) / 169
/-- The probability that `y` wins. -/
noncomputable def probYWins : ℝ := (∑ p ∈ card ×ˢ card, ind (yWins n p.1 p.2)) / 169
/-- The probability of a tie. -/
noncomputable def probTie : ℝ := (∑ p ∈ card ×ˢ card, ind (tie n p.1 p.2)) / 169

/-- "The probability that `x` wins is `(n–1) / 169`." -/
theorem probXWins_eq (hn : 1 ≤ n ∧ n ≤ 13) : probXWins n = (n - 1) / 169 := by
  unfold probXWins
  rw [sum_ind]
  have hf : (card ×ˢ card).filter (fun p => xWins n p.1 p.2) = {n} ×ˢ Finset.Ico (15 - n) 14 := by
    ext ⟨c, d⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hc, hd⟩, hw⟩
      rw [xWins_iff n hn hc hd] at hw
      simp only [card, Finset.mem_Ico] at hc hd
      omega
    · rintro ⟨rfl, hd⟩
      have hc : c ∈ card := by simp only [card, Finset.mem_Ico]; omega
      have hd' : d ∈ card := by simp only [card, Finset.mem_Ico]; omega
      exact ⟨⟨hc, hd'⟩, (xWins_iff c hn hc hd').2 ⟨rfl, by omega⟩⟩
  rw [hf, Finset.card_product, Finset.card_singleton, Int.card_Ico, one_mul]
  have : (((14 - (15 - n)).toNat : ℕ) : ℝ) = n - 1 := by
    have h : ((14 - (15 - n)).toNat : ℤ) = n - 1 := by rw [Int.toNat_of_nonneg (by omega)]; ring
    exact_mod_cast h
  rw [this]

/-- "The probability that `y` wins is `(14–n) / 169`." -/
theorem probYWins_eq (hn : 1 ≤ n ∧ n ≤ 13) : probYWins n = (14 - n) / 169 := by
  unfold probYWins
  rw [sum_ind]
  have hf : (card ×ˢ card).filter (fun p => yWins n p.1 p.2) = {n} ×ˢ Finset.Ico 1 (15 - n) := by
    ext ⟨c, d⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hc, hd⟩, hw⟩
      rw [yWins_iff n hn hc hd] at hw
      simp only [card, Finset.mem_Ico] at hc hd
      omega
    · rintro ⟨rfl, hd⟩
      have hc : c ∈ card := by simp only [card, Finset.mem_Ico]; omega
      have hd' : d ∈ card := by simp only [card, Finset.mem_Ico]; omega
      exact ⟨⟨hc, hd'⟩, (yWins_iff c hn hc hd').2 ⟨rfl, by omega⟩⟩
  rw [hf, Finset.card_product, Finset.card_singleton, Int.card_Ico, one_mul]
  have : (((15 - n - 1).toNat : ℕ) : ℝ) = 14 - n := by
    have h : ((15 - n - 1).toNat : ℤ) = 14 - n := by rw [Int.toNat_of_nonneg (by omega)]; ring
    exact_mod_cast h
  rw [this]

/-- "The probability of a tie is `12/13`." -/
theorem probTie_eq (hn : 1 ≤ n ∧ n ≤ 13) : probTie n = 12 / 13 := by
  unfold probTie
  rw [sum_ind]
  have hf : (card ×ˢ card).filter (fun p => tie n p.1 p.2) = card.erase n ×ˢ card := by
    ext ⟨c, d⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hc, hd⟩, hw⟩
      exact ⟨⟨(tie_iff n hn hc hd).1 hw, hc⟩, hd⟩
    · rintro ⟨⟨hne, hc⟩, hd⟩
      exact ⟨⟨hc, hd⟩, (tie_iff n hn hc hd).2 hne⟩
  have hn' : n ∈ card := by simp only [card, Finset.mem_Ico]; omega
  rw [hf, Finset.card_product, Finset.card_erase_of_mem hn', card_card]
  norm_num

/-- The three outcomes exhaust the game: the probabilities sum to `1`. -/
theorem probs_sum (hn : 1 ≤ n ∧ n ≤ 13) : probXWins n + probYWins n + probTie n = 1 := by
  rw [probXWins_eq n hn, probYWins_eq n hn, probTie_eq n hn]; ring

/-- "For `n<8`, “under `n+1`” beats “under `n`”." -/
theorem under_succ_beats (hn : 1 ≤ n ∧ n < 8) : probXWins n < probYWins n := by
  rw [probXWins_eq n ⟨hn.1, by omega⟩, probYWins_eq n ⟨hn.1, by omega⟩]
  have : (n : ℝ) ≤ 7 := by exact_mod_cast (by omega : n ≤ 7)
  linarith

/-- "For `n≥8`, “under `n`” beats “under `n+1`”." -/
theorem under_beats_succ (hn : 8 ≤ n ∧ n ≤ 13) : probYWins n < probXWins n := by
  rw [probXWins_eq n ⟨by omega, hn.2⟩, probYWins_eq n ⟨by omega, hn.2⟩]
  have : (8 : ℝ) ≤ n := by exact_mod_cast hn.1
  linarith

/-- "So “under 8” beats both “under 7” and “under 9”": as player `y` against "under 7" (`n = 7`)
and as player `x` against "under 9" (`n = 8`). -/
theorem under_eight_best : probXWins 7 < probYWins 7 ∧ probYWins 8 < probXWins 8 :=
  ⟨under_succ_beats 7 (by norm_num), under_beats_succ 8 (by norm_num)⟩

end Probabilistic

end LaPToP.ProgramTheory
