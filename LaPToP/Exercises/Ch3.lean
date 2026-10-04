import LaPToP.Exercises.Basic
import LaPToP.BasicTheories.Bunch
import Mathlib.Tactic

/-!
# Exercises — Function Theory (aPToP §10.3)

Quantifiers are Lean's, over types or over sets standing for the book's
domains; bunches are sets; `¢` is `Set.encard`. "Express formally" exercises are
answered by definitions, with what can be proved about them (an example, or
agreement with Mathlib's notion). Exercises that ask to translate English
(79, 82, 89), to design (81, 84, 85, 114(a), 115), to explain (108, 120), or
that rest on the book's untyped functions and lists (86, 87, 103, 106, 110) have
no formal statement here; they are listed in `MISSING.md` §5.
-/

namespace LaPToP.Exercises.Ch3

open LaPToP.BasicTheories

/-! ### Exercise 69: application -/

/-- `⟨x: int· ⟨y: int· ⟨z: int· x≥0 ∧ x²≤y ∧ ∀z: int· z²≤y ⇒ z≤x⟩⟩⟩`. -/
def p (x y _ : ℤ) : Prop := 0 ≤ x ∧ x ^ 2 ≤ y ∧ ∀ z : ℤ, z ^ 2 ≤ y → z ≤ x

/-- **Exercise 69**: applied, the bound `z` is renamed so as not to capture. -/
theorem exercise_69 (x y z u w : ℤ) :
    (p (x + y) (2 * u + w) z ↔
        0 ≤ x + y ∧ (x + y) ^ 2 ≤ 2 * u + w ∧ ∀ z' : ℤ, z' ^ 2 ≤ 2 * u + w → z' ≤ x + y) ∧
      (p (x + y) (2 * u + w) = fun _ =>
        0 ≤ x + y ∧ (x + y) ^ 2 ≤ 2 * u + w ∧ ∀ z' : ℤ, z' ^ 2 ≤ 2 * u + w → z' ≤ x + y) ∧
      (p (x + z) (y + y) (2 + z) ↔
        0 ≤ x + z ∧ (x + z) ^ 2 ≤ y + y ∧ ∀ z' : ℤ, z' ^ 2 ≤ y + y → z' ≤ x + z) :=
  ⟨Iff.rfl, rfl, Iff.rfl⟩

/-! ### Exercises 70–72 -/

/-- `∃!x: D· P x`. -/
def ExistsOne {α : Type*} (D : Set α) (P : α → Prop) : Prop :=
  (∃ x ∈ D, P x) ∧ ∀ x ∈ D, ∀ y ∈ D, P x → P y → x = y

/-- **Exercise 70**: `∃!` defined, and it is Mathlib's unique existence. -/
theorem exercise_70 {α : Type*} (P : α → Prop) : ExistsOne Set.univ P ↔ ∃! x, P x := by
  simp only [ExistsOne, Set.mem_univ, true_and, forall_const]
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩; exact ⟨x, hx, fun y hy => h y x hy hx⟩
  · rintro ⟨x, hx, h⟩; exact ⟨⟨x, hx⟩, fun a b ha hb => (h a ha).trans (h b hb).symm⟩

/-- **Exercise 71**: `¢(§x: D· P x) = 0, 1, 2` without `§`. -/
theorem exercise_71 {α : Type*} (D : Set α) (P : α → Prop) :
    ({x ∈ D | P x}.encard = 0 ↔ ∀ x ∈ D, ¬ P x) ∧
    ({x ∈ D | P x}.encard = 1 ↔ ∃ x ∈ D, P x ∧ ∀ y ∈ D, P y → y = x) ∧
    ({x ∈ D | P x}.encard = 2 ↔
      ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧ P x ∧ P y ∧ ∀ z ∈ D, P z → z = x ∨ z = y) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]; simp
  · rw [Set.encard_eq_one]
    constructor
    · rintro ⟨x, hx⟩
      have : x ∈ {x ∈ D | P x} := hx ▸ rfl
      exact ⟨x, this.1, this.2, fun y hy hpy => by
        have : y ∈ {x ∈ D | P x} := ⟨hy, hpy⟩; rw [hx] at this; exact this⟩
    · rintro ⟨x, hxD, hx, h⟩
      exact ⟨x, Set.ext fun y => ⟨fun ⟨hy, hpy⟩ => h y hy hpy, fun hy => hy ▸ ⟨hxD, hx⟩⟩⟩
  · rw [Set.encard_eq_two]
    constructor
    · rintro ⟨x, y, hxy, hs⟩
      have hx : x ∈ {x ∈ D | P x} := hs ▸ Or.inl rfl
      have hy : y ∈ {x ∈ D | P x} := hs ▸ Or.inr rfl
      exact ⟨x, hx.1, y, hy.1, hxy, hx.2, hy.2, fun z hz hpz => by
        have : z ∈ {x ∈ D | P x} := ⟨hz, hpz⟩; rw [hs] at this; exact this⟩
    · rintro ⟨x, hxD, y, hyD, hxy, hx, hy, h⟩
      refine ⟨x, y, hxy, Set.ext fun z => ⟨fun ⟨hz, hpz⟩ => h z hz hpz, ?_⟩⟩
      rintro (rfl | rfl)
      · exact ⟨hxD, hx⟩
      · exact ⟨hyD, hy⟩

/-- **Exercise 72**: (a) `§n: nat· ∃m: nat· n = m²` is the squares; (b)
`§n: nat· ∃m: nat· n² = m ⇒ n = m²` is all of `nat`. -/
theorem exercise_72 :
    {n : ℕ | ∃ m, n = m ^ 2} = Set.range (· ^ 2) ∧ {n : ℕ | ∃ m, n ^ 2 = m → n = m ^ 2} = Set.univ := by
  refine ⟨Set.ext fun n => ⟨fun ⟨m, h⟩ => ⟨m, h.symm⟩, fun ⟨m, h⟩ => ⟨m, h.symm⟩⟩, ?_⟩
  ext n; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨n ^ 2 + 1, fun h => absurd h (by omega)⟩

/-! ### Exercises 73–76: lists -/

/-- **Exercise 73**: `join` of a list of lists. -/
def join {α : Type*} (L : List (List α)) : List α := L.flatten

theorem exercise_73 : join [[0, 1, 2], [], [3], [4, 5]] = [0, 1, 2, 3, 4, 5] := rfl

/-- **Exercise 74**: `L` is a sublist of `M`: Mathlib's `List.Sublist`. -/
theorem exercise_74 : [0, 2, 1].Sublist [0, 1, 2, 2, 1, 0] ∧ ¬ [2, 0, 1].Sublist [0, 1, 2, 2, 1, 0] := by
  decide

/-- `L` is a segment of `M`. -/
def Seg {α : Type*} (L M : List α) : Prop := ∃ a b, M = a ++ L ++ b

/-- **Exercise 75(a)**: `L` is a longest sorted segment of `M`. -/
def LongestSortedSeg (L M : List ℤ) : Prop :=
  Seg L M ∧ L.Pairwise (· ≤ ·) ∧ ∀ K, Seg K M → K.Pairwise (· ≤ ·) → K.length ≤ L.length

/-- **Exercise 75(b)**: nonempty. -/
def LongestSortedSeg' (L M : List ℤ) : Prop := LongestSortedSeg L M ∧ L ≠ []

/-- **Exercise 75(c)**: a longest sorted sublist, not necessarily a segment. -/
def LongestSortedSub (L M : List ℤ) : Prop :=
  L.Sublist M ∧ L.Pairwise (· ≤ ·) ∧ ∀ K : List ℤ, K.Sublist M → K.Pairwise (· ≤ ·) → K.length ≤ L.length

/-- A palindrome. -/
def Pal {α : Type*} (L : List α) : Prop := L = L.reverse

/-- **Exercise 76**: `n` is the length of a longest palindromic segment of `L`. -/
def LongestPal {α : Type*} (n : ℕ) (L : List α) : Prop :=
  (∃ K, Seg K L ∧ Pal K ∧ K.length = n) ∧ ∀ K, Seg K L → Pal K → K.length ≤ n

/-! ### Exercises 77, 78, 80: arguments -/

/-- **Exercise 77**: John ("if one of us gets sick, we all do") and Mary ("if one
of us stays well, we all do") say the same: all of us are alike. -/
theorem exercise_77 {Person : Type*} (sick : Person → Prop) :
    ((∃ x, sick x) → ∀ x, sick x) ↔ ((∃ x, ¬ sick x) → ∀ x, ¬ sick x) := by
  constructor
  · intro h ⟨x, hx⟩ y hy; exact hx (h ⟨y, hy⟩ x)
  · intro h ⟨x, hx⟩ y; by_contra hy; exact h ⟨y, hy⟩ x hx

/-- **Exercise 78**: if Epimenides, a Cretan, says "all Cretans are liars", and a
liar's statements are false and others' true, then he is a liar and some Cretan
is not. -/
theorem exercise_78 {Person : Type*} (cretan liar : Person → Prop) (e : Person) (he : cretan e)
    (htruth : ¬ liar e → ∀ c, cretan c → liar c) (hlie : liar e → ¬ ∀ c, cretan c → liar c) :
    liar e ∧ ∃ c, cretan c ∧ ¬ liar c := by
  by_cases h : liar e
  · exact ⟨h, by simpa using hlie h⟩
  · exact absurd (htruth h e he) h

/-- **Exercise 80**: the Russell mansion. -/
theorem exercise_80 {Person : Type*} (criminal robbed accomplice breakin smash pick locksmith
    heard fool actor : Person → Prop)
    (i : ∃ x, criminal x ∧ robbed x) (ii : ∀ x, robbed x → accomplice x ∨ breakin x)
    (iii : ∀ x, breakin x → smash x ∨ pick x) (iv : ∀ x, pick x → locksmith x)
    (v : ∀ x, smash x → heard x) (vi : ∀ x, ¬ heard x) (vii : ∀ x, robbed x → fool x)
    (viii : ∀ x, fool x → actor x) (ix : ∀ x, criminal x → ¬ (locksmith x ∧ actor x)) :
    ∃ x, criminal x ∧ accomplice x := by
  obtain ⟨x, hc, hr⟩ := i
  refine ⟨x, hc, (ii x hr).resolve_right fun hb => ?_⟩
  rcases iii x hb with hs | hp
  · exact vi x (v x hs)
  · exact ix x hc ⟨iv x hp, viii x (vii x hr)⟩

/-! ### Exercises 83, 88, 90–93 -/

/-- **Exercise 83**: `(∀i· P i) ⇒ (∃i· Q i) = (∃i, j· P i ⇒ Q j)`. -/
theorem exercise_83 {ι : Type*} (P Q : ι → Prop) :
    ((∀ i, P i) → ∃ i, Q i) ↔ ∃ i j, P i → Q j := by
  constructor
  · intro h
    by_cases hp : ∀ i, P i
    · obtain ⟨j, hj⟩ := h hp
      exact ⟨j, j, fun _ => hj⟩
    · push_neg at hp
      obtain ⟨i, hi⟩ := hp
      exact ⟨i, i, fun h' => absurd h' hi⟩
  · rintro ⟨i, j, h⟩ hp; exact ⟨j, h (hp i)⟩

/-- **Exercise 88**: you can't drive for 6 hours after drinking; so you can't
drink and drive at the same time. -/
theorem exercise_88 (drink drive : ℝ → Prop)
    (rule : ∀ t, drink t → ∀ t', t ≤ t' → t' < t + 6 → ¬ drive t') (t : ℝ) :
    ¬ (drink t ∧ drive t) := fun ⟨h₁, h₂⟩ => rule t h₁ t le_rfl (by linarith) h₂

/-- **Exercise 90**: everyone loves my baby, my baby loves only me: I am my baby. -/
theorem exercise_90 {Person : Type*} (loves : Person → Person → Prop) (me baby : Person)
    (h₁ : ∀ x, loves x baby) (h₂ : ∀ x, loves baby x → x = me) : baby = me := h₂ baby (h₁ baby)

/-- **Exercise 91**: in a bar with someone in it, there is a person such that if
that person drinks, everyone drinks. -/
theorem exercise_91 {Person : Type*} [Nonempty Person] (drinks : Person → Prop) :
    ∃ x, drinks x → ∀ y, drinks y := by
  by_cases h : ∀ y, drinks y
  · exact ⟨Classical.arbitrary _, fun _ => h⟩
  · push_neg at h; obtain ⟨y, hy⟩ := h; exact ⟨y, fun h' => absurd h' hy⟩

/-- **Exercise 92**: (a) `∀y· y = x+2 ⇒ y>5` is `x>3`; (b)
`∀y· y = x+2 ∨ y = x+1 ⇒ y>5` is `x>4`. -/
theorem exercise_92 (x : ℕ) :
    ((∀ y, y = x + 2 → y > 5) ↔ x > 3) ∧ ((∀ y, y = x + 2 ∨ y = x + 1 → y > 5) ↔ x > 4) := by
  constructor
  · constructor
    · intro h; have := h (x + 2) rfl; omega
    · rintro h y rfl; omega
  · constructor
    · intro h; have := h (x + 1) (.inr rfl); omega
    · rintro h y (rfl | rfl) <;> omega

/-- **Exercise 93**. -/
theorem exercise_93 {α : Type*} (P Q R : α → Prop)
    (h : ((∃ x, P x) → ∀ x, R x → Q x) ∧ (∃ x, P x ∨ Q x) ∧ ∀ x, Q x → P x) :
    ∀ x, R x → P x := by
  obtain ⟨h₁, ⟨y, hy⟩, h₃⟩ := h
  have hp : ∃ x, P x := ⟨y, hy.elim id (h₃ y)⟩
  exact fun x hr => h₃ x (h₁ hp x hr)

/-! ### Exercises 94–97 -/

/-- **Exercise 94**: for `P: bin→bin` monotonic, `(∃x· P x) = P ⊤` and
`(∀x· P x) = P ⊥`; antimonotonic, the other way round. -/
theorem exercise_94 (P : Bool → Bool) :
    (P false ≤ P true → ((∃ x, P x = true) ↔ P true = true) ∧ ((∀ x, P x = true) ↔ P false = true)) ∧
    (P true ≤ P false → ((∃ x, P x = true) ↔ P false = true) ∧ ((∀ x, P x = true) ↔ P true = true)) := by
  obtain ⟨t, f, rfl⟩ : ∃ t f : Bool, P = fun x => bif x then t else f :=
    ⟨P true, P false, funext fun x => by cases x <;> rfl⟩
  revert t f; decide

/-- **Exercise 95**: `L` is bitonic: monotonic up to some index, antimonotonic
after. -/
def Bitonic (L : List ℤ) : Prop :=
  ∃ k, (L.take k).Pairwise (· ≤ ·) ∧ (L.drop k).Pairwise (· ≥ ·) ∧
    ∀ (h : 0 < k) (h' : k < L.length), L[k - 1] ≥ L[k]'h'

/-- **Exercise 96**: "there is a natural number that is not equal to any natural
number" is false. -/
theorem exercise_96 : ¬ ∃ n : ℕ, ∀ m : ℕ, n ≠ m := fun ⟨n, h⟩ => h n rfl

/-- **Exercise 97(b), (c), (d), (e), (g), (h)**: the greatest common divisor, the
lowest common multiple, primes, relative primes (as Mathlib's), that there is no
smallest integer, and that between two rationals there is another. -/
theorem exercise_97 (a b g m p n : ℕ) :
    ((g ∣ a ∧ g ∣ b ∧ ∀ d, d ∣ a → d ∣ b → d ∣ g) ↔ g = Nat.gcd a b) ∧
    ((a ∣ m ∧ b ∣ m ∧ ∀ k, a ∣ k → b ∣ k → m ∣ k) ↔ m = Nat.lcm a b) ∧
    ((2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) ↔ p.Prime) ∧
    ((∀ d, d ∣ n → d ∣ m → d = 1) ↔ Nat.Coprime n m) ∧
    (¬ ∃ i : ℤ, ∀ j : ℤ, i ≤ j) ∧
    (∀ x y : ℚ, x < y → ∃ z, x < z ∧ z < y) := by
  refine ⟨⟨fun ⟨h₁, h₂, h₃⟩ => Nat.dvd_antisymm (Nat.dvd_gcd h₁ h₂) (h₃ _ (Nat.gcd_dvd_left a b)
      (Nat.gcd_dvd_right a b)), fun h => h ▸ ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b,
      fun d => Nat.dvd_gcd⟩⟩,
    ⟨fun ⟨h₁, h₂, h₃⟩ => Nat.dvd_antisymm (h₃ _ (Nat.dvd_lcm_left a b) (Nat.dvd_lcm_right a b))
      (Nat.lcm_dvd h₁ h₂), fun h => h ▸ ⟨Nat.dvd_lcm_left a b, Nat.dvd_lcm_right a b,
      fun k => Nat.lcm_dvd⟩⟩,
    ⟨fun ⟨h₁, h₂⟩ => Nat.prime_def.mpr ⟨h₁, h₂⟩, fun h => ⟨h.two_le, fun d hd => (Nat.dvd_prime h).mp hd⟩⟩,
    ⟨fun h => Nat.coprime_of_dvd' fun k _ hn hm => (h k hn hm).symm ▸ dvd_refl 1,
      fun h d hn hm => Nat.eq_one_of_dvd_coprimes h hn hm⟩,
    fun ⟨i, h⟩ => by have := h (i - 1); omega,
    fun x y h => ⟨(x + y) / 2, by linarith, by linarith⟩⟩

/-! ### Exercises 98–102 -/

/-- **Exercise 98**: the people you know are those known by all who know all
whom you know. -/
theorem exercise_98 {Person : Type*} (knows : Person → Person → Prop) (you : Person) (y : Person) :
    knows you y ↔ ∀ z, (∀ w, knows you w → knows z w) → knows z y :=
  ⟨fun h z hz => hz y h, fun h => h you fun _ hw => hw⟩

/-- **Exercise 99**: couples whose oldest man and oldest woman are the same age,
and whose any two swapped make couples with equally old younger partners, have
partners of the same age. -/
theorem exercise_99 {n : ℕ} (man woman : Fin n → ℕ)
    (hold : ∃ j k, (∀ i, man i ≤ man j) ∧ (∀ i, woman i ≤ woman k) ∧ man j = woman k)
    (hswap : ∀ i j, min (man i) (woman j) = min (man j) (woman i)) (i : Fin n) :
    man i = woman i := by
  obtain ⟨j, k, hj, hk, hjk⟩ := hold
  have h₁ := hswap i j
  have h₂ := hswap k i
  have : min (man j) (woman i) = woman i := min_eq_right (hjk ▸ hk i)
  have : min (man i) (woman k) = man i := min_eq_left (hjk ▸ hj i)
  have hk' := hswap i k
  omega

/-- **Exercise 100**: the square of an odd natural is odd, of an even one even. -/
theorem exercise_100 (n : ℕ) : (Odd n → Odd (n ^ 2)) ∧ (Even n → Even (n ^ 2)) :=
  ⟨fun h => h.pow, fun h => by rw [pow_two]; exact h.mul_right n⟩

/-- **Exercise 101**: `∀x: D· P x = (§x: D· P x) = D` and
`∃x: D· P x = ¢(§x: D· P x) ⧧ 0`. -/
theorem exercise_101 {α : Type*} (D : Set α) (P : α → Prop) :
    ((∀ x ∈ D, P x) ↔ {x ∈ D | P x} = D) ∧ ((∃ x ∈ D, P x) ↔ {x ∈ D | P x}.encard ≠ 0) := by
  refine ⟨⟨fun h => Set.ext fun x => ⟨And.left, fun hx => ⟨hx, h x hx⟩⟩,
    fun h x hx => (h.symm ▸ hx : x ∈ {x ∈ D | P x}).2⟩, ?_⟩
  rw [Ne, Set.encard_eq_zero, ← Ne, ← Set.nonempty_iff_ne_empty]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, hx, hp⟩, fun ⟨x, hx, hp⟩ => ⟨x, hx, hp⟩⟩

/-- **Exercise 102**: `Σ((0,..n)→m) = n×m`, `Π((0,..n)→m) = mⁿ`,
`∀((0,..n)→b) = (n=0 ∨ b)`, `∃((0,..n)→b) = (n>0 ∧ b)`. -/
theorem exercise_102 (n m : ℕ) (b : Prop) :
    ∑ _i ∈ Finset.range n, m = n * m ∧ ∏ _i ∈ Finset.range n, m = m ^ n ∧
      ((∀ i ∈ Finset.range n, b) ↔ n = 0 ∨ b) ∧ ((∃ i ∈ Finset.range n, b) ↔ n > 0 ∧ b) := by
  refine ⟨by simp, by simp, ⟨fun h => ?_, ?_⟩, ⟨fun ⟨i, hi, hb⟩ => ⟨by simp at hi; omega, hb⟩,
    fun ⟨hn, hb⟩ => ⟨0, by simp; omega, hb⟩⟩⟩
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact .inl h0
    · exact .inr (h 0 (by simp; omega))
  · rintro (h0 | hb) i hi
    · simp [h0] at hi
    · exact hb

/-! ### Exercises 104, 105, 107, 109 -/

/-- **Exercise 104**: the unicorn statements are consistent only if there are no
unicorns. -/
theorem exercise_104 {Thing : Type*} (unicorn white black : Thing → Prop)
    (h₁ : ∀ x, unicorn x → white x) (h₂ : ∀ x, unicorn x → black x)
    (h₃ : ¬ ∃ x, unicorn x ∧ white x ∧ black x) : ∀ x, ¬ unicorn x :=
  fun x hx => h₃ ⟨x, hx, h₁ x hx, h₂ x hx⟩

/-- **Exercise 105**: there is no man who shaves exactly the men who do not
shave themselves. -/
theorem exercise_105 {Man : Type*} (shaves : Man → Man → Prop) :
    ¬ ∃ b, ∀ m, shaves b m ↔ ¬ shaves m m := fun ⟨b, h⟩ => by
  have := h b; tauto

/-- **Exercise 107** (Cantor's diagonal). -/
theorem exercise_107 : ¬ ∃ f : ℕ → ℕ → ℕ, ∀ g : ℕ → ℕ, ∃ n, f n = g := by
  rintro ⟨f, h⟩
  obtain ⟨n, hn⟩ := h fun k => f k k + 1
  have := congrFun hn n
  omega

/-- **Exercise 109**: `f g = g` for every `g` exactly when `f` is the identity,
and so is `g f = g`. -/
theorem exercise_109 (f : ℕ → ℕ) : ((∀ g : ℕ → ℕ, f ∘ g = g) ↔ f = id) ∧
    ((∀ g : ℕ → ℕ, g ∘ f = g) ↔ f = id) := by
  refine ⟨⟨fun h => by simpa using h id, fun h g => by simp [h]⟩,
    ⟨fun h => by simpa using h id, fun h g => by simp [h]⟩⟩

/-! ### Exercises 111–114, 116–119 -/

/-- **Exercise 111**: `∀i· L i ≤ m = ⇑L ≤ m` and `∃i· L i ≤ m = ⇓L ≤ m`, for a
nonempty list (a function on `0,..n+1`). -/
theorem exercise_111 {n : ℕ} (L : Fin (n + 1) → ℕ) (m : ℕ) :
    ((∀ i, L i ≤ m) ↔ Finset.univ.sup L ≤ m) ∧
      ((∃ i, L i ≤ m) ↔ Finset.univ.inf' Finset.univ_nonempty L ≤ m) := by
  constructor
  · simp [Finset.sup_le_iff]
  · simp [Finset.inf'_le_iff]

/-- **Exercise 112**: `∃b: f A· p b = ∃a: A· p (f a)`, and likewise `∀`. -/
theorem exercise_112 {α β : Type*} (f : α → β) (A : Set α) (p : β → Prop) :
    ((∃ b ∈ f '' A, p b) ↔ ∃ a ∈ A, p (f a)) ∧ ((∀ b ∈ f '' A, p b) ↔ ∀ a ∈ A, p (f a)) :=
  ⟨Set.exists_mem_image, Set.forall_mem_image⟩

/-- **Exercise 113**: `n=m = ∀k· (k≤n)=(k≤m)`, over the reals. -/
theorem exercise_113 (n m : ℝ) : n = m ↔ ∀ k, (k ≤ n ↔ k ≤ m) := by
  refine ⟨fun h k => h ▸ Iff.rfl, fun h => le_antisymm ((h n).mp le_rfl) ((h m).mpr le_rfl)⟩

/-- **Exercise 114(b)**: no two different naturals are tied for smallest. -/
theorem exercise_114 (a b : ℕ) (ha : ∀ m, a ≤ m) (hb : ∀ m, b ≤ m) : a = b :=
  le_antisymm (ha b) (hb a)

/-- **Exercise 116**: the axioms are inconsistent (on anything with an element):
there is no such relation. -/
theorem exercise_116 {α : Type*} [Nonempty α] :
    ¬ ∃ R : α → α → Prop, (∀ x, ∃ y, R x y) ∧ (∀ x, ¬ R x x) ∧
      (∀ x y z, R x y → R y z → R x z) ∧ ∃ u, ∀ x, x = u ∨ R x u := by
  rintro ⟨R, htot, hirr, htr, u, hu⟩
  obtain ⟨y, hy⟩ := htot u
  rcases hu y with rfl | h
  · exact hirr _ hy
  · exact hirr u (htr u y u hy h)

/-- **Exercise 117**: from `x` we can reach `y` in some number of steps: there is
a path, a list of points each a step from the one before. -/
def Reach {α : Type*} (R : α → α → Prop) (x y : α) : Prop :=
  ∃ k, ∃ path : Fin (k + 1) → α, path 0 = x ∧ path (Fin.last k) = y ∧
    ∀ i : Fin k, R (path i.castSucc) (path i.succ)

/-- **Exercise 118**: `R` is the transitive closure of `Q`: the strongest
transitive relation implied by `Q`; `Relation.TransGen Q` is it. -/
def TransClosure {α : Type*} (Q R : α → α → Prop) : Prop :=
  (∀ x y, Q x y → R x y) ∧ (∀ x y z, R x y → R y z → R x z) ∧
    ∀ S : α → α → Prop, (∀ x y, Q x y → S x y) → (∀ x y z, S x y → S y z → S x z) →
      ∀ x y, R x y → S x y

theorem exercise_118 {α : Type*} (Q : α → α → Prop) : TransClosure Q (Relation.TransGen Q) := by
  refine ⟨fun x y h => .single h, fun x y z h₁ h₂ => h₁.trans h₂, fun S hQ hS x y h => ?_⟩
  induction h with
  | single h => exact hQ _ _ h
  | tail _ h ih => exact hS _ _ _ ih (hQ _ _ h)

/-- **Exercise 119** (pigeon-hole): `ΣL > n×#L ⇒ ∃i: ☐L· L i > n`. -/
theorem exercise_119 (L : List ℝ) (n : ℝ) (h : L.sum > n * L.length) : ∃ x ∈ L, x > n := by
  by_contra hc
  push_neg at hc
  have : L.sum ≤ n * L.length := by
    have := List.sum_le_length_nsmul L n hc
    simpa [nsmul_eq_mul, mul_comm] using this
  linarith

end LaPToP.Exercises.Ch3
