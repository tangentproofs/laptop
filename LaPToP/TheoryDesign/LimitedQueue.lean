import LaPToP.TheoryDesign.DataTransformation

/-!
# Limited queue

This module formalizes Section 7.2.3 (Limited Queue) of Eric Hehner's *A
Practical Theory of Programming* (aPToP), Exercise 464: the transformer, the
discovery that it loses information, the revised transformer with a mode
bit, and the transformed `mkemptyq`, `isemptyq`, `isfullq`, `join`, `leave`
and `front`.

"A limited queue is a queue with a limited number of places for items. Let
the limit be `n: nat+1`, and let `Q: [n*X]` and `p: 0,..n+1` be implementer's
variables. Then the original implementation is as follows.
`mkemptyq = p:= 0`, `isemptyq = p=0`, `isfullq = p=n`, `join x = Q p:= x. p:= p+1`,
`leave = for i:= 1;..p do Q (i–1):= Q i od. p:= p–1`, `front = Q 0`. ...
Unfortunately, removing the front item from the queue takes time `p–1` to
shift all remaining items down one index. We want to transform the queue so
that all operations are instant. Variables `Q` and `p` will be replaced by
`R: [n*X]` and `f, b: 0,..n+1` with `f` and `b` indicating the current front
and back. ... Here is the data transformer `D`.

    Q[0;..p] = R[f;..b]  ∨  Q[0;..p] = R[(f;..n); (0;..b)]

The conjuncts `0≤p≤n ∧ 0≤f≤b≤n ∧ p=b–f` are implicit in the left disjunct,
and the conjuncts `0≤p≤n ∧ 0≤f≤n ∧ 0≤b≤n ∧ p=n–f+b` are implicit in the right
disjunct."

## The model

Lists of length `n` are functions `ℕ → X` of which only the indexes below `n`
matter. The implicit conjuncts are made explicit in `D₀`: the "inside" mode
`f ≤ b`, `p = b – f`, `Q k = R (f + k)` for `k < p`, or the "outside" mode
`p = n – f + b`, `Q k = R ((f + k) mod n)` for `k < p`. The book's typing
`f, b: 0,..n+1` is a hypothesis of the transformer property `∀new· ∃old· D`
(`isTransformer_D₀`).

"Suspiciously, we have `¬c′` in every case. That's because `f=b` is missing!
So the transformed operation is unimplementable. That's the transformer's
way of telling us that the new variables do not hold enough information to
answer whether the queue is empty. The problem occurs when `f=b` because that
could be either an empty queue or a full queue." This is
`not_implementable_isemptyq₀`: from `f = b` the imagined queue may be empty
(inside) or full (outside), and `c′` would have to be both `⊤` and `⊥`.

"A solution is to add a new variable `m: bin` to say whether we have the
“inside” mode or “outside” mode." With the revised `D`, the book's programs
for `mkemptyq` (`m:= ⊤. f:= 0. b:= 0`), `c:= isemptyq`
(`c:= if m then f=b else b=0 ∧ f=n`) and `c:= isfullq`
(`c:= if m then f=0 ∧ b=n else f=b`) are proved to refine the transformed
operations; the book's intermediate equalities ("several omitted steps") are
not reproduced. "Before this operation, there should be a check that the
queue is not full" (resp. "not empty"): the refinements of `join`, `leave`
and `front` are stated under these checks as preconditions on the new state
(the transformed `isfullq` and `isemptyq`). The "opportunity to rotate the
queue within `R`", which the book declines, is likewise declined: the new
final states are those of the book's programs.
-/

namespace LaPToP.TheoryDesign

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

universe u

namespace LimitedQueue

open Spec

variable {X : Type u} (n : ℕ)

/-- The user's variables: the binary `c` and an item `x`. -/
abbrev U (X : Type u) := Prop × X

/-- The old implementer's variables `Q: [n*X]`, `p: 0,..n+1`. -/
abbrev O (X : Type u) := (ℕ → X) × ℕ

/-- The new implementer's variables `R: [n*X]`, `f, b: 0,..n+1`. -/
abbrev N₀ (X : Type u) := (ℕ → X) × ℕ × ℕ

/-- The new implementer's variables with the mode bit `m`. -/
abbrev N (X : Type u) := N₀ X × Prop

/-- `Q[0;..p] = R[f;..b]` with its implicit conjuncts `f≤b ∧ p=b–f`. -/
def Inside (Q : ℕ → X) (p : ℕ) (R : ℕ → X) (f b : ℕ) : Prop :=
  f ≤ b ∧ p = b - f ∧ ∀ k, k < p → Q k = R (f + k)

/-- `Q[0;..p] = R[(f;..n); (0;..b)]` with its implicit conjunct `p=n–f+b`. -/
def Outside (Q : ℕ → X) (p : ℕ) (R : ℕ → X) (f b : ℕ) : Prop :=
  p = n - f + b ∧ ∀ k, k < p → Q k = R ((f + k) % n)

/-- The book's first transformer `D`, with the implicit bounds `0≤p≤n`, `0≤f≤n`,
`0≤b≤n` made explicit. -/
def D₀ (o : O X) (r : N₀ X) : Prop :=
  o.2 ≤ n ∧ r.2.1 ≤ n ∧ r.2.2 ≤ n ∧ (Inside o.1 o.2 r.1 r.2.1 r.2.2 ∨ Outside n o.1 o.2 r.1 r.2.1 r.2.2)

/-- The revised transformer: `m ∧ Q[0;..p] = R[f;..b] ∨ ¬m ∧ Q[0;..p] = R[(f;..n); (0;..b)]`. -/
def D (o : O X) (r : N X) : Prop :=
  o.2 ≤ n ∧ r.1.2.1 ≤ n ∧ r.1.2.2 ≤ n ∧
    ((r.2 ∧ Inside o.1 o.2 r.1.1 r.1.2.1 r.1.2.2) ∨ (¬ r.2 ∧ Outside n o.1 o.2 r.1.1 r.1.2.1 r.1.2.2))

/-- `∀new· ∃old· D`, under the typing `f, b: 0,..n+1` of the new variables. -/
theorem isTransformer_D₀ (R : ℕ → X) {f b : ℕ} (hf : f ≤ n) (hb : b ≤ n) : ∃ o, D₀ n o (R, f, b) := by
  rcases le_or_gt f b with hfb | hfb
  · exact ⟨(fun k => R (f + k), b - f), show b - f ≤ n by omega, hf, hb, Or.inl ⟨hfb, rfl, fun _ _ => rfl⟩⟩
  · exact ⟨(fun k => R ((f + k) % n), n - f + b), show n - f + b ≤ n by omega, hf, hb,
      Or.inr ⟨rfl, fun _ _ => rfl⟩⟩

/-- `∀new· ∃old· D` for the revised transformer, under the typing `f, b: 0,..n+1`
and the implicit conjuncts of the chosen mode (`f ≤ b` inside, `b ≤ f` outside). -/
theorem isTransformer_D (R : ℕ → X) {f b : ℕ} (hf : f ≤ n) (hb : b ≤ n) {m : Prop}
    (hin : m → f ≤ b) (hout : ¬ m → b ≤ f) : ∃ o, D n o ((R, f, b), m) := by
  by_cases hm : m
  · exact ⟨(fun k => R (f + k), b - f), show b - f ≤ n by omega, hf, hb,
      Or.inl ⟨hm, hin hm, rfl, fun _ _ => rfl⟩⟩
  · have := hout hm
    exact ⟨(fun k => R ((f + k) % n), n - f + b), show n - f + b ≤ n by omega, hf, hb,
      Or.inr ⟨hm, rfl, fun _ _ => rfl⟩⟩

/-! ### The original operations, on the user's and old implementer's variables -/

/-- `mkemptyq = p:= 0`. -/
def mkemptyq : Spec (U X × O X) := fun s s' => s' = (s.1, (s.2.1, 0))

/-- `c:= e` for an expression `e` of the implementer's variables. -/
def assignC (e : O X → Prop) : Spec (U X × O X) := fun s s' => s' = ((e s.2, s.1.2), s.2)

/-- `c:= isemptyq`, i.e. `c:= (p=0)`. -/
def assignC_isemptyq : Spec (U X × O X) := assignC fun o => o.2 = 0

/-- `c:= isfullq`, i.e. `c:= (p=n)`. -/
def assignC_isfullq : Spec (U X × O X) := assignC fun o => o.2 = n

/-! ### "f=b is missing!" -/

/-- The transformed `c:= isemptyq` under the first transformer is unimplementable:
when `f = b` the new state represents both an empty queue (inside mode) and a
full one (outside mode), so `c′` would have to be both `⊤` and `⊥`. -/
theorem not_implementable_isemptyq₀ (hn : 0 < n) [Inhabited X] :
    ¬ Implementable (transform (D₀ n) (assignC_isemptyq (X := X))) := by
  intro h
  obtain ⟨s', hs'⟩ := h ((True, default), (fun _ => default, 0, 0))
  -- the empty queue is represented
  obtain ⟨_, -, h₁⟩ := hs' (fun _ => default, 0) ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Or.inl ⟨le_rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  -- the full queue is represented too
  obtain ⟨_, -, h₂⟩ := hs' (fun _ => default, n) ⟨le_rfl, Nat.zero_le _, Nat.zero_le _,
    Or.inr ⟨by simp, fun _ _ => rfl⟩⟩
  simp only [assignC_isemptyq, assignC, Prod.mk.injEq] at h₁ h₂
  have := congrArg Prod.fst (h₁.1.symm.trans h₂.1)
  simp only [eq_iff_iff, true_iff] at this
  omega

/-! ### The transformed operations under the revised transformer -/

/-- `m:= ⊤. f:= 0. b:= 0`. -/
def mkemptyqT : Spec (U X × N X) := fun s s' => s' = (s.1, ((s.2.1.1, 0, 0), True))

/-- `c:= if m then f=b else b=0 ∧ f=n`, as `c:= (m ∧ f=b ∨ ¬m ∧ b=0 ∧ f=n)`. -/
def isemptyqT : Spec (U X × N X) := fun s s' =>
  s' = (((s.2.2 ∧ s.2.1.2.1 = s.2.1.2.2) ∨ (¬ s.2.2 ∧ s.2.1.2.2 = 0 ∧ s.2.1.2.1 = n), s.1.2), s.2)

/-- `c:= if m then f=0 ∧ b=n else f=b`. -/
def isfullqT : Spec (U X × N X) := fun s s' =>
  s' = (((s.2.2 ∧ s.2.1.2.1 = 0 ∧ s.2.1.2.2 = n) ∨ (¬ s.2.2 ∧ s.2.1.2.1 = s.2.1.2.2), s.1.2), s.2)

/-- `∀Q, p· D ⇒ ∃Q′, p′· D′ ∧ p′=0 ∧ Q′=Q ⇐ m:= ⊤. f:= 0. b:= 0`. -/
theorem mkemptyq_refines : Refines (transform (D n) (mkemptyq (X := X))) mkemptyqT := by
  rintro s _ rfl ⟨Q, p⟩ ⟨-, -, -, -⟩
  exact ⟨(Q, 0), ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Or.inl ⟨trivial, le_rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩, rfl⟩

/-- `∀Q, p· D ⇒ ∃Q′, p′· D′ ∧ c′=(p=0) ∧ p′=p ∧ Q′=Q ⇐ c:= if m then f=b else b=0 ∧ f=n`:
the new variables now hold enough information to tell whether the queue is empty. -/
theorem isemptyq_refines : Refines (transform (D n) (assignC_isemptyq (X := X))) (isemptyqT n) := by
  rintro ⟨⟨c, x⟩, ⟨R, f, b⟩, m⟩ _ rfl ⟨Q, p⟩ ⟨hp, hf, hb, hmode⟩
  refine ⟨(Q, p), ⟨hp, hf, hb, hmode⟩, ?_⟩
  simp only [assignC_isemptyq, assignC, Prod.mk.injEq, and_true]
  apply propext
  dsimp only [Inside, Outside] at hmode
  dsimp only at hp hf hb
  rcases hmode with ⟨hm, hfb, hpe, -⟩ | ⟨hm, hpe, -⟩
  · constructor
    · rintro (⟨-, h⟩ | ⟨hm', -⟩)
      · omega
      · exact absurd hm hm'
    · intro h0; exact Or.inl ⟨hm, by omega⟩
  · constructor
    · rintro (⟨hm', -⟩ | ⟨-, h1, h2⟩)
      · exact absurd hm' hm
      · omega
    · intro h0; exact Or.inr ⟨hm, by omega, by omega⟩

/-- `∀Q, p· D ⇒ ∃Q′, p′· D′ ∧ c′=(p=n) ∧ p′=p ∧ Q′=Q ⇐ c:= if m then f=0 ∧ b=n else f=b`. -/
theorem isfullq_refines : Refines (transform (D n) (assignC_isfullq n (X := X))) (isfullqT n) := by
  rintro ⟨⟨c, x⟩, ⟨R, f, b⟩, m⟩ _ rfl ⟨Q, p⟩ ⟨hp, hf, hb, hmode⟩
  refine ⟨(Q, p), ⟨hp, hf, hb, hmode⟩, ?_⟩
  simp only [assignC_isfullq, assignC, Prod.mk.injEq, and_true]
  apply propext
  dsimp only [Inside, Outside] at hmode
  dsimp only at hp hf hb
  rcases hmode with ⟨hm, hfb, hpe, -⟩ | ⟨hm, hpe, -⟩
  · constructor
    · rintro (⟨-, h1, h2⟩ | ⟨hm', -⟩)
      · omega
      · exact absurd hm hm'
    · intro h; exact Or.inl ⟨hm, by omega, by omega⟩
  · constructor
    · rintro (⟨hm', -⟩ | ⟨-, h⟩)
      · exact absurd hm' hm
      · omega
    · intro h; exact Or.inr ⟨hm, by omega⟩

/-- With the mode bit, the transformed `c:= isemptyq` is implementable (it is
refined by a total program). -/
theorem implementable_isemptyqT : Implementable (transform (D n) (assignC_isemptyq (X := X))) :=
  implementable_of_refines _ _ (isemptyq_refines n) fun _ => ⟨_, rfl⟩

/-! ### `join`, `leave`, `front` (aPToP §7.2.3, continued)

"Next we transform `join x`. Before this operation, there should be a check
that the queue is not full. ... `⇐ if b<n then R b:= x. b:= b+1 else R 0:= x.
b:= 1. m:= ⊥`. Next we transform `leave`. Before this operation, there should
be a check that the queue is not empty. ... `⇐ if f<n then f:= f+1 else f:= 1.
m:= ⊤`. Last we transform `x:= front` where `x` is a user's variable of the
same type as the items. Before this operation, there should be a check that
the queue is not empty. ... `⇐ if f<n then x:= R f else x:= R 0`."

The checks are preconditions on the new state (the transformed `isfullq`
and `isemptyq`), and the refinements are stated under them. -/

/-- `join x = Q p:= x. p:= p+1`. -/
def join (x : X) : Spec (U X × O X) := fun s s' => s' = (s.1, (Function.update s.2.1 s.2.2 x, s.2.2 + 1))

/-- `leave = for i:= 1;..p do Q (i–1):= Q i od. p:= p–1`, i.e.
`Q′ = Q[(1;..p); (p–1;..n)] ∧ p′ = p–1`: the items below `p–1` shift down, the
rest stay. -/
def leave : Spec (U X × O X) := fun s s' =>
  s' = (s.1, (fun k => if k + 1 < s.2.2 then s.2.1 (k + 1) else s.2.1 k, s.2.2 - 1))

/-- `x:= front`, i.e. `x:= Q 0`. -/
def assignX_front : Spec (U X × O X) := fun s s' => s' = ((s.1.1, s.2.1 0), s.2)

/-- `if b<n then R b:= x. b:= b+1 else R 0:= x. b:= 1. m:= ⊥`. -/
def joinT (x : X) : Spec (U X × N X) :=
  cond (fun s => s.2.1.2.2 < n)
    (fun s s' => s' = (s.1, ((Function.update s.2.1.1 s.2.1.2.2 x, s.2.1.2.1, s.2.1.2.2 + 1), s.2.2)))
    (fun s s' => s' = (s.1, ((Function.update s.2.1.1 0 x, s.2.1.2.1, 1), False)))

/-- `if f<n then f:= f+1 else f:= 1. m:= ⊤`. -/
def leaveT : Spec (U X × N X) :=
  cond (fun s => s.2.1.2.1 < n)
    (fun s s' => s' = (s.1, ((s.2.1.1, s.2.1.2.1 + 1, s.2.1.2.2), s.2.2)))
    (fun s s' => s' = (s.1, ((s.2.1.1, 1, s.2.1.2.2), True)))

/-- `if f<n then x:= R f else x:= R 0`. -/
def frontT : Spec (U X × N X) :=
  cond (fun s => s.2.1.2.1 < n)
    (fun s s' => s' = ((s.1.1, s.2.1.1 s.2.1.2.1), s.2))
    (fun s s' => s' = ((s.1.1, s.2.1.1 0), s.2))

/-- The check "the queue is not full", in the new variables (the transformed `isfullq`). -/
def notFullT (s : U X × N X) : Prop :=
  ¬ ((s.2.2 ∧ s.2.1.2.1 = 0 ∧ s.2.1.2.2 = n) ∨ (¬ s.2.2 ∧ s.2.1.2.1 = s.2.1.2.2))

/-- The check "the queue is not empty", in the new variables (the transformed `isemptyq`). -/
def notEmptyT (s : U X × N X) : Prop :=
  ¬ ((s.2.2 ∧ s.2.1.2.1 = s.2.1.2.2) ∨ (¬ s.2.2 ∧ s.2.1.2.2 = 0 ∧ s.2.1.2.1 = n))

/-- A specification under a precondition on the initial state. -/
def guardT (b : U X × N X → Prop) (S : Spec (U X × N X)) : Spec (U X × N X) := fun s s' => b s → S s s'

/-- `(f + k) mod n` for `f + k < n + b`, `b ≤ n`: the "outside" index. -/
theorem outside_index_lt {f k b : ℕ} (hb : b ≤ n) (h : f + k < n + b) :
    (f + k) % n = f + k ∨ (n ≤ f + k ∧ (f + k) % n = f + k - n) := by
  rcases Nat.lt_or_ge (f + k) n with hlt | hge
  · exact Or.inl (Nat.mod_eq_of_lt hlt)
  · right
    refine ⟨hge, ?_⟩
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]

/-- `∀Q, p· D ⇒ ∃Q′, p′· D′ ∧ Q′ = p→x | Q ∧ p′=p+1 ⇐ if b<n then R b:= x. b:= b+1 else
R 0:= x. b:= 1. m:= ⊥`, when the queue is not full. -/
theorem join_refines (hn : 0 < n) (x : X) :
    Refines (guardT (notFullT n) (transform (D n) (join x))) (joinT n x) := by
  rintro ⟨⟨c, x₀⟩, ⟨R, f, b⟩, m⟩ s' h hnf ⟨Q, p⟩ ⟨hp, hf, hb, hmode⟩
  dsimp only [notFullT] at hnf
  dsimp only [Inside, Outside] at hmode
  dsimp only at hp hf hb
  refine ⟨(Function.update Q p x, p + 1), ?_, ?_⟩
  · rcases h with ⟨hbn, rfl⟩ | ⟨hbn, rfl⟩
    · dsimp only [D, Inside, Outside] at hbn ⊢
      rcases hmode with ⟨hm, hfb, hpe, hQ⟩ | ⟨hm, hpe, hQ⟩
      · refine ⟨by omega, hf, by omega, Or.inl ⟨hm, by omega, by omega, fun k hk => ?_⟩⟩
        rcases Nat.lt_or_ge k p with hkp | hkp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hQ k hkp
        · have : k = p := by omega
          subst this
          rw [Function.update_self, show f + k = b by omega, Function.update_self]
      · have hfb : f ≠ b := fun h => hnf (Or.inr ⟨hm, h⟩)
        have hbf : b < f := by omega
        refine ⟨by omega, hf, by omega, Or.inr ⟨hm, by omega, fun k hk => ?_⟩⟩
        rcases Nat.lt_or_ge k p with hkp | hkp
        · rw [Function.update_of_ne (by omega)]
          rw [hQ k hkp]
          rcases outside_index_lt n hb (show f + k < n + b by omega) with h1 | ⟨h2, h3⟩
          · rw [Function.update_of_ne (by omega)]
          · rw [Function.update_of_ne (by omega)]
        · have : k = p := by omega
          subst this
          rw [Function.update_self, show f + k = n + b by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hbn,
            Function.update_self]
    · dsimp only [D, Inside, Outside] at hbn ⊢
      have hbn' : b = n := by omega
      rcases hmode with ⟨hm, hfb, hpe, hQ⟩ | ⟨hm, hpe, hQ⟩
      · have hf0 : 0 < f := by
          by_contra h0
          exact hnf (Or.inl ⟨hm, by omega, hbn'⟩)
        refine ⟨by omega, hf, hn, Or.inr ⟨not_false, by omega, fun k hk => ?_⟩⟩
        rcases Nat.lt_or_ge k p with hkp | hkp
        · rw [Function.update_of_ne (by omega), hQ k hkp, Nat.mod_eq_of_lt (by omega),
            Function.update_of_ne (by omega)]
        · have : k = p := by omega
          subst this
          rw [Function.update_self, show f + k = n by omega, Nat.mod_self, Function.update_self]
      · have hfb : f = b := by omega
        exact absurd (Or.inr ⟨hm, hfb⟩) hnf
  · rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- `∀Q, p· D ⇒ ∃Q′, p′· D′ ∧ Q′ = Q[(1;..p); (p–1;..n)] ∧ p′=p–1 ⇐ if f<n then f:= f+1 else
f:= 1. m:= ⊤`, when the queue is not empty. -/
theorem leave_refines (hn : 0 < n) :
    Refines (guardT (notEmptyT n) (transform (D n) (leave (X := X)))) (leaveT n) := by
  rintro ⟨⟨c, x₀⟩, ⟨R, f, b⟩, m⟩ s' h hne ⟨Q, p⟩ ⟨hp, hf, hb, hmode⟩
  dsimp only [notEmptyT] at hne
  dsimp only [Inside, Outside] at hmode
  dsimp only at hp hf hb
  refine ⟨(fun k => if k + 1 < p then Q (k + 1) else Q k, p - 1), ?_, ?_⟩
  · rcases h with ⟨hfn, rfl⟩ | ⟨hfn, rfl⟩
    · dsimp only [D, Inside, Outside] at hfn ⊢
      rcases hmode with ⟨hm, hfb, hpe, hQ⟩ | ⟨hm, hpe, hQ⟩
      · have hlt : f < b := lt_of_le_of_ne hfb fun h => hne (Or.inl ⟨hm, h⟩)
        refine ⟨by omega, by omega, hb, Or.inl ⟨hm, by omega, by omega, fun k hk => ?_⟩⟩
        rw [if_pos (by omega), hQ (k + 1) (by omega), show f + (k + 1) = f + 1 + k by omega]
      · refine ⟨by omega, by omega, hb, Or.inr ⟨hm, by omega, fun k hk => ?_⟩⟩
        rw [if_pos (by omega), hQ (k + 1) (by omega), show f + (k + 1) = f + 1 + k by omega]
    · dsimp only [D, Inside, Outside] at hfn ⊢
      have hfn' : f = n := by omega
      rcases hmode with ⟨hm, hfb, hpe, hQ⟩ | ⟨hm, hpe, hQ⟩
      · exact absurd (Or.inl ⟨hm, by omega⟩) hne
      · have hb1 : 1 ≤ b := by
          by_contra h0
          exact hne (Or.inr ⟨hm, by omega, hfn'⟩)
        refine ⟨by omega, by omega, hb, Or.inl ⟨trivial, hb1, by omega, fun k hk => ?_⟩⟩
        rw [if_pos (by omega), hQ (k + 1) (by omega), hfn', Nat.add_mod_left, Nat.mod_eq_of_lt (by omega),
          show 1 + k = k + 1 by omega]
  · rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- `∀Q, p· D ⇒ ∃Q′, p′· D′ ∧ x′ = Q 0 ∧ p′=p ∧ Q′=Q ⇐ if f<n then x:= R f else x:= R 0`,
when the queue is not empty. -/
theorem front_refines :
    Refines (guardT (notEmptyT n) (transform (D n) (assignX_front (X := X)))) (frontT n) := by
  rintro ⟨⟨c, x₀⟩, ⟨R, f, b⟩, m⟩ s' h hne ⟨Q, p⟩ ⟨hp, hf, hb, hmode⟩
  dsimp only [notEmptyT] at hne
  dsimp only [Inside, Outside] at hmode
  dsimp only at hp hf hb
  rcases h with ⟨hfn, rfl⟩ | ⟨hfn, rfl⟩
  · dsimp only at hfn
    refine ⟨(Q, p), ⟨hp, hf, hb, hmode⟩, ?_⟩
    simp only [assignX_front, Prod.mk.injEq, and_true, true_and]
    rcases hmode with ⟨hm, hfb, hpe, hQ⟩ | ⟨hm, hpe, hQ⟩
    · have hlt : f < b := lt_of_le_of_ne hfb fun h => hne (Or.inl ⟨hm, h⟩)
      rw [hQ 0 (by omega), Nat.add_zero]
    · rw [hQ 0 (by omega), Nat.add_zero, Nat.mod_eq_of_lt hfn]
  · dsimp only at hfn
    have hfn' : f = n := by omega
    refine ⟨(Q, p), ⟨hp, hf, hb, hmode⟩, ?_⟩
    simp only [assignX_front, Prod.mk.injEq, and_true, true_and]
    rcases hmode with ⟨hm, hfb, hpe, hQ⟩ | ⟨hm, hpe, hQ⟩
    · exact absurd (Or.inl ⟨hm, by omega⟩) hne
    · have hb1 : 1 ≤ b := by
        by_contra h0
        exact hne (Or.inr ⟨hm, by omega, hfn'⟩)
      rw [hQ 0 (by omega), Nat.add_zero, hfn', Nat.mod_self]

end LimitedQueue

end LaPToP.TheoryDesign
