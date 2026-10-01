import LaPToP.ProgramTheory.Interpreter
import Mathlib.Tactic.Linarith

/-!
# Probabilistic execution

Section 5.7 generalizes the programming notations "to allow probabilistic
operands": `if b then P else Q = b × P + (1–b) × Q` with `b` a probability, and
`P. Q = Σx′′· (P with x′′ for x′) × (Q with x′′ for x)`, so that a program
denotes a distribution of final states. `Prog.prob r p q` is the probabilistic
`if`; the other interpreters read it as the choice between the branches that
have a chance. `runDist` reads it as the book does: it computes, for a prestate,
the list of final states each with the probability of reaching it, exactly, in
rationals. The same final state may appear more than once; its probability is
the sum of its entries.

## What is proved

* `eval_of_mem_runDist` — every state the distribution gives is an execution of
  the program, so the support is inside the denotation.
* `runDist_nonneg` and `runDist_mass_le` — every weight is a probability, and the
  weights sum to at most `1`. What is missing is the probability of not
  finishing within the fuel, of not finishing at all, or of a failed `ensure`.

The demonstrations in `InterpreterLangSyntax` compute the book's examples and
agree with the values `Probabilistic` proves of them.

## Honest scope

A probability outside `[0, 1]` is clamped. A choice `p or q` is not a
probability; it is resolved as `run` resolves it, by its first branch. Time is
not kept, and an assertion that fails loses its probability, as an `ensure`
does.
-/

namespace LaPToP.ProgramTheory.Interpreter

universe u v

variable {Var : Type u} {Val : Type v} [Defs Var Val] [DecidableEq Var]

/-- The probability of the first branch of `if r then p else q`, the given `r`
clamped to `[0, 1]`. -/
def leftProb (r : ℚ) : ℚ := min 1 r

/-- The probability of the second branch. -/
def rightProb (r : ℚ) : ℚ := 1 - max 0 r

/-- Weight every entry of a distribution by `w`. -/
def scaleDist {σ : Type u} (w : ℚ) (d : List (σ × ℚ)) : List (σ × ℚ) :=
  d.map fun (t, a) => (t, w * a)

/-- Run the distribution `d`, then from each of its states the distribution `k`
gives: the book's `P. Q`, as a sum over the intermediate states. -/
def bindDist {σ τ : Type u} (d : List (σ × ℚ)) (k : σ → List (τ × ℚ)) : List (τ × ℚ) :=
  d.flatMap fun (t, a) => scaleDist a (k t)

/-- `runDist fuel p s`: the final states of `p` from `s`, each with the
probability of reaching it within the fuel. -/
def runDist : ℕ → Prog Var Val → Spec.State Var Val → List (Spec.State Var Val × ℚ)
  | 0, _, _ => []
  | _ + 1, .ok, s => [(s, 1)]
  | _ + 1, .assign x e, s => [(Function.update s x (e s), 1)]
  | n + 1, .seq p q, s => bindDist (runDist n p s) (runDist n q)
  | n + 1, .cond b p q, s => if b s then runDist n p s else runDist n q s
  | n + 1, .whileDo b p, s =>
      if b s then bindDist (runDist n p s) (runDist n (.whileDo b p)) else [(s, 1)]
  | n + 1, .newLocal x e p, s =>
      (runDist n p (Function.update s x (e s))).map fun (t, a) => (Function.update t x (s x), a)
  | _ + 1, .assignAt x e, s => [(Function.update s (x s) (e s), 1)]
  | _ + 1, .ensure b, s => if b s then [(s, 1)] else []
  | n + 1, .or p _, s => runDist n p s
  | _ + 1, .tick, s => [(s, 1)]
  | _ + 1, .assert b, s => if b s then [(s, 1)] else []
  | n + 1, .call k, s => runDist n (Defs.body k) s
  | n + 1, .par own p q, s =>
      bindDist (runDist n p s) fun t =>
        (runDist n q s).map fun (u, b) => (Spec.merge own t u, b)
  | n + 1, .prob r p q, s =>
      (if 0 < r s then scaleDist (leftProb (r s)) (runDist n p s) else []) ++
        (if r s < 1 then scaleDist (rightProb (r s)) (runDist n q s) else [])

/-- The total probability of a distribution. -/
def mass {σ : Type u} (d : List (σ × ℚ)) : ℚ := (d.map (·.2)).sum

/-! ### The support is inside the denotation -/

omit [DecidableEq Var] [Defs Var Val] in
private theorem mem_scaleDist {σ : Type u} {w : ℚ} {d : List (σ × ℚ)} {t : σ} {c : ℚ}
    (h : (t, c) ∈ scaleDist w d) : ∃ a, (t, a) ∈ d ∧ c = w * a := by
  simp only [scaleDist, List.mem_map, Prod.mk.injEq, Prod.exists] at h
  obtain ⟨t', a, hm, rfl, rfl⟩ := h
  exact ⟨a, hm, rfl⟩

omit [DecidableEq Var] [Defs Var Val] in
private theorem mem_bindDist {σ τ : Type u} {d : List (σ × ℚ)} {k : σ → List (τ × ℚ)} {u : τ}
    {c : ℚ} (h : (u, c) ∈ bindDist d k) :
    ∃ t a b, (t, a) ∈ d ∧ (u, b) ∈ k t ∧ c = a * b := by
  simp only [bindDist, List.mem_flatMap, Prod.exists] at h
  obtain ⟨t, a, hd, hk⟩ := h
  obtain ⟨b, hb, rfl⟩ := mem_scaleDist hk
  exact ⟨t, a, b, hd, hb, rfl⟩

/-- **Soundness of the distribution**: every state it gives is an execution. -/
theorem eval_of_mem_runDist : ∀ {f : ℕ} {p : Prog Var Val} {s t : Spec.State Var Val} {w : ℚ},
    (t, w) ∈ runDist f p s → Eval p s t := by
  intro f
  induction f with
  | zero => intro p s t w h; simp [runDist] at h
  | succ n ih =>
    intro p s t w h
    cases p with
    | ok => simp only [runDist, List.mem_singleton, Prod.mk.injEq] at h; rw [h.1]; exact .ok
    | assign x e =>
      simp only [runDist, List.mem_singleton, Prod.mk.injEq] at h; rw [h.1]; exact .assign
    | seq p q =>
      obtain ⟨u, a, b, hu, ht, -⟩ := mem_bindDist (show (t, w) ∈ bindDist _ _ from h)
      exact .seq (ih hu) (ih ht)
    | cond b p q =>
      simp only [runDist] at h
      split_ifs at h with hb
      · exact .condTrue hb (ih h)
      · exact .condFalse (by simpa using hb) (ih h)
    | whileDo b p =>
      simp only [runDist] at h
      split_ifs at h with hb
      · obtain ⟨u, a, c, hu, ht, -⟩ := mem_bindDist h
        exact .whileTrue hb (ih hu) (ih ht)
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        rw [h.1]; exact .whileFalse (by simpa using hb)
    | newLocal x e p =>
      simp only [runDist, List.mem_map, Prod.mk.injEq, Prod.exists] at h
      obtain ⟨u, a, hu, rfl, -⟩ := h
      exact .newLocal (ih hu)
    | assignAt x e =>
      simp only [runDist, List.mem_singleton, Prod.mk.injEq] at h; rw [h.1]; exact .assignAt
    | ensure b =>
      simp only [runDist] at h
      split_ifs at h with hb
      · simp only [List.mem_singleton, Prod.mk.injEq] at h; rw [h.1]; exact .ensure hb
      · simp at h
    | or p q => exact .orLeft (ih (show (t, w) ∈ runDist n p s from h))
    | tick => simp only [runDist, List.mem_singleton, Prod.mk.injEq] at h; rw [h.1]; exact .tick
    | assert b =>
      simp only [runDist] at h
      split_ifs at h with hb
      · simp only [List.mem_singleton, Prod.mk.injEq] at h; rw [h.1]; exact .assert hb
      · simp at h
    | call k => exact .call (ih (show (t, w) ∈ runDist n (Defs.body k) s from h))
    | par own p q =>
      obtain ⟨u, a, c, hu, hk, -⟩ := mem_bindDist (show (t, w) ∈ bindDist _ _ from h)
      simp only [List.mem_map, Prod.mk.injEq, Prod.exists] at hk
      obtain ⟨v, b, hv, rfl, -⟩ := hk
      exact .par (ih hu) (ih hv)
    | prob r p q =>
      simp only [runDist, List.mem_append] at h
      rcases h with h | h
      · split_ifs at h with hr
        · obtain ⟨a, ha, -⟩ := mem_scaleDist h
          exact .probLeft hr (ih ha)
        · simp at h
      · split_ifs at h with hr
        · obtain ⟨a, ha, -⟩ := mem_scaleDist h
          exact .probRight hr (ih ha)
        · simp at h

/-- So every state the distribution gives satisfies the program's denotation. -/
theorem denote_of_mem_runDist {f : ℕ} {p : Prog Var Val} {s t : Spec.State Var Val} {w : ℚ}
    (h : (t, w) ∈ runDist f p s) : denote p s t :=
  denote_of_eval (eval_of_mem_runDist h)

/-! ### The weights are probabilities -/

/-- A list of nonnegative weights summing to at most `1`. -/
def SubDist {σ : Type u} (d : List (σ × ℚ)) : Prop := (∀ e ∈ d, 0 ≤ e.2) ∧ mass d ≤ 1

omit [DecidableEq Var] [Defs Var Val] in
private theorem mass_cons {σ : Type u} (e : σ × ℚ) (d : List (σ × ℚ)) :
    mass (e :: d) = e.2 + mass d := by simp [mass]

omit [DecidableEq Var] [Defs Var Val] in
private theorem mass_append {σ : Type u} (d₁ d₂ : List (σ × ℚ)) :
    mass (d₁ ++ d₂) = mass d₁ + mass d₂ := by simp [mass]

omit [DecidableEq Var] [Defs Var Val] in
private theorem mass_scaleDist {σ : Type u} (w : ℚ) (d : List (σ × ℚ)) :
    mass (scaleDist w d) = w * mass d := by
  induction d with
  | nil => simp [mass, scaleDist]
  | cons e d ih =>
    simp only [scaleDist, List.map_cons] at ih ⊢
    rw [mass_cons, mass_cons, ih, mul_add]

omit [DecidableEq Var] [Defs Var Val] in
private theorem nonneg_scaleDist {σ : Type u} {w : ℚ} (hw : 0 ≤ w) {d : List (σ × ℚ)}
    (hd : ∀ e ∈ d, 0 ≤ e.2) : ∀ e ∈ scaleDist w d, 0 ≤ e.2 := by
  intro e he
  obtain ⟨t, c⟩ := e
  obtain ⟨a, ha, rfl⟩ := mem_scaleDist he
  exact mul_nonneg hw (hd _ ha)

omit [DecidableEq Var] [Defs Var Val] in
/-- Sequencing two sub-distributions gives one. -/
private theorem subDist_bindDist {σ τ : Type u} {d : List (σ × ℚ)} {k : σ → List (τ × ℚ)}
    (hd : SubDist d) (hk : ∀ t, SubDist (k t)) : SubDist (bindDist d k) := by
  obtain ⟨hnn, hm⟩ := hd
  refine ⟨fun e he => ?_, ?_⟩
  · obtain ⟨u, c⟩ := e
    obtain ⟨t, a, b, ht, hu, rfl⟩ := mem_bindDist he
    exact mul_nonneg (hnn _ ht) ((hk t).1 _ hu)
  · have key : ∀ (d : List (σ × ℚ)), (∀ e ∈ d, 0 ≤ e.2) → mass (bindDist d k) ≤ mass d := by
      intro d hd
      induction d with
      | nil => simp [bindDist, mass]
      | cons e d ih =>
        obtain ⟨t, a⟩ := e
        have ha : 0 ≤ a := hd _ List.mem_cons_self
        have hrest := ih fun e he => hd e (List.mem_cons_of_mem _ he)
        simp only [bindDist, List.flatMap_cons] at hrest ⊢
        rw [mass_append, mass_scaleDist, mass_cons]
        have : a * mass (k t) ≤ a := by
          simpa using mul_le_mul_of_nonneg_left (hk t).2 ha
        exact add_le_add this hrest
    exact le_trans (key d hnn) hm

/-- **The weights are probabilities**: every weight is nonnegative, and the
weights sum to at most `1`. -/
theorem subDist_runDist : ∀ (f : ℕ) (p : Prog Var Val) (s : Spec.State Var Val),
    SubDist (runDist f p s) := by
  have point : ∀ (t : Spec.State Var Val), SubDist [(t, (1 : ℚ))] :=
    fun t => ⟨by simp, by simp [mass]⟩
  have empty : SubDist ([] : List (Spec.State Var Val × ℚ)) := ⟨by simp, by simp [mass]⟩
  intro f
  induction f with
  | zero => intro p s; exact empty
  | succ n ih =>
    intro p s
    cases p with
    | ok => exact point s
    | assign x e => exact point _
    | seq p q => exact subDist_bindDist (ih p s) (ih q)
    | cond b p q =>
      simp only [runDist]; split_ifs
      · exact ih p s
      · exact ih q s
    | whileDo b p =>
      simp only [runDist]; split_ifs
      · exact subDist_bindDist (ih p _) (ih _)
      · exact point s
    | newLocal x e p =>
      obtain ⟨hnn, hm⟩ := ih p (Function.update s x (e s))
      refine ⟨fun e he => ?_, ?_⟩
      · simp only [runDist, List.mem_map, Prod.exists] at he
        obtain ⟨u, a, hu, rfl⟩ := he
        exact hnn (u, a) hu
      · simpa [runDist, mass, List.map_map, Function.comp_def] using hm
    | assignAt x e => exact point _
    | ensure b =>
      simp only [runDist]; split_ifs
      · exact point s
      · exact empty
    | or p q => exact ih p s
    | tick => exact point s
    | assert b =>
      simp only [runDist]; split_ifs
      · exact point s
      · exact empty
    | call k => exact ih _ s
    | par own p q =>
      refine subDist_bindDist (ih p s) fun t => ?_
      obtain ⟨hnn, hm⟩ := ih q s
      refine ⟨fun e he => ?_, ?_⟩
      · simp only [List.mem_map, Prod.exists] at he
        obtain ⟨u, b, hu, rfl⟩ := he
        exact hnn (u, b) hu
      · simpa [mass, List.map_map, Function.comp_def] using hm
    | prob r p q =>
      obtain ⟨hnp, hmp⟩ := ih p s
      obtain ⟨hnq, hmq⟩ := ih q s
      have hl : 0 ≤ leftProb (r s) ∨ ¬ 0 < r s := by
        by_cases h : 0 < r s
        · exact Or.inl (le_min zero_le_one h.le)
        · exact Or.inr h
      have hr : 0 ≤ rightProb (r s) ∨ ¬ r s < 1 := by
        by_cases h : r s < 1
        · exact Or.inl (sub_nonneg.mpr (max_le zero_le_one h.le))
        · exact Or.inr h
      simp only [runDist]
      refine ⟨fun e he => ?_, ?_⟩
      · rw [List.mem_append] at he
        rcases he with he | he
        · split_ifs at he with h
          · exact nonneg_scaleDist (hl.resolve_right (not_not.mpr h)) hnp e he
          · simp at he
        · split_ifs at he with h
          · exact nonneg_scaleDist (hr.resolve_right (not_not.mpr h)) hnq e he
          · simp at he
      · rw [mass_append]
        split_ifs with h₁ h₂ h₂
        · rw [mass_scaleDist, mass_scaleDist]
          have e₁ : leftProb (r s) = r s := min_eq_right h₂.le
          have e₂ : rightProb (r s) = 1 - r s := by rw [rightProb, max_eq_right h₁.le]
          rw [e₁, e₂]
          have a₁ : r s * mass (runDist n p s) ≤ r s := by
            simpa using mul_le_mul_of_nonneg_left hmp h₁.le
          have a₂ : (1 - r s) * mass (runDist n q s) ≤ 1 - r s := by
            simpa using mul_le_mul_of_nonneg_left hmq (sub_nonneg.mpr h₂.le)
          linarith
        · rw [mass_scaleDist]
          have : leftProb (r s) ≤ 1 := min_le_left _ _
          simp only [mass, List.map_nil, List.sum_nil, add_zero]
          exact le_trans (mul_le_of_le_one_right (le_min zero_le_one h₁.le) hmp) this
        · rw [mass_scaleDist]
          have e₂ : rightProb (r s) = 1 := by rw [rightProb, max_eq_left (not_lt.mp h₁), sub_zero]
          rw [e₂, one_mul]
          simpa [mass] using hmq
        · simp [mass]

/-- Every weight is nonnegative. -/
theorem runDist_nonneg (f : ℕ) (p : Prog Var Val) (s : Spec.State Var Val) :
    ∀ e ∈ runDist f p s, 0 ≤ e.2 :=
  (subDist_runDist f p s).1

/-- The weights sum to at most `1`. -/
theorem runDist_mass_le (f : ℕ) (p : Prog Var Val) (s : Spec.State Var Val) :
    mass (runDist f p s) ≤ 1 :=
  (subDist_runDist f p s).2

end LaPToP.ProgramTheory.Interpreter
