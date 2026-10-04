import LaPToP.ProgramTheory.CompileBT

/-!
# The converse: the machine does nothing the language disallows

The compiler's theorems run forward: whenever the language's 32-bit execution
takes a state to another, the loaded machine halts holding it (`load_correct`,
`bt_success`). This file runs the other way. If the loaded machine halts, the
language's own 32-bit execution — backtracking's abstract machine (`BStep`),
which for a program without `or` and `ensure` is just its run — cannot go on
forever. It ends:

* at the end of the program, in a state the machine's cells hold and the
  language's semantics allows (`Eval`);
* in failure, and then the program has no poststate at all;
* or **stuck**: no step of the 32-bit execution applies. That is where some
  value would leave 32 bits or an index leave its array (`Fits` fails), or the
  program uses something the backtracking compiler leaves out (time, a choice
  inside a call, too many choice points).

So a machine that halts computes what the language computes, or the language's
32-bit run got stuck first (**`converse`**).

The argument: every step of backtracking either moves the machine at least one
instruction (`machine_sim`'s progress, and the count of choice points for a
choice or a failure), or is idle — `ok`, the split of `P. Q`, an empty list
literal, a true `ensure` — and makes what is left to run smaller. Since the
machine is deterministic and halts after `N` instructions, the pair
(instructions still to come, size of what is left) goes down at every step.
-/

namespace LaPToP.ProgramTheory.CompileConverse

open LaPToP.ProgramTheory.Interpreter LaPToP.ProgramTheory.Interpreter.Lang
open LaPToP.ProgramTheory.CompileB4 LaPToP.ProgramTheory.CompileNet
open LaPToP.ProgramTheory.CompileBT LaPToP.ProgramTheory.Interpreter.Network B4 Relation

/-! ### Counting the machine's steps -/

/-- One instruction. -/
abbrev Step1 (a b : State) : Prop := Running a ∧ NotIo a ∧ b = step a

theorem runN_add (a b : ℕ) (s : State) : runN (a + b) s = runN b (runN a s) := by
  induction a generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    by_cases h : Running s
    · rw [show a + 1 + b = (a + b) + 1 by omega, runN_succ_of_running _ _ h,
        runN_succ_of_running _ _ h, ih]
    · -- a machine that is not running stays put
      have hs : ∀ n, runN n s = s := by
        intro n; cases n with
        | zero => rfl
        | succ n => simp only [runN]; unfold Running at h; split_ifs <;> simp_all
      rw [hs, hs, hs]

/-- A run of `d` instructions, every one from a running machine. -/
def RunsFor (d : ℕ) (s s' : State) : Prop := runN d s = s' ∧ ∀ j < d, Running (runN j s)

theorem runsFor_of_steps {s s' : State} (h : Steps s s') : ∃ d, RunsFor d s s' := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | head hab _ ih =>
    obtain ⟨hr, -, rfl⟩ := hab
    obtain ⟨d, hd, hrun⟩ := ih
    refine ⟨d + 1, by rw [runN_succ_of_running _ _ hr, hd], fun j hj => ?_⟩
    cases j with
    | zero => exact hr
    | succ j => rw [runN_succ_of_running _ _ hr]; exact hrun j (by omega)

theorem runsFor_of_transGen {s s' : State} (h : TransGen Step1 s s') :
    ∃ d, 0 < d ∧ RunsFor d s s' := by
  obtain ⟨b, hab, hb⟩ := TransGen.head'_iff.mp h
  obtain ⟨hr, -, rfl⟩ := hab
  obtain ⟨d, hd, hrun⟩ := runsFor_of_steps hb
  refine ⟨d + 1, by omega, by rw [runN_succ_of_running _ _ hr, hd], fun j hj => ?_⟩
  cases j with
  | zero => exact hr
  | succ j => rw [runN_succ_of_running _ _ hr]; exact hrun j (by omega)

theorem RunsFor.trans {d e : ℕ} {s s' s'' : State} (h₁ : RunsFor d s s') (h₂ : RunsFor e s' s'') :
    RunsFor (d + e) s s'' := by
  refine ⟨by rw [runN_add, h₁.1, h₂.1], fun j hj => ?_⟩
  by_cases hjd : j < d
  · exact h₁.2 j hjd
  · obtain ⟨i, rfl⟩ : ∃ i, j = d + i := ⟨j - d, by omega⟩
    rw [runN_add, h₁.1]; exact h₂.2 i (by omega)

/-- A machine that has halted by `N` ran at most `N` instructions to get anywhere. -/
theorem le_of_halts {N d : ℕ} {s₀ s : State} (hN : getRST (runN N s₀) = 0) (h : RunsFor d s₀ s) :
    d ≤ N := by
  by_contra hlt
  have := (h.2 N (by omega)).1
  rw [hN] at this; exact absurd this (by decide)

theorem transGen_of_ne {s s' : State} (h : Steps s s') (hne : s' ≠ s) : TransGen Step1 s s' := by
  rcases reflTransGen_iff_eq_or_transGen.mp h with h | h
  · exact absurd h hne
  · exact h

/-! ### What is left gets smaller -/

/-- The size of a statement: a sequence counts more than its parts. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.size : Stmt → ℕ
  | .seq p q => p.size + q.size + 1
  | _ => 1

/-- The size of what is left to run. -/
def size (ks : List Stmt) : ℕ := (ks.map Stmt.size).sum

theorem size_cons (p : Stmt) (ks : List Stmt) : size (p :: ks) = p.size + size ks := by
  simp [size]

theorem size_lt_of_idle {L : Layout} {Λ : Scripts Value} {a b : List Stmt × PSt ℕ Value}
    {Λ' : Scripts Value} (h : SAct L lone Λ a b Λ') (hi : Idle a.1) : size b.1 < size a.1 := by
  cases h with
  | ok => simp [size_cons, Stmt.size]
  | seq => simp [size_cons, Stmt.size]; omega
  | @fill ks st x a₀ es vs _ _ _ _ =>
    cases es with
    | nil => simp [size_cons, Stmt.size]
    | cons e es => exact absurd hi (by simp [Idle])
  | _ => simp [Idle] at hi

/-! ### Every step of backtracking makes progress -/

theorem cnt_ne {L : Layout} (hB : BTOk L) {c c' : BCfg} {s : State} (hr : BRel L c s)
    (hr' : BRel L c' s) (hne : c'.cps.length ≠ c.cps.length) : False := by
  have h₁ := hr.cnt; have h₂ := hr'.cnt
  rw [h₁] at h₂
  have hcap := hB.cap
  have hc : L.choices ≤ L.cap := by
    have := Nat.le_mul_of_pos_right L.choices (show 0 < L.W + 1 by omega)
    unfold Layout.cap; omega
  have hl := hr.len; have hl' := hr'.len
  have := fromInt32_inj (a := c.cps.length) (b := c'.cps.length)
    ⟨by omega, by push_cast; omega⟩ ⟨by omega, by push_cast; omega⟩ h₂
  omega

/-- **A step of backtracking moves the machine, or makes what is left smaller.** -/
theorem bt_step_progress {L : Layout} (hB : BTOk L) {c c' : BCfg} (h : BStep L c c') {s : State}
    (hr : BRel L c s) :
    ∃ s', Steps s s' ∧ BRel L c' s' ∧ (TransGen Step1 s s' ∨ size c'.cur.1 < size c.cur.1) := by
  cases h with
  | @act a b cps Λ ha ht =>
    obtain ⟨s₁, r₁, hr₁, hd₁, -⟩ := hr.follow hB.ok
    obtain ⟨s₂, r₂, hp₂, lo₂, top₂, prog⟩ :=
      machine_sim L hB.ok ha (sact_not_send ha) (sact_not_recv ha) hr₁.p hd₁
    obtain ⟨et, er⟩ := sact_tr ha ht
    have hw : ∀ j, L.W ≤ j → Wd L (high s₂) j = Wd L (high s₁) j := fun j hj => wd_of_top top₂ hj
    refine ⟨s₂, r₁.trans r₂, ⟨by rw [er]; exact hp₂, by rw [hw _ le_rfl]; exact hr₁.cnt,
      by rw [hw _ (by omega)]; exact hr₁.flag, hr₁.len, fun i hi => (hr₁.recs i hi).mono lo₂ hw,
      fun cp hcp => by rw [et, er]; exact hr₁.same cp hcp⟩, ?_⟩
    rcases prog with hne | hi
    · exact .inl (TransGen.trans_right r₁ (transGen_of_ne r₂ hne))
    · exact .inr (size_lt_of_idle ha hi)
  | choice hfr hlen =>
    obtain ⟨s', r', hr'⟩ := sim_choice hB hfr hlen hr
    refine ⟨s', r', hr', .inl (transGen_of_ne r' fun e => ?_)⟩
    subst e
    exact cnt_ne hB hr hr' (by simp)
  | ensureT hf hc =>
    obtain ⟨s', r', hr'⟩ := sim_ensureT hB.ok hf hc hr
    exact ⟨s', r', hr', .inr (by simp [size_cons, Stmt.size])⟩
  | ensureF hf hc hfr =>
    obtain ⟨s', r', hr'⟩ := sim_ensureF hB hf hc hfr hr
    refine ⟨s', r', hr', .inl (transGen_of_ne r' fun e => ?_)⟩
    subst e
    exact cnt_ne hB hr hr' (by simp)

/-! ### Backtracking cannot run forever on a machine that halts -/

/-- A configuration with no step of backtracking after it. -/
def Final (L : Layout) (c : BCfg) : Prop := ¬ ∃ c', BStep L c c'

/-- **If the machine halts, backtracking reaches a configuration with nothing
after it.** -/
theorem reaches_final {L : Layout} (hB : BTOk L) {N : ℕ} {s₀ : State}
    (hN : getRST (runN N s₀) = 0) :
    ∀ (n m : ℕ) (c : BCfg) (s : State) (k : ℕ), N - k = n → size c.cur.1 = m → RunsFor k s₀ s →
      BRel L c s → ∃ c', ReflTransGen (BStep L) c c' ∧ Final L c' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro c s k hn hm hk hr
      by_cases hc : ∃ c', BStep L c c'
      · obtain ⟨c', hstep⟩ := hc
        obtain ⟨s', r', hr', prog⟩ := bt_step_progress hB hstep hr
        obtain ⟨d, hd⟩ := runsFor_of_steps r'
        have hkd := hk.trans hd
        have hle := le_of_halts hN hkd
        rcases prog with ht | hlt
        · obtain ⟨d', hd'pos, hd'⟩ := runsFor_of_transGen ht
          have hle' := le_of_halts hN (hk.trans hd')
          obtain ⟨c'', r'', hf⟩ := ihn (N - (k + d')) (by omega) _ c' s' (k + d') rfl rfl
            (hk.trans hd') hr'
          exact ⟨c'', .head hstep r'', hf⟩
        · by_cases hd0 : d = 0
          · subst hd0
            have hs : s' = s := by rw [← hd.1]; rfl
            subst hs
            obtain ⟨c'', r'', hf⟩ := ihm _ (by omega) c' s' k hn rfl hk hr'
            exact ⟨c'', .head hstep r'', hf⟩
          · obtain ⟨c'', r'', hf⟩ := ihn (N - (k + d)) (by omega) _ c' s' (k + d) rfl rfl hkd hr'
            exact ⟨c'', .head hstep r'', hf⟩
      · exact ⟨c, .refl, hc⟩

/-! ### The converse -/

/-- A configuration where backtracking is **stuck**: something is left to run, it
is not a failure, and no step applies — a value would leave 32 bits, an index its
array, or the program uses what the backtracking compiler leaves out. -/
def Stuck (L : Layout) (c : BCfg) : Prop := c.cur.1 ≠ [] ∧ ¬ BFails L c ∧ Final L c

theorem halted_eq {s₀ : State} {N n : ℕ} (hN : getRST (runN N s₀) = 0) (hn : getRST (runN n s₀) = 0) :
    runN N s₀ = runN n s₀ := by
  rcases le_total N n with h | h
  · obtain ⟨i, rfl⟩ : ∃ i, n = N + i := ⟨n - N, by omega⟩
    rw [runN_add, runN_of_stopped _ hN]
  · obtain ⟨i, rfl⟩ : ∃ i, N = n + i := ⟨N - n, by omega⟩
    rw [runN_add, runN_of_stopped _ hn]

/-- **The converse.** If the loaded machine halts, then one of three things
holds. The program ends in a state `t` that the language's semantics allows,
the machine's cells hold `t`, and its failure flag is clear. Or the program has
no poststate at all, and the flag is set. Or the language's 32-bit execution got
stuck: a value would have left 32 bits, an index its array, or the program used
what the compiler leaves out. -/
theorem converse {L : Layout} (hB : BTOk L) {p : Stmt} (hF : L.Fit p) (hcl : p.clean = true)
    {st : St} {N : ℕ} (hN : getRST (runN N (load L p st)) = 0) :
    (∃ t : St, @Eval ℕ Value L.env _ p.toProg st t ∧ VarsOk L (high (runN N (load L p st))) t ∧
        Wd L (high (runN N (load L p st))) (L.W + 4) = 0) ∨
      ((∀ t : St, ¬ @Eval ℕ Value L.env _ p.toProg st t) ∧
        Wd L (high (runN N (load L p st))) (L.W + 4) = fromInt32 (-1)) ∨
      ∃ c, ReflTransGen (BStep L) (BCfg.init p st) c ∧ Stuck L c := by
  obtain ⟨c, hc, hfin⟩ := reaches_final hB hN _ _ (BCfg.init p st) (load L p st) 0 rfl rfl
    ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ (bt_init hB.ok hF hcl st)
  obtain ⟨⟨ks, t⟩, cps⟩ := c
  by_cases hks : ks = []
  · subst hks
    left
    obtain ⟨n, hn, hv, hfl⟩ := bt_success hB hF hcl hc
    rw [halted_eq hN hn]
    exact ⟨t.mem, bt_sound hc, hv, hfl⟩
  · by_cases hfail : BFails L ⟨(ks, t), cps⟩
    · right; left
      obtain ⟨n, hn, hfl⟩ := bt_failure hB hF hcl hc hfail
      rw [halted_eq hN hn]
      exact ⟨bt_fail_sound hc hfail, hfl⟩
    · right; right
      exact ⟨_, hc, hks, hfail, hfin⟩

end LaPToP.ProgramTheory.CompileConverse
