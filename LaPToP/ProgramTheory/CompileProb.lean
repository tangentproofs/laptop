import LaPToP.ProgramTheory.CompileB4

/-!
# Probabilistic choice on b4

The book's `if a/b then P else Q fi` (Section 5.7) takes `P` with probability
`a/b`. The language's execution (`Eval`) reads it by its support: either branch
that has a chance. b4 has no notion of chance in the compiler's proofs, so a
probabilistic choice is made deterministic before it is compiled (`Stmt.det`):
a hidden variable `z` holds a seed, which each choice advances by one step of the
Lehmer generator `z ↦ 16807 z mod (2³¹ – 1)` (computed by Schrage's method, so
that every value stays within 32 bits), and the choice takes `P` when
`z mod b < a`.

The deterministic program is compiled as any other (`CompileB4.load_correct`
applies to it), and **`det_sound`** says what it computes is what the original
program may compute: every 32-bit execution of the deterministic program ends in
a state that the language's execution of the original program also reaches, but
for the seed. A branch is taken only when `z mod b < a` (so `0 < a`, as
`0 ≤ z mod b`) or when `a ≤ z mod b` (so `a < b`, as `z mod b < b`): only when it
has a chance. That `z mod b` is spread evenly over `0,..b` is the generator's
quality, not proved here.
-/

namespace LaPToP.ProgramTheory.CompileProb

open LaPToP.ProgramTheory.Interpreter LaPToP.ProgramTheory.Interpreter.Lang
open LaPToP.ProgramTheory.CompileB4

/-! ### Not touching the seed -/

/-- The variables an expression reads. -/
def reads : Exp → List ℕ
  | .lit _ | .nil => []
  | .var x => [x]
  | .un _ a => reads a
  | .bin _ a b | .cons a b | .index a b => reads a ++ reads b
  | .cond c a b => reads c ++ reads a ++ reads b

/-- Two states that agree but for `z`. -/
def Agree (z : ℕ) (s t : St) : Prop := ∀ y, y ≠ z → s y = t y

theorem Agree.symm {z : ℕ} {s t : St} (h : Agree z s t) : Agree z t s := fun y hy => (h y hy).symm

theorem Agree.trans {z : ℕ} {s t u : St} (h₁ : Agree z s t) (h₂ : Agree z t u) : Agree z s u :=
  fun y hy => (h₁ y hy).trans (h₂ y hy)

theorem Agree.update {z x : ℕ} {s t : St} (h : Agree z s t) (v : Value) :
    Agree z (Function.update s x v) (Function.update t x v) := fun y hy => by
  by_cases hyx : y = x
  · subst hyx; simp
  · simp [Function.update_of_ne hyx, h y hy]

/-- An expression that does not read `z` has the same value in states that agree
but for `z`. -/
theorem eval_agree {z : ℕ} {s t : St} (h : Agree z s t) :
    ∀ e : Exp, z ∉ reads e → e.eval s = e.eval t
  | .lit _, _ => rfl
  | .nil, _ => rfl
  | .var x, hz => h x (by simp [reads] at hz; exact Ne.symm hz)
  | .un _ a, hz => by simp only [Exp.eval]; rw [eval_agree h a hz]
  | .bin _ a b, hz => by
    simp only [reads, List.mem_append, not_or] at hz
    simp only [Exp.eval]; rw [eval_agree h a hz.1, eval_agree h b hz.2]
  | .cons a b, hz => by
    simp only [reads, List.mem_append, not_or] at hz
    simp only [Exp.eval]; rw [eval_agree h a hz.1, eval_agree h b hz.2]
  | .index a b, hz => by
    simp only [reads, List.mem_append, not_or] at hz
    simp only [Exp.eval]; rw [eval_agree h a hz.1, eval_agree h b hz.2]
  | .cond c a b, hz => by
    simp only [reads, List.mem_append, not_or] at hz
    simp only [Exp.eval]; rw [eval_agree h c hz.1.1, eval_agree h a hz.1.2, eval_agree h b hz.2]

/-- A statement that never reads or writes `z`. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.avoids (z : ℕ) : Stmt → Prop
  | .ok | .tick | .call _ | .ret => True
  | .assign x e => x ≠ z ∧ z ∉ reads e
  | .seq p q | .choice p q => p.avoids z ∧ q.avoids z
  | .cond c p q => z ∉ reads c ∧ p.avoids z ∧ q.avoids z
  | .loop c p => z ∉ reads c ∧ p.avoids z
  | .send _ e | .ensure e => z ∉ reads e
  | .recv _ x | .check _ x | .restore x _ => x ≠ z
  | .scope x e p => x ≠ z ∧ z ∉ reads e ∧ p.avoids z
  | .store x i e => x ≠ z ∧ z ∉ reads i ∧ z ∉ reads e
  | .fill x es => x ≠ z ∧ z ∉ reads (Exp.ofList es)
  | .prob a b p q => z ∉ reads a ∧ z ∉ reads b ∧ p.avoids z ∧ q.avoids z

/-! ### Making a choice deterministic -/

/-- `2³¹ – 1`, the Lehmer generator's modulus. -/
def modulus : ℤ := 2147483647

/-- One step of the generator, `16807 z mod (2³¹ – 1)` by Schrage's method:
`16807 (z mod 127773) – 2836 (z div 127773)`, which is the step or the step less
the modulus; every value along the way fits in 32 bits. -/
def next (z : ℕ) : Exp :=
  .bin .sub (.bin .mul (.lit (.int 16807)) (.bin .mod (.var z) (.lit (.int 127773))))
    (.bin .mul (.lit (.int 2836)) (.bin .div (.var z) (.lit (.int 127773))))

/-- Schrage's correction: add the modulus back when the step went below `1`. -/
def fix (z : ℕ) : Stmt :=
  .cond (.bin .lt (.var z) (.lit (.int 1))) (.assign z (.bin .add (.var z) (.lit (.int modulus)))) .ok

/-- The coin: `z mod b < a`. -/
def coin (z : ℕ) (a b : Exp) : Exp := .bin .lt (.bin .mod (.var z) b) a

/-- **The deterministic program**: each `if a/b then P else Q fi` advances the
seed in `z` and takes `P` when `z mod b < a`. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.det (z : ℕ) : Stmt → Stmt
  | .prob a b p q => .seq (.assign z (next z)) (.seq (fix z) (.cond (coin z a b) (p.det z) (q.det z)))
  | .seq p q => .seq (p.det z) (q.det z)
  | .cond c p q => .cond c (p.det z) (q.det z)
  | .loop c p => .loop c (p.det z)
  | .scope x e p => .scope x e (p.det z)
  | .choice p q => .choice (p.det z) (q.det z)
  | p => p

/-- The statements `det` leaves alone and the compiler's execution (`SEval`) does
not run: those of a network, and backtracking's `ensure`. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.leaf : Stmt → Bool
  | .tick | .send _ _ | .recv _ _ | .ret | .restore _ _ | .check _ _ | .ensure _ => true
  | _ => false

/-- What a statement becomes on the way to its deterministic version: the
statement itself made deterministic, or a choice part way through, after the
seed has moved on. -/
inductive Des (z : ℕ) : Stmt → Stmt → Prop
  | ok : Des z .ok .ok
  | assign {x e} : Des z (.assign x e) (.assign x e)
  | seq {p q p' q'} : Des z p p' → Des z q q' → Des z (.seq p q) (.seq p' q')
  | cond {c p q p' q'} : Des z p p' → Des z q q' → Des z (.cond c p q) (.cond c p' q')
  | loop {c p p'} : Des z p p' → Des z (.loop c p) (.loop c p')
  | call {k} : Des z (.call k) (.call k)
  | scope {x e p p'} : Des z p p' → Des z (.scope x e p) (.scope x e p')
  | store {x i e} : Des z (.store x i e) (.store x i e)
  | fill {x es} : Des z (.fill x es) (.fill x es)
  | choice {p q p' q'} : Des z p p' → Des z q q' → Des z (.choice p q) (.choice p' q')
  | leaf {p} : p.leaf = true → Des z p p
  | probA {a b p q p' q'} : Des z p p' → Des z q q' →
      Des z (.prob a b p q) (.seq (.assign z (next z)) (.seq (fix z) (.cond (coin z a b) p' q')))
  | probB {a b p q p' q'} : Des z p p' → Des z q q' →
      Des z (.prob a b p q) (.seq (fix z) (.cond (coin z a b) p' q'))
  | probC {a b p q p' q'} : Des z p p' → Des z q q' →
      Des z (.prob a b p q) (.cond (coin z a b) p' q')

theorem des_det (z : ℕ) : ∀ p : Stmt, Des z p (p.det z)
  | .ok => .ok
  | .assign _ _ => .assign
  | .seq p q => .seq (des_det z p) (des_det z q)
  | .cond _ p q => .cond (des_det z p) (des_det z q)
  | .loop _ p => .loop (des_det z p)
  | .call _ => .call
  | .scope _ _ p => .scope (des_det z p)
  | .store _ _ _ => .store
  | .fill _ _ => .fill
  | .prob _ _ p q => .probA (des_det z p) (des_det z q)
  | .choice p q => .choice (des_det z p) (des_det z q)
  | .tick => .leaf rfl
  | .send _ _ => .leaf rfl
  | .recv _ _ => .leaf rfl
  | .ret => .leaf rfl
  | .restore _ _ => .leaf rfl
  | .check _ _ => .leaf rfl
  | .ensure _ => .leaf rfl

/-- Statements that only move the seed on. -/
inductive SeedOnly (z : ℕ) : Stmt → Prop
  | ok : SeedOnly z .ok
  | asg {e} : SeedOnly z (.assign z e)
  | cond {c p q} : SeedOnly z p → SeedOnly z q → SeedOnly z (.cond c p q)

theorem seedOnly_fix (z : ℕ) : SeedOnly z (fix z) := .cond .asg .ok

/-! ### The coin -/

theorem coin_parts {L : Layout} {s : St} {z : ℕ} {a b : Exp} (hf : Fits L s (coin z a b)) :
    ∃ ka kb kz, a.eval s = .int ka ∧ b.eval s = .int kb ∧ s z = .int kz ∧ 0 < kb ∧
      (coin z a b).eval s = .bool (decide (kz.fmod kb < ka)) := by
  simp only [coin, Fits] at hf
  obtain ⟨⟨-, -, ⟨kz, hz, -⟩, ⟨kb, hb, -⟩, hpos, -⟩, -, -, ⟨ka, ha, -⟩⟩ := hf
  simp only [Exp.eval] at hz
  rw [hb, Value.toInt_int] at hpos
  exact ⟨ka, kb, kz, ha, hb, hz, hpos, by simp [coin, Exp.eval, BinOp.apply, hz, hb, ha]⟩

/-- Heads only when the first branch has a chance. -/
theorem coin_true {L : Layout} {s : St} {z : ℕ} {a b : Exp} (hf : Fits L s (coin z a b))
    (hc : (coin z a b).eval s = .bool true) : 0 < ratio a b s := by
  obtain ⟨ka, kb, kz, ha, hb, -, hpos, he⟩ := coin_parts hf
  rw [he] at hc
  have hlt : kz.fmod kb < ka := by simpa using hc
  have := Int.fmod_nonneg_of_pos kz hpos
  unfold ratio; rw [ha, hb]
  simp only [Value.toInt_int]
  exact div_pos (by exact_mod_cast (show (0 : ℤ) < ka by omega)) (by exact_mod_cast hpos)

/-- Tails only when the second branch has a chance. -/
theorem coin_false {L : Layout} {s : St} {z : ℕ} {a b : Exp} (hf : Fits L s (coin z a b))
    (hc : (coin z a b).eval s = .bool false) : ratio a b s < 1 := by
  obtain ⟨ka, kb, kz, ha, hb, -, hpos, he⟩ := coin_parts hf
  rw [he] at hc
  have hle : ka ≤ kz.fmod kb := by simpa using hc
  have := Int.fmod_lt_of_pos kz hpos
  unfold ratio; rw [ha, hb]
  simp only [Value.toInt_int]
  rw [div_lt_one₀ (by exact_mod_cast hpos)]
  exact_mod_cast (show ka < kb by omega)

theorem ratio_agree {z : ℕ} {s t : St} {a b : Exp} (h : Agree z s t) (ha : z ∉ reads a)
    (hb : z ∉ reads b) : ratio a b s = ratio a b t := by
  unfold ratio; rw [eval_agree h a ha, eval_agree h b hb]

/-! ### Soundness -/

/-- The original program's named statements, as the interpreter's definitions. -/
@[instance_reducible] def envOf (Od : ℕ → Stmt) : Defs ℕ Value := ⟨fun k => (Od k).toProg⟩

/-- **The deterministic program computes what the original may**: every 32-bit
execution of `p.det z`, with the named statements made deterministic too, ends
in a state the language's execution of `p` reaches from any state agreeing but
for the seed — agreeing but for the seed. (And statements that only move the
seed change nothing else.) -/
theorem det_sound {L : Layout} {z : ℕ} (Od : ℕ → Stmt) (hdefs : ∀ k, L.defs k = (Od k).det z)
    (hav : ∀ k, (Od k).avoids z) {d : ℕ} {D : Stmt} {s t : St} (h : SEval L d D s t) :
    (∀ O, Des z O D → O.avoids z → ∀ s₀, Agree z s s₀ →
      ∃ t₀, @Eval ℕ Value (envOf Od) _ O.toProg s₀ t₀ ∧ Agree z t t₀) ∧
    (SeedOnly z D → Agree z s t) := by
  let _ := envOf Od
  induction h with
  | ok =>
    refine ⟨fun O hD _ s₀ hs => ?_, fun _ => fun _ _ => rfl⟩
    cases hD with
    | ok => exact ⟨s₀, .ok, hs⟩
    | leaf hl => simp [Stmt.leaf] at hl
  | @assign d x e s hx ha hf =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => ?_⟩
    · cases hD with
      | assign =>
        obtain ⟨-, hre⟩ := hO
        refine ⟨_, .assign, ?_⟩
        rw [eval_agree hs e hre]; exact hs.update _
      | leaf hl => simp [Stmt.leaf] at hl
    · cases hso with
      | asg => exact fun y hy => by simp [Function.update_of_ne hy]
  | seq h₁ h₂ ih₁ ih₂ =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => by cases hso⟩
    cases hD with
    | seq hp hq =>
      obtain ⟨t₁, e₁, a₁⟩ := ih₁.1 _ hp hO.1 s₀ hs
      obtain ⟨t₀, e₂, a₂⟩ := ih₂.1 _ hq hO.2 t₁ a₁
      exact ⟨t₀, .seq e₁ e₂, a₂⟩
    | probA hp hq => exact ih₂.1 _ (.probB hp hq) hO s₀ ((ih₁.2 .asg).symm.trans hs)
    | probB hp hq => exact ih₂.1 _ (.probC hp hq) hO s₀ ((ih₁.2 (seedOnly_fix z)).symm.trans hs)
    | leaf hl => simp [Stmt.leaf] at hl
  | @condT d c p q s t hf hc _ ih =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => ?_⟩
    · cases hD with
      | cond hp _ =>
        obtain ⟨hrc, hO₁, -⟩ := hO
        obtain ⟨t₀, e, a⟩ := ih.1 _ hp hO₁ s₀ hs
        exact ⟨t₀, .condTrue (by simp [Exp.test, ← eval_agree hs c hrc, hc]) e, a⟩
      | @probC a b _ _ _ _ hp _ =>
        obtain ⟨hra, hrb, hO₁, -⟩ := hO
        obtain ⟨t₀, e, ag⟩ := ih.1 _ hp hO₁ s₀ hs
        exact ⟨t₀, .probLeft (by rw [← ratio_agree hs hra hrb]; exact coin_true hf hc) e, ag⟩
      | leaf hl => simp [Stmt.leaf] at hl
    · cases hso with
      | cond h₁ _ => exact ih.2 h₁
  | @condF d c p q s t hf hc _ ih =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => ?_⟩
    · cases hD with
      | cond _ hq =>
        obtain ⟨hrc, -, hO₂⟩ := hO
        obtain ⟨t₀, e, a⟩ := ih.1 _ hq hO₂ s₀ hs
        exact ⟨t₀, .condFalse (by simp [Exp.test, ← eval_agree hs c hrc, hc]) e, a⟩
      | @probC a b _ _ _ _ _ hq =>
        obtain ⟨hra, hrb, -, hO₂⟩ := hO
        obtain ⟨t₀, e, ag⟩ := ih.1 _ hq hO₂ s₀ hs
        exact ⟨t₀, .probRight (by rw [← ratio_agree hs hra hrb]; exact coin_false hf hc) e, ag⟩
      | leaf hl => simp [Stmt.leaf] at hl
    · cases hso with
      | cond _ h₂ => exact ih.2 h₂
  | @loopT d c p s t u hf hc _ _ ih₁ ih₂ =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => by cases hso⟩
    cases hD with
    | loop hp =>
      obtain ⟨hrc, hO₁⟩ := hO
      obtain ⟨t₁, e₁, a₁⟩ := ih₁.1 _ hp hO₁ s₀ hs
      obtain ⟨t₀, e₂, a₂⟩ := ih₂.1 _ (.loop hp) ⟨hrc, hO₁⟩ t₁ a₁
      exact ⟨t₀, .whileTrue (by simp [Exp.test, ← eval_agree hs c hrc, hc]) e₁ e₂, a₂⟩
    | leaf hl => simp [Stmt.leaf] at hl
  | @loopF d c p s hf hc =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => by cases hso⟩
    cases hD with
    | loop _ =>
      exact ⟨s₀, .whileFalse (by simp [Exp.test, ← eval_agree hs c hO.1, hc]), hs⟩
    | leaf hl => simp [Stmt.leaf] at hl
  | @call d k s t _ _ _ ih =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => by cases hso⟩
    cases hD with
    | call =>
      obtain ⟨t₀, e, a⟩ := ih.1 (Od k) (by rw [hdefs k]; exact des_det z _) (hav k) s₀ hs
      exact ⟨t₀, .call e, a⟩
    | leaf hl => simp [Stmt.leaf] at hl
  | @scope d x e p s t _ _ _ _ _ ih =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => by cases hso⟩
    cases hD with
    | scope hp =>
      obtain ⟨hxz, hre, hO₁⟩ := hO
      have hs' : Agree z (Function.update s x (e.eval s)) (Function.update s₀ x (e.eval s₀)) := by
        rw [eval_agree hs e hre]; exact hs.update _
      obtain ⟨t₀, ev, a⟩ := ih.1 _ hp hO₁ _ hs'
      refine ⟨_, .newLocal ev, ?_⟩
      rw [hs x hxz]; exact a.update _
    | leaf hl => simp [Stmt.leaf] at hl
  | @store d x i e s _ _ =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => by cases hso⟩
    cases hD with
    | store =>
      obtain ⟨hxz, hri, hre⟩ := hO
      refine ⟨_, .assign, ?_⟩
      simp only [List.map]
      rw [← hs x hxz, ← eval_agree hs i hri, ← eval_agree hs e hre]; exact hs.update _
    | leaf hl => simp [Stmt.leaf] at hl
  | @fill d x a₀ es s vs _ _ _ _ =>
    refine ⟨fun O hD hO s₀ hs => ?_, fun hso => by cases hso⟩
    cases hD with
    | fill =>
      obtain ⟨-, hre⟩ := hO
      refine ⟨_, .assign, ?_⟩
      rw [← eval_agree hs _ hre]; exact hs.update _
    | leaf hl => simp [Stmt.leaf] at hl

/-- **A program with probabilistic choices, run deterministically**: whatever
the deterministic program computes in 32 bits, the original may compute, but
for the seed. With `CompileB4.load_correct`, this is what the machine computes. -/
theorem det_eval {L : Layout} {z : ℕ} (Od : ℕ → Stmt) (hdefs : ∀ k, L.defs k = (Od k).det z)
    (hav : ∀ k, (Od k).avoids z) {p : Stmt} (hp : p.avoids z) {d : ℕ} {s t : St}
    (h : SEval L d (p.det z) s t) :
    ∃ t₀, @Eval ℕ Value (envOf Od) _ p.toProg s t₀ ∧ ∀ y, y ≠ z → t y = t₀ y :=
  (det_sound Od hdefs hav h).1 p (des_det z p) hp s (fun _ _ => rfl)

end LaPToP.ProgramTheory.CompileProb
