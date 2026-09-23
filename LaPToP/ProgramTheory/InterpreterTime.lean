import LaPToP.ProgramTheory.Interpreter
import LaPToP.ProgramTheory.Time

/-!
# The interpreter with a clock

`LaPToP.ProgramTheory.Interpreter` runs programs on a state of memory variables
alone. Without a clock two of the notations are invisible: `t:= t+1` does
nothing observable, and `assert b` cannot be told from `ensure b`, because the
difference between them — a false assertion prints a message and waits until
`∞`, which is implementable, where a false `ensure` is not implementable at all
— is a statement about time. This module gives the same syntax a state with a
time variable and tells them apart.

## The model

`TState Var Val` is the memory of the untimed interpreter together with a clock
`t : ℕ∞` (`⊤ = ∞`), as in Section 4.2. Time is not charged automatically: the
programmer advances it with `Prog.tick`, exactly as the book writes `t:= t+1`,
and the loop of Section 5.2 takes time only if its body ticks. `denoteT` is the
timed specification of a program and `runT` its fuelled interpreter; `EvalT` is
the fuel-free execution relation, equal to `denoteT` as in the untimed module.

Two facts hold of every program: time does not decrease (`time_le_of_denoteT`),
and `∞` is absorbing (`time_top_of_denoteT`) — once a computation has waited
forever nothing afterwards happens in finite time.

## The untimed interpreter is the finite-time part of this one

`denote_iff_denoteT` is the theorem this module exists for: from a state at
finite time, the behaviours of `p` that the untimed interpreter has are exactly
the timed behaviours of `p` that end in finite time. So the untimed development
is not a rival account but a projection of this one, and the identification of
`assert` with `ensure` that it makes is exactly right for an observer without a
clock — which is what `Assertions.assert_finite` says of a single assertion, here
proved of every program.

With the clock, the two part company: `denoteT (.assert b)` is implementable
with nondecreasing time and its run always succeeds, ending at `t = ∞` when `b`
fails, while `denoteT (.ensure b)` has no poststate there at all.

## Honest scope

The memory of a false assertion is left as it was; the book's `Assertions.assert`
says nothing about the memory variables, so what is implemented here refines it
(`refines_assertSpec`), and the error message is still not modelled. Time is
charged only where the program says `tick`, so nothing here claims a cost model
for the other notations. The loop with a ticking body has exactly the shape of
`LoopBridge.whileRun`, but the axioms of Section 6.1.1 are stated over the
concrete state `ZS` of `LaPToP.RecursiveDefinition`; generalizing them to an
arbitrary clocked state, and so restating that bridge over `Prog`, is left.
-/

namespace LaPToP.ProgramTheory.Interpreter

universe u v

namespace Timed

variable {Var : Type u} {Val : Type v}

/-! ### A state with a clock -/

/-- The interpreter's state together with a time variable (aPToP §4.2). -/
@[ext]
structure TState (Var : Type u) (Val : Type v) where
  /-- The memory variables. -/
  mem : Spec.State Var Val
  /-- The time. -/
  t : ℕ∞

variable [DecidableEq Var]

/-! ### The timed denotation -/

/-- The timed specification of a program: the memory changes as in the untimed
interpreter, `tick` advances the clock, and a failed assertion waits until `∞`. -/
def denoteT : Prog Var Val → Spec (TState Var Val)
  | .ok => Spec.ok
  | .assign x e => fun st st' => st' = ⟨Function.update st.mem x (e st.mem), st.t⟩
  | .seq p q => Spec.seq (denoteT p) (denoteT q)
  | .cond b p q => Spec.cond (fun st => b st.mem = true) (denoteT p) (denoteT q)
  | .whileDo b p => Spec.whileRel (fun st => b st.mem = true) (denoteT p)
  | .newLocal x e p => fun st st' => ∃ u : TState Var Val,
      denoteT p ⟨Function.update st.mem x (e st.mem), st.t⟩ u ∧
        st' = ⟨Function.update u.mem x (st.mem x), u.t⟩
  | .assignAt x e => fun st st' => st' = ⟨Function.update st.mem (x st.mem) (e st.mem), st.t⟩
  | .ensure b => fun st st' => b st.mem = true ∧ st' = st
  | .or p q => Spec.or (denoteT p) (denoteT q)
  | .tick => fun st st' => st' = ⟨st.mem, st.t + 1⟩
  | .assert b =>
      Spec.cond (fun st => b st.mem = true) Spec.ok fun st st' => st' = ⟨st.mem, ⊤⟩

@[simp] theorem denoteT_ok : denoteT (Prog.ok : Prog Var Val) = Spec.ok := rfl

@[simp] theorem denoteT_assign (x : Var) (e : Spec.State Var Val → Val) :
    denoteT (.assign x e) =
      fun st st' => st' = ⟨Function.update st.mem x (e st.mem), st.t⟩ := rfl

@[simp] theorem denoteT_seq (p q : Prog Var Val) :
    denoteT (.seq p q) = Spec.seq (denoteT p) (denoteT q) := rfl

@[simp] theorem denoteT_cond (b : Spec.State Var Val → Bool) (p q : Prog Var Val) :
    denoteT (.cond b p q) =
      Spec.cond (fun st => b st.mem = true) (denoteT p) (denoteT q) := rfl

@[simp] theorem denoteT_whileDo (b : Spec.State Var Val → Bool) (p : Prog Var Val) :
    denoteT (.whileDo b p) = Spec.whileRel (fun st => b st.mem = true) (denoteT p) := rfl

@[simp] theorem denoteT_assignAt (x : Spec.State Var Val → Var)
    (e : Spec.State Var Val → Val) :
    denoteT (.assignAt x e) =
      fun st st' => st' = ⟨Function.update st.mem (x st.mem) (e st.mem), st.t⟩ := rfl

@[simp] theorem denoteT_ensure (b : Spec.State Var Val → Bool) :
    denoteT (.ensure b) = fun st st' => b st.mem = true ∧ st' = st := rfl

@[simp] theorem denoteT_or (p q : Prog Var Val) :
    denoteT (.or p q) = Spec.or (denoteT p) (denoteT q) := rfl

@[simp] theorem denoteT_tick :
    denoteT (Prog.tick : Prog Var Val) = fun st st' => st' = ⟨st.mem, st.t + 1⟩ := rfl

@[simp] theorem denoteT_assert (b : Spec.State Var Val → Bool) :
    denoteT (.assert b) =
      Spec.cond (fun st => b st.mem = true) Spec.ok
        (fun st st' => st' = ⟨st.mem, ⊤⟩) := rfl

/-! ### Time does not decrease -/

/-- Time does not decrease: `t′ ≥ t` for every behaviour of every program. This
is the first of the three axioms of Section 6.1.1, holding here of the whole
language. -/
theorem time_le_of_denoteT : ∀ (p : Prog Var Val) {st st' : TState Var Val},
    denoteT p st st' → st.t ≤ st'.t := by
  intro p
  induction p with
  | ok => rintro st st' rfl; exact le_rfl
  | assign x e => rintro st st' rfl; exact le_rfl
  | seq p q ihp ihq =>
    rintro st st' ⟨u, hp, hq⟩
    exact le_trans (ihp hp) (ihq hq)
  | cond b p q ihp ihq =>
    rintro st st' (⟨-, h⟩ | ⟨-, h⟩)
    · exact ihp h
    · exact ihq h
  | whileDo b p ihp =>
    intro st st' h
    replace h : Spec.whileRel (fun st : TState Var Val => b st.mem = true) (denoteT p) st st' := h
    induction h with
    | exit => exact le_rfl
    | step _ hR _ ih => exact le_trans (ihp hR) ih
  | newLocal x e p ihp =>
    rintro st st' ⟨u, hp, rfl⟩
    have h := ihp hp
    exact h
  | assignAt x e => rintro st st' rfl; exact le_rfl
  | ensure b => rintro st st' ⟨-, rfl⟩; exact le_rfl
  | or p q ihp ihq =>
    rintro st st' (h | h)
    · exact ihp h
    · exact ihq h
  | tick => rintro st st' rfl; exact le_self_add
  | assert b =>
    rintro st st' (⟨-, h⟩ | ⟨-, rfl⟩)
    · rw [show st' = st from h]
    · exact le_top

/-- `∞` is absorbing: after a computation that never finished, nothing finishes.
-/
theorem time_top_of_denoteT (p : Prog Var Val) {st st' : TState Var Val}
    (h : denoteT p st st') (ht : st.t = ⊤) : st'.t = ⊤ :=
  top_le_iff.mp (ht ▸ time_le_of_denoteT p h)

/-- A behaviour that ends in finite time started in finite time. -/
theorem time_ne_top_of_denoteT (p : Prog Var Val) {st st' : TState Var Val}
    (h : denoteT p st st') (ht : st'.t ≠ ⊤) : st.t ≠ ⊤ :=
  fun htop => ht (time_top_of_denoteT p h htop)

/-! ### The fuelled timed interpreter -/

/-- `runT fuel p st` executes `p` from the timed state `st`. -/
def runT : ℕ → Prog Var Val → TState Var Val → Option (TState Var Val)
  | 0, _, _ => none
  | _ + 1, .ok, st => some st
  | _ + 1, .assign x e, st => some ⟨Function.update st.mem x (e st.mem), st.t⟩
  | n + 1, .seq p q, st => (runT n p st).bind (runT n q)
  | n + 1, .cond b p q, st => if b st.mem then runT n p st else runT n q st
  | n + 1, .whileDo b p, st =>
      if b st.mem then (runT n p st).bind (runT n (.whileDo b p)) else some st
  | n + 1, .newLocal x e p, st =>
      (runT n p ⟨Function.update st.mem x (e st.mem), st.t⟩).map
        fun u => ⟨Function.update u.mem x (st.mem x), u.t⟩
  | _ + 1, .assignAt x e, st => some ⟨Function.update st.mem (x st.mem) (e st.mem), st.t⟩
  | _ + 1, .ensure b, st => if b st.mem then some st else none
  | n + 1, .or p _q, st => runT n p st
  | _ + 1, .tick, st => some ⟨st.mem, st.t + 1⟩
  | _ + 1, .assert b, st => if b st.mem then some st else some ⟨st.mem, ⊤⟩

@[simp] theorem runT_zero (p : Prog Var Val) (st : TState Var Val) : runT 0 p st = none := by
  cases p <;> rfl

@[simp] theorem runT_ok (n : ℕ) (st : TState Var Val) : runT (n + 1) .ok st = some st := rfl

@[simp] theorem runT_assign (n : ℕ) (x : Var) (e : Spec.State Var Val → Val)
    (st : TState Var Val) :
    runT (n + 1) (.assign x e) st = some ⟨Function.update st.mem x (e st.mem), st.t⟩ := rfl

@[simp] theorem runT_seq (n : ℕ) (p q : Prog Var Val) (st : TState Var Val) :
    runT (n + 1) (.seq p q) st = (runT n p st).bind (runT n q) := rfl

@[simp] theorem runT_cond (n : ℕ) (b : Spec.State Var Val → Bool) (p q : Prog Var Val)
    (st : TState Var Val) :
    runT (n + 1) (.cond b p q) st = if b st.mem then runT n p st else runT n q st := rfl

@[simp] theorem runT_whileDo (n : ℕ) (b : Spec.State Var Val → Bool) (p : Prog Var Val)
    (st : TState Var Val) :
    runT (n + 1) (.whileDo b p) st =
      if b st.mem then (runT n p st).bind (runT n (.whileDo b p)) else some st := rfl

@[simp] theorem runT_newLocal (n : ℕ) (x : Var) (e : Spec.State Var Val → Val)
    (p : Prog Var Val) (st : TState Var Val) :
    runT (n + 1) (.newLocal x e p) st =
      (runT n p ⟨Function.update st.mem x (e st.mem), st.t⟩).map
        fun u => ⟨Function.update u.mem x (st.mem x), u.t⟩ := rfl

@[simp] theorem runT_assignAt (n : ℕ) (x : Spec.State Var Val → Var)
    (e : Spec.State Var Val → Val) (st : TState Var Val) :
    runT (n + 1) (.assignAt x e) st =
      some ⟨Function.update st.mem (x st.mem) (e st.mem), st.t⟩ := rfl

@[simp] theorem runT_ensure (n : ℕ) (b : Spec.State Var Val → Bool) (st : TState Var Val) :
    runT (n + 1) (.ensure b) st = if b st.mem then some st else none := rfl

@[simp] theorem runT_or (n : ℕ) (p q : Prog Var Val) (st : TState Var Val) :
    runT (n + 1) (.or p q) st = runT n p st := rfl

@[simp] theorem runT_tick (n : ℕ) (st : TState Var Val) :
    runT (n + 1) (Prog.tick : Prog Var Val) st = some ⟨st.mem, st.t + 1⟩ := rfl

@[simp] theorem runT_assert (n : ℕ) (b : Spec.State Var Val → Bool) (st : TState Var Val) :
    runT (n + 1) (.assert b) st = if b st.mem then some st else some ⟨st.mem, ⊤⟩ := rfl

/-- More fuel never spoils a successful timed run. -/
theorem runT_le : ∀ {f g : ℕ} {p : Prog Var Val} {st st' : TState Var Val},
    runT f p st = some st' → f ≤ g → runT g p st = some st' := by
  intro f
  induction f with
  | zero => intro g p st st' h _; simp at h
  | succ n ih =>
    intro g p st st' h hle
    obtain ⟨m, rfl⟩ : ∃ m, g = m + 1 := ⟨g - 1, by omega⟩
    have hnm : n ≤ m := by omega
    cases p with
    | ok => simpa using h
    | assign x e => simpa using h
    | seq p q =>
      simp only [runT_seq] at h ⊢
      cases hp : runT n p st with
      | none => rw [hp] at h; simp at h
      | some u =>
        rw [hp] at h
        simp only [Option.bind_some] at h
        rw [ih hp hnm]
        simpa using ih h hnm
    | cond b p q =>
      simp only [runT_cond] at h ⊢
      split_ifs at h ⊢ with hb
      · exact ih h hnm
      · exact ih h hnm
    | whileDo b p =>
      simp only [runT_whileDo] at h ⊢
      split_ifs at h ⊢ with hb
      · cases hp : runT n p st with
        | none => rw [hp] at h; simp at h
        | some u =>
          rw [hp] at h
          simp only [Option.bind_some] at h
          rw [ih hp hnm]
          simpa using ih h hnm
      · exact h
    | newLocal x e p =>
      simp only [runT_newLocal] at h ⊢
      cases hp : runT n p ⟨Function.update st.mem x (e st.mem), st.t⟩ with
      | none => rw [hp] at h; simp at h
      | some u => rw [hp] at h; rw [ih hp hnm]; exact h
    | assignAt x e => simpa using h
    | ensure b =>
      simp only [runT_ensure] at h ⊢
      split_ifs at h ⊢ with hb
      exact h
    | or p q => simp only [runT_or] at h ⊢; exact ih h hnm
    | tick => simpa using h
    | assert b =>
      simp only [runT_assert] at h ⊢
      split_ifs at h ⊢ with hb <;> exact h

/-- **Soundness**: a successful timed run satisfies the timed specification. -/
theorem denoteT_of_runT : ∀ {f : ℕ} {p : Prog Var Val} {st st' : TState Var Val},
    runT f p st = some st' → denoteT p st st' := by
  intro f
  induction f with
  | zero => intro p st st' h; simp at h
  | succ n ih =>
    intro p st st' h
    cases p with
    | ok => simp only [runT_ok, Option.some.injEq] at h; exact h.symm
    | assign x e => simp only [runT_assign, Option.some.injEq] at h; exact h.symm
    | seq p q =>
      simp only [runT_seq] at h
      cases hp : runT n p st with
      | none => rw [hp] at h; simp at h
      | some u =>
        rw [hp] at h
        simp only [Option.bind_some] at h
        exact ⟨u, ih hp, ih h⟩
    | cond b p q =>
      simp only [runT_cond] at h
      split_ifs at h with hb
      · exact Or.inl ⟨hb, ih h⟩
      · exact Or.inr ⟨hb, ih h⟩
    | whileDo b p =>
      simp only [runT_whileDo] at h
      split_ifs at h with hb
      · cases hp : runT n p st with
        | none => rw [hp] at h; simp at h
        | some u =>
          rw [hp] at h
          simp only [Option.bind_some] at h
          exact Spec.whileRel.step hb (ih hp) (ih h)
      · simp only [Option.some.injEq] at h
        subst h
        exact Spec.whileRel.exit hb
    | newLocal x e p =>
      simp only [runT_newLocal] at h
      cases hp : runT n p ⟨Function.update st.mem x (e st.mem), st.t⟩ with
      | none => rw [hp] at h; simp at h
      | some u =>
        rw [hp] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨u, ih hp, h.symm⟩
    | assignAt x e => simp only [runT_assignAt, Option.some.injEq] at h; exact h.symm
    | ensure b =>
      simp only [runT_ensure] at h
      split_ifs at h with hb
      simp only [Option.some.injEq] at h
      exact ⟨hb, h.symm⟩
    | or p q => simp only [runT_or] at h; exact Or.inl (ih h)
    | tick => simp only [runT_tick, Option.some.injEq] at h; exact h.symm
    | assert b =>
      simp only [runT_assert] at h
      split_ifs at h with hb
      · simp only [Option.some.injEq] at h
        exact Or.inl ⟨hb, h.symm⟩
      · simp only [Option.some.injEq] at h
        exact Or.inr ⟨hb, h.symm⟩

/-- **Completeness on the deterministic fragment**: every timed behaviour of a
program without a choice is a run with enough fuel. -/
theorem exists_runT_of_denoteT : ∀ {p : Prog Var Val}, Det p →
    ∀ {st st' : TState Var Val}, denoteT p st st' → ∃ f, runT f p st = some st' := by
  intro p
  induction p with
  | ok => intro _ st st' h; exact ⟨1, by rw [runT_ok, show st' = st from h]⟩
  | assign x e => intro _ st st' h; exact ⟨1, by rw [runT_assign, show st' = _ from h]⟩
  | seq p q ihp ihq =>
    intro hd st st' h
    obtain ⟨u, hp, hq⟩ : ∃ u, denoteT p st u ∧ denoteT q u st' := h
    obtain ⟨f₁, h₁⟩ := ihp hd.1 hp
    obtain ⟨f₂, h₂⟩ := ihq hd.2 hq
    refine ⟨max f₁ f₂ + 1, ?_⟩
    rw [runT_seq, runT_le h₁ (le_max_left f₁ f₂), Option.bind_some]
    exact runT_le h₂ (le_max_right f₁ f₂)
  | cond b p q ihp ihq =>
    intro hd st st' h
    obtain ⟨hb, h⟩ | ⟨hb, h⟩ :
        ((b st.mem = true) ∧ denoteT p st st') ∨ (¬ (b st.mem = true) ∧ denoteT q st st') := h
    · obtain ⟨f, hf⟩ := ihp hd.1 h
      exact ⟨f + 1, by rw [runT_cond, ite_eq_left hb]; exact hf⟩
    · obtain ⟨f, hf⟩ := ihq hd.2 h
      exact ⟨f + 1, by rw [runT_cond, ite_eq_right hb]; exact hf⟩
  | whileDo b p ihp =>
    intro hd st st' h
    replace h : Spec.whileRel (fun st : TState Var Val => b st.mem = true) (denoteT p) st st' := h
    induction h with
    | exit hb => exact ⟨1, by rw [runT_whileDo, ite_eq_right hb]⟩
    | step hb hR _ ihLoop =>
      obtain ⟨f₁, h₁⟩ := ihp hd hR
      obtain ⟨f₂, h₂⟩ := ihLoop
      refine ⟨max f₁ f₂ + 1, ?_⟩
      rw [runT_whileDo, ite_eq_left hb, runT_le h₁ (le_max_left f₁ f₂), Option.bind_some]
      exact runT_le h₂ (le_max_right f₁ f₂)
  | newLocal x e p ihp =>
    intro hd st st' h
    obtain ⟨u, hp, hst⟩ : ∃ u, denoteT p ⟨Function.update st.mem x (e st.mem), st.t⟩ u ∧
        st' = ⟨Function.update u.mem x (st.mem x), u.t⟩ := h
    obtain ⟨f, hf⟩ := ihp hd hp
    exact ⟨f + 1, by rw [runT_newLocal, hf, Option.map_some, hst]⟩
  | assignAt x e => intro _ st st' h; exact ⟨1, by rw [runT_assignAt, show st' = _ from h]⟩
  | ensure b =>
    intro _ st st' h
    obtain ⟨hb, hok⟩ : (b st.mem = true) ∧ st' = st := h
    exact ⟨1, by rw [runT_ensure, ite_eq_left hb, hok]⟩
  | or p q _ _ => intro hd; exact hd.elim
  | tick => intro _ st st' h; exact ⟨1, by rw [runT_tick, show st' = _ from h]⟩
  | assert b =>
    intro _ st st' h
    obtain ⟨hb, hok⟩ | ⟨hb, hst⟩ :
        ((b st.mem = true) ∧ Spec.ok st st') ∨
          (¬ (b st.mem = true) ∧ st' = ⟨st.mem, ⊤⟩) := h
    · exact ⟨1, by rw [runT_assert, ite_eq_left hb, show st' = st from hok]⟩
    · exact ⟨1, by rw [runT_assert, ite_eq_right hb, hst]⟩

/-! ### Fuel-free timed execution -/

/-- `EvalT p st st'`: started in the timed state `st`, the program `p`
terminates in `st'`. The fuel-free account, as `Eval` is for the untimed
interpreter. -/
inductive EvalT : Prog Var Val → TState Var Val → TState Var Val → Prop
  /-- `ok`. -/
  | ok {st : TState Var Val} : EvalT .ok st st
  /-- `x:= e`, which takes no time. -/
  | assign {x : Var} {e : Spec.State Var Val → Val} {st : TState Var Val} :
      EvalT (.assign x e) st ⟨Function.update st.mem x (e st.mem), st.t⟩
  /-- `p. q`. -/
  | seq {p q : Prog Var Val} {st u st' : TState Var Val} :
      EvalT p st u → EvalT q u st' → EvalT (.seq p q) st st'
  /-- `if b then p else q` with `b` true. -/
  | condTrue {b : Spec.State Var Val → Bool} {p q : Prog Var Val} {st st' : TState Var Val}
      (hb : b st.mem = true) : EvalT p st st' → EvalT (.cond b p q) st st'
  /-- `if b then p else q` with `b` false. -/
  | condFalse {b : Spec.State Var Val → Bool} {p q : Prog Var Val} {st st' : TState Var Val}
      (hb : b st.mem = false) : EvalT q st st' → EvalT (.cond b p q) st st'
  /-- One iteration of a loop. -/
  | whileTrue {b : Spec.State Var Val → Bool} {p : Prog Var Val} {st u st' : TState Var Val}
      (hb : b st.mem = true) :
      EvalT p st u → EvalT (.whileDo b p) u st' → EvalT (.whileDo b p) st st'
  /-- A loop that exits. -/
  | whileFalse {b : Spec.State Var Val → Bool} {p : Prog Var Val} {st : TState Var Val}
      (hb : b st.mem = false) : EvalT (.whileDo b p) st st
  /-- A local declaration: the slot is borrowed and restored, the clock runs on. -/
  | newLocal {x : Var} {e : Spec.State Var Val → Val} {p : Prog Var Val}
      {st u : TState Var Val} :
      EvalT p ⟨Function.update st.mem x (e st.mem), st.t⟩ u →
        EvalT (.newLocal x e p) st ⟨Function.update u.mem x (st.mem x), u.t⟩
  /-- `A i:= e`. -/
  | assignAt {x : Spec.State Var Val → Var} {e : Spec.State Var Val → Val}
      {st : TState Var Val} :
      EvalT (.assignAt x e) st ⟨Function.update st.mem (x st.mem) (e st.mem), st.t⟩
  /-- `ensure b` with `b` true; with `b` false there is no poststate. -/
  | ensure {b : Spec.State Var Val → Bool} {st : TState Var Val} (hb : b st.mem = true) :
      EvalT (.ensure b) st st
  /-- The left branch of a choice. -/
  | orLeft {p q : Prog Var Val} {st st' : TState Var Val} :
      EvalT p st st' → EvalT (.or p q) st st'
  /-- The right branch of a choice. -/
  | orRight {p q : Prog Var Val} {st st' : TState Var Val} :
      EvalT q st st' → EvalT (.or p q) st st'
  /-- `t:= t+1`. -/
  | tick {st : TState Var Val} : EvalT (Prog.tick : Prog Var Val) st ⟨st.mem, st.t + 1⟩
  /-- `assert b` with `b` true is `ok`. -/
  | assertTrue {b : Spec.State Var Val → Bool} {st : TState Var Val} (hb : b st.mem = true) :
      EvalT (.assert b) st st
  /-- `assert b` with `b` false waits until `∞`. -/
  | assertFalse {b : Spec.State Var Val → Bool} {st : TState Var Val} (hb : b st.mem = false) :
      EvalT (.assert b) st ⟨st.mem, ⊤⟩

/-- Fuel-free timed execution is the timed specification. -/
theorem evalT_iff_denoteT {p : Prog Var Val} {st st' : TState Var Val} :
    EvalT p st st' ↔ denoteT p st st' := by
  constructor
  · intro h
    induction h with
    | ok => rfl
    | assign => rfl
    | seq _ _ ihp ihq => exact ⟨_, ihp, ihq⟩
    | condTrue hb _ ih => exact Or.inl ⟨hb, ih⟩
    | condFalse hb _ ih => exact Or.inr ⟨by simp [hb], ih⟩
    | whileTrue hb _ _ ihp ihw => exact Spec.whileRel.step hb ihp ihw
    | whileFalse hb => exact Spec.whileRel.exit (by simp [hb])
    | newLocal _ ih => exact ⟨_, ih, rfl⟩
    | assignAt => rfl
    | ensure hb => exact ⟨hb, rfl⟩
    | orLeft _ ih => exact Or.inl ih
    | orRight _ ih => exact Or.inr ih
    | tick => rfl
    | assertTrue hb => exact Or.inl ⟨hb, rfl⟩
    | assertFalse hb => exact Or.inr ⟨by simp [hb], rfl⟩
  · revert st st'
    induction p with
    | ok => intro st st' h; exact (show st' = st from h) ▸ .ok
    | assign x e => intro st st' h; exact (show st' = _ from h) ▸ .assign
    | seq p q ihp ihq =>
      intro st st' h
      obtain ⟨u, hp, hq⟩ : ∃ u, denoteT p st u ∧ denoteT q u st' := h
      exact .seq (ihp hp) (ihq hq)
    | cond b p q ihp ihq =>
      intro st st' h
      obtain ⟨hb, h⟩ | ⟨hb, h⟩ :
          ((b st.mem = true) ∧ denoteT p st st') ∨ (¬ (b st.mem = true) ∧ denoteT q st st') := h
      · exact .condTrue hb (ihp h)
      · exact .condFalse (by simpa using hb) (ihq h)
    | whileDo b p ihp =>
      intro st st' h
      replace h : Spec.whileRel (fun st : TState Var Val => b st.mem = true) (denoteT p) st st' := h
      induction h with
      | exit hb => exact .whileFalse (by simpa using hb)
      | step hb hR _ ihw => exact .whileTrue hb (ihp hR) ihw
    | newLocal x e p ihp =>
      intro st st' h
      obtain ⟨u, hp, hst⟩ : ∃ u, denoteT p ⟨Function.update st.mem x (e st.mem), st.t⟩ u ∧
          st' = ⟨Function.update u.mem x (st.mem x), u.t⟩ := h
      subst hst
      exact .newLocal (ihp hp)
    | assignAt x e => intro st st' h; exact (show st' = _ from h) ▸ .assignAt
    | ensure b =>
      intro st st' h
      obtain ⟨hb, hok⟩ : (b st.mem = true) ∧ st' = st := h
      subst hok
      exact .ensure hb
    | or p q ihp ihq =>
      intro st st' h
      exact h.elim (fun hp => .orLeft (ihp hp)) fun hq => .orRight (ihq hq)
    | tick => intro st st' h; exact (show st' = _ from h) ▸ .tick
    | assert b =>
      intro st st' h
      obtain ⟨hb, hok⟩ | ⟨hb, hst⟩ :
          ((b st.mem = true) ∧ Spec.ok st st') ∨
            (¬ (b st.mem = true) ∧ st' = ⟨st.mem, ⊤⟩) := h
      · rw [show st' = st from hok]; exact .assertTrue hb
      · exact hst ▸ .assertFalse (by simpa using hb)

/-! ### The untimed interpreter is what a finite-time observer sees -/

/-- **The projection theorem.** From a state at finite time, the behaviours the
untimed interpreter has are exactly the timed behaviours that end in finite
time. So the untimed development of `Interpreter` is not a rival account of the
same programs but this one with the clock forgotten, and the identification it
makes of `assert` with `ensure` is exactly right for an observer without a
clock. This is `Assertions.assert_finite` for every program instead of one
assertion. -/
theorem denote_iff_denoteT : ∀ (p : Prog Var Val) {s s' : Spec.State Var Val} {t : ℕ∞},
    t ≠ ⊤ → (denote p s s' ↔ ∃ t' : ℕ∞, t' ≠ ⊤ ∧ denoteT p ⟨s, t⟩ ⟨s', t'⟩) := by
  intro p
  induction p with
  | ok =>
    intro s s' t ht
    refine ⟨fun h => ⟨t, ht, by rw [show s' = s from h]; rfl⟩, ?_⟩
    rintro ⟨t', -, h⟩
    exact congrArg TState.mem h
  | assign x e =>
    intro s s' t ht
    refine ⟨fun h => ⟨t, ht, by rw [show s' = _ from h]; rfl⟩, ?_⟩
    rintro ⟨t', -, h⟩
    exact congrArg TState.mem h
  | seq p q ihp ihq =>
    intro s s' t ht
    constructor
    · rintro ⟨u, hp, hq⟩
      obtain ⟨tu, htu, hpT⟩ := (ihp ht).mp hp
      obtain ⟨t', ht', hqT⟩ := (ihq htu).mp hq
      exact ⟨t', ht', ⟨⟨u, tu⟩, hpT, hqT⟩⟩
    · rintro ⟨t', ht', ⟨u, hpT, hqT⟩⟩
      obtain ⟨um, ut⟩ := u
      have hu : ut ≠ ⊤ := time_ne_top_of_denoteT q hqT ht'
      exact ⟨um, (ihp ht).mpr ⟨ut, hu, hpT⟩, (ihq hu).mpr ⟨t', ht', hqT⟩⟩
  | cond b p q ihp ihq =>
    intro s s' t ht
    constructor
    · rintro (⟨hb, h⟩ | ⟨hb, h⟩)
      · obtain ⟨t', ht', hT⟩ := (ihp ht).mp h
        exact ⟨t', ht', Or.inl ⟨hb, hT⟩⟩
      · obtain ⟨t', ht', hT⟩ := (ihq ht).mp h
        exact ⟨t', ht', Or.inr ⟨hb, hT⟩⟩
    · rintro ⟨t', ht', (⟨hb, hT⟩ | ⟨hb, hT⟩)⟩
      · exact Or.inl ⟨hb, (ihp ht).mpr ⟨t', ht', hT⟩⟩
      · exact Or.inr ⟨hb, (ihq ht).mpr ⟨t', ht', hT⟩⟩
  | whileDo b p ihp =>
    intro s s' t ht
    constructor
    · intro h
      replace h : Spec.whileRel (fun s => b s = true) (denote p) s s' := h
      have key : ∀ {u u' : Spec.State Var Val},
          Spec.whileRel (fun s => b s = true) (denote p) u u' →
          ∀ (tu : ℕ∞), tu ≠ ⊤ → ∃ tu', tu' ≠ ⊤ ∧
            Spec.whileRel (fun st : TState Var Val => b st.mem = true) (denoteT p)
              ⟨u, tu⟩ ⟨u', tu'⟩ := by
        intro u u' hw
        induction hw with
        | exit hb => exact fun tu htu => ⟨tu, htu, Spec.whileRel.exit hb⟩
        | step hb hR _ ih =>
          intro tu htu
          obtain ⟨tm, htm, hRT⟩ := (ihp htu).mp hR
          obtain ⟨tu', htu', hwT⟩ := ih tm htm
          exact ⟨tu', htu', Spec.whileRel.step hb hRT hwT⟩
      exact key h t ht
    · rintro ⟨t', ht', hT⟩
      replace hT : Spec.whileRel (fun st : TState Var Val => b st.mem = true) (denoteT p)
          ⟨s, t⟩ ⟨s', t'⟩ := hT
      have key : ∀ {st st' : TState Var Val},
          Spec.whileRel (fun st : TState Var Val => b st.mem = true) (denoteT p) st st' →
          st.t ≠ ⊤ → st'.t ≠ ⊤ →
          Spec.whileRel (fun s => b s = true) (denote p) st.mem st'.mem := by
        intro st st' hw
        induction hw with
        | exit hb => intro _ _; exact Spec.whileRel.exit hb
        | @step st u st' hb hR hW ih =>
          intro hst hst'
          have hu : u.t ≠ ⊤ := time_ne_top_of_denoteT (.whileDo b p) hW hst'
          obtain ⟨um, ut⟩ := u
          exact Spec.whileRel.step hb ((ihp hst).mpr ⟨ut, hu, hR⟩) (ih hu hst')
      exact key hT ht ht'
  | newLocal x e p ihp =>
    intro s s' t ht
    constructor
    · rintro ⟨u, hp, hs⟩
      obtain ⟨tu, htu, hpT⟩ := (ihp ht).mp hp
      exact ⟨tu, htu, ⟨⟨u, tu⟩, hpT, by rw [hs]⟩⟩
    · rintro ⟨t', ht', ⟨u, hpT, hst⟩⟩
      obtain ⟨um, ut⟩ := u
      have hut : ut = t' := (congrArg TState.t hst).symm
      subst hut
      exact ⟨um, (ihp ht).mpr ⟨_, ht', hpT⟩, congrArg TState.mem hst⟩
  | assignAt x e =>
    intro s s' t ht
    refine ⟨fun h => ⟨t, ht, by rw [show s' = _ from h]; rfl⟩, ?_⟩
    rintro ⟨t', -, h⟩
    exact congrArg TState.mem h
  | ensure b =>
    intro s s' t ht
    constructor
    · rintro ⟨hb, hs⟩
      exact ⟨t, ht, hb, by rw [hs]⟩
    · rintro ⟨t', -, hb, h⟩
      exact ⟨hb, congrArg TState.mem h⟩
  | or p q ihp ihq =>
    intro s s' t ht
    constructor
    · rintro (h | h)
      · obtain ⟨t', ht', hT⟩ := (ihp ht).mp h
        exact ⟨t', ht', Or.inl hT⟩
      · obtain ⟨t', ht', hT⟩ := (ihq ht).mp h
        exact ⟨t', ht', Or.inr hT⟩
    · rintro ⟨t', ht', (hT | hT)⟩
      · exact Or.inl ((ihp ht).mpr ⟨t', ht', hT⟩)
      · exact Or.inr ((ihq ht).mpr ⟨t', ht', hT⟩)
  | tick =>
    intro s s' t ht
    constructor
    · intro h
      refine ⟨t + 1, ?_, by rw [show s' = s from h]; rfl⟩
      simpa using ht
    · rintro ⟨t', -, h⟩
      exact congrArg TState.mem h
  | assert b =>
    intro s s' t ht
    constructor
    · rintro ⟨hb, hs⟩
      exact ⟨t, ht, Or.inl ⟨hb, by rw [hs]; rfl⟩⟩
    · rintro ⟨t', ht', (⟨hb, h⟩ | ⟨-, h⟩)⟩
      · exact ⟨hb, congrArg TState.mem h⟩
      · exact absurd (congrArg TState.t h) ht'

/-! ### An assertion is not an `ensure` -/

/-- A false assertion waits until `∞`, which is a behaviour: the run succeeds. -/
theorem runT_assert_of_not (n : ℕ) {b : Spec.State Var Val → Bool} {st : TState Var Val}
    (hb : b st.mem = false) : runT (n + 1) (.assert b) st = some ⟨st.mem, ⊤⟩ := by
  rw [runT_assert, ite_eq_right (by simp [hb])]

/-- A false `ensure` has no behaviour at all: the run fails for every fuel. -/
theorem runT_ensure_of_not (n : ℕ) {b : Spec.State Var Val → Bool} {st : TState Var Val}
    (hb : b st.mem = false) : runT (n + 1) (.ensure b) st = none := by
  rw [runT_ensure, ite_eq_right (by simp [hb])]

/-- An assertion is implementable with nondecreasing time — "a false assertion is
satisfied by waiting forever" — for every condition. -/
theorem implementableT_assert (b : Spec.State Var Val → Bool) (st : TState Var Val) :
    ∃ st', denoteT (.assert b) st st' ∧ st.t ≤ st'.t := by
  by_cases hb : b st.mem = true
  · exact ⟨st, Or.inl ⟨hb, rfl⟩, le_rfl⟩
  · exact ⟨⟨st.mem, ⊤⟩, Or.inr ⟨hb, rfl⟩, le_top⟩

/-- An `ensure` is not: where its condition fails it has no poststate, which is
the book's "when `b` is false, ... this is unimplementable". So with a clock the
two notations are told apart, where `Interpreter.denote_assert_eq_ensure` says
that without one they cannot be. -/
theorem not_implementable_ensure {b : Spec.State Var Val → Bool} {st : TState Var Val}
    (hb : b st.mem = false) : ¬ ∃ st', denoteT (.ensure b) st st' := by
  rintro ⟨st', hb', -⟩
  rw [hb] at hb'
  exact Bool.noConfusion hb'

/-- What is implemented refines the book's assertion, which leaves the memory
variables unconstrained where this one keeps them: `Assertions.assert` is
`if b then ok else t′ = ∞`, and so is this, with the memory pinned. -/
theorem refines_assertSpec (b : Spec.State Var Val → Bool) :
    Spec.Refines
      (Spec.cond (fun st : TState Var Val => b st.mem = true) Spec.ok fun _ st' => st'.t = ⊤)
      (denoteT (.assert b)) := by
  rintro st st' (⟨hb, h⟩ | ⟨hb, h⟩)
  · exact Or.inl ⟨hb, h⟩
  · exact Or.inr ⟨hb, congrArg TState.t h⟩

/-! ### The loop, and Section 6.1.1 -/

/-- The timed loop unfolds as the book's loop does:
`while b do p od = if b then p. while b do p od else ok`. -/
theorem denoteT_whileDo_unfold (b : Spec.State Var Val → Bool) (p : Prog Var Val) :
    denoteT (.whileDo b p) =
      Spec.cond (fun st => b st.mem = true)
        (Spec.seq (denoteT p) (denoteT (.whileDo b p))) Spec.ok :=
  Spec.whileRel_unfold _ _

/-- A loop whose body ends in `t:= t+1` has the body `P. t:= t+1` of Section
6.1.1: its terminating runs are `Spec.whileRel b (P. tick)`, which is the shape
`LoopBridge.whileRun` has on the state `ZS`. The axioms themselves are stated
over `ZS`, so the bridge is not restated here; what is available for any clocked
program is that time does not decrease along a loop, the first of those axioms.
-/
theorem denoteT_whileDo_tick (b : Spec.State Var Val → Bool) (p : Prog Var Val) :
    denoteT (.whileDo b (.seq p .tick)) =
      Spec.whileRel (fun st => b st.mem = true)
        (Spec.seq (denoteT p) (denoteT (Prog.tick : Prog Var Val))) := rfl

/-- Time does not decrease along a loop: the base axiom of Section 6.1.1, for
the interpreter's loop. -/
theorem time_le_of_whileDo (b : Spec.State Var Val → Bool) (p : Prog Var Val)
    {st st' : TState Var Val} (h : denoteT (.whileDo b p) st st') : st.t ≤ st'.t :=
  time_le_of_denoteT _ h

/-! ### Printing, and a demonstration -/

/-- A time, written out. -/
def renderTime (t : ℕ∞) : String := if t = ⊤ then "∞" else toString t.toNat

namespace Demonstration

open LaPToP.ProgramTheory.Interpreter.Demo

/-- `while i ⧧ n do i:= i+1. t:= t+1 od`: the counting loop that charges one unit
of time for each iteration, as Section 4.2 does. -/
def timedCount : P := loop countCond (.seq (set .i (.add (.var .i) (.lit 1))) .tick)

-- From `i = 0` and `n = 7` it finishes at time 7.
#eval (runT 100 timedCount ⟨start 7, 0⟩).map fun st => (st.mem Vr.i, st.t)

/-- The loop takes one unit of time per iteration: from `n = 7` it ends at
`t = 7`, computed by the interpreter and checked by the kernel. -/
theorem timedCount_seven :
    (runT 100 timedCount ⟨start 7, 0⟩).map (fun st => (st.mem Vr.i, st.t)) = some (7, 7) := rfl

/-- The condition `s = 1`, which the start state does not satisfy. -/
def failing : Spec.State Vr ℤ → Bool := isOne.eval

/-- A false assertion ends the computation at time `∞`: the run succeeds and
says so, leaving the memory as it was. -/
theorem assert_false_run :
    runT 10 (.assert failing) ⟨start 3, 0⟩ = some ⟨start 3, ⊤⟩ := rfl

/-- A false `ensure` has no poststate at all: the run fails, at any fuel. -/
theorem ensure_false_run : runT 10 (.ensure failing) ⟨start 3, 0⟩ = none := rfl

/-- Which is the split the clock makes: without one the two are the same
program (`Interpreter.denote_assert_eq_ensure`). -/
theorem assert_ne_ensure :
    runT 10 (.assert failing) ⟨start 3, 0⟩ ≠ runT 10 (.ensure failing) ⟨start 3, 0⟩ := by
  rw [assert_false_run, ensure_false_run]
  simp

end Demonstration

end Timed

end LaPToP.ProgramTheory.Interpreter
