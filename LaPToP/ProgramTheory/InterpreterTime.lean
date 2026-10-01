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
`runAllT` is the searching timed interpreter, `runAll` with a clock: it keeps
both branches of every choice and finds exactly the timed behaviours
(`mem_runAllT_iff_denoteT`), where `runT` is complete only without a choice.

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

/-- The timed state after two processes that ran concurrently: each process's own
variables, and the later of the two finishing times — "execution of the
composition `P||Q` finishes when both `P` and `Q` are finished", `t′ = tP↑tQ`
(Section 8.0). -/
def mergeT (own : Var → Bool) (a b : TState Var Val) : TState Var Val :=
  ⟨Spec.merge own a.mem b.mem, max a.t b.t⟩

variable [DecidableEq Var] [Defs Var Val]

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
  /-- A call runs the body of what it names, on the clock. -/
  | call {k : ℕ} {st st' : TState Var Val} :
      EvalT (Defs.body k) st st' → EvalT (.call k) st st'
  /-- `p || q` runs both processes from the prestate and finishes when both have. -/
  | par {own : Var → Bool} {p q : Prog Var Val} {st st₁ st₂ : TState Var Val} :
      EvalT p st st₁ → EvalT q st st₂ → EvalT (.par own p q) st (mergeT own st₁ st₂)
  /-- A probabilistic choice takes a branch that has a chance. -/
  | probLeft {r : Spec.State Var Val → ℚ} {p q : Prog Var Val} {st st' : TState Var Val}
      (hr : 0 < r st.mem) : EvalT p st st' → EvalT (.prob r p q) st st'
  /-- ... either branch. -/
  | probRight {r : Spec.State Var Val → ℚ} {p q : Prog Var Val} {st st' : TState Var Val}
      (hr : r st.mem < 1) : EvalT q st st' → EvalT (.prob r p q) st st'

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
  | .call k => fun st st' => EvalT (.call k) st st'
  | .par own p q => fun st st' =>
      ∃ st₁ st₂, denoteT p st st₁ ∧ denoteT q st st₂ ∧ st' = mergeT own st₁ st₂
  | .prob r p q => fun st st' =>
      (0 < r st.mem ∧ denoteT p st st') ∨ (r st.mem < 1 ∧ denoteT q st st')

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

/-- A call is denoted by its timed executions. -/
theorem denoteT_call (k : ℕ) :
    denoteT (.call k : Prog Var Val) = fun st st' => EvalT (.call k) st st' := rfl

/-- `P||Q = ∃tP, tQ· ⟨t′· P⟩ tP ∧ ⟨t′· Q⟩ tQ ∧ t′ = tP↑tQ` (Section 8.0), each
process on its own variables. -/
@[simp] theorem denoteT_par (own : Var → Bool) (p q : Prog Var Val) :
    denoteT (.par own p q) = fun st st' =>
      ∃ st₁ st₂, denoteT p st st₁ ∧ denoteT q st st₂ ∧ st' = mergeT own st₁ st₂ := rfl

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
    | call h _ => exact .call h
    | par _ _ ihp ihq => exact ⟨_, _, ihp, ihq, rfl⟩
    | probLeft hr _ ih => exact Or.inl ⟨hr, ih⟩
    | probRight hr _ ih => exact Or.inr ⟨hr, ih⟩
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
    | call k => intro st st' h; exact h
    | par own p q ihp ihq =>
      intro st st' h
      obtain ⟨st₁, st₂, h₁, h₂, rfl⟩ := h
      exact .par (ihp h₁) (ihq h₂)
    | prob r p q ihp ihq =>
      intro st st' h
      rcases h with ⟨hr, h⟩ | ⟨hr, h⟩
      · exact .probLeft hr (ihp h)
      · exact .probRight hr (ihq h)

/-! ### Time does not decrease -/

/-- Time does not decrease along an execution. -/
theorem time_le_of_evalT {p : Prog Var Val} {st st' : TState Var Val} (h : EvalT p st st') :
    st.t ≤ st'.t := by
  induction h with
  | ok => exact le_rfl
  | assign => exact le_rfl
  | seq _ _ ihp ihq => exact le_trans ihp ihq
  | condTrue _ _ ih => exact ih
  | condFalse _ _ ih => exact ih
  | whileTrue _ _ _ ihp ihw => exact le_trans ihp ihw
  | whileFalse => exact le_rfl
  | newLocal _ ih => exact ih
  | assignAt => exact le_rfl
  | ensure => exact le_rfl
  | orLeft _ ih => exact ih
  | orRight _ ih => exact ih
  | tick => exact le_self_add
  | assertTrue => exact le_rfl
  | assertFalse => exact le_top
  | call _ ih => exact ih
  | par _ _ ihp _ => exact le_trans ihp (le_max_left _ _)
  | probLeft _ _ ih => exact ih
  | probRight _ _ ih => exact ih

/-- Time does not decrease: `t′ ≥ t` for every behaviour of every program. This
is the first of the three axioms of Section 6.1.1, holding here of the whole
language. -/
theorem time_le_of_denoteT (p : Prog Var Val) {st st' : TState Var Val}
    (h : denoteT p st st') : st.t ≤ st'.t :=
  time_le_of_evalT (evalT_iff_denoteT.mpr h)

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
  | n + 1, .call k, st => runT n (Defs.body k) st
  | n + 1, .par own p q, st =>
      (runT n p st).bind fun a => (runT n q st).map fun b => mergeT own a b
  | n + 1, .prob r p q, st => if 0 < r st.mem then runT n p st else runT n q st

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

@[simp] theorem runT_call (n k : ℕ) (st : TState Var Val) :
    runT (n + 1) (.call k) st = runT n (Defs.body k) st := rfl

@[simp] theorem runT_par (n : ℕ) (own : Var → Bool) (p q : Prog Var Val) (st : TState Var Val) :
    runT (n + 1) (.par own p q) st =
      (runT n p st).bind fun a => (runT n q st).map fun b => mergeT own a b := rfl

@[simp] theorem runT_prob (n : ℕ) (r : Spec.State Var Val → ℚ) (p q : Prog Var Val)
    (st : TState Var Val) :
    runT (n + 1) (.prob r p q) st = if 0 < r st.mem then runT n p st else runT n q st := rfl

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
    | call k =>
      simp only [runT_call] at h ⊢
      exact ih h hnm
    | par own p q =>
      simp only [runT_par] at h ⊢
      cases hp : runT n p st with
      | none => simp [hp] at h
      | some a =>
        cases hq : runT n q st with
        | none => simp [hp, hq] at h
        | some b =>
          simp only [hp, hq, Option.bind_some, Option.map_some] at h
          rw [ih hp hnm, ih hq hnm]
          exact h
    | prob r p q =>
      simp only [runT_prob] at h ⊢
      split_ifs at h ⊢ with hr
      · exact ih h hnm
      · exact ih h hnm

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
    | call k =>
      simp only [runT_call] at h
      exact .call (evalT_iff_denoteT.mpr (ih h))
    | par own p q =>
      simp only [runT_par] at h
      cases hp : runT n p st with
      | none => simp [hp] at h
      | some a =>
        cases hq : runT n q st with
        | none => simp [hp, hq] at h
        | some b =>
          simp only [hp, hq, Option.bind_some, Option.map_some, Option.some.injEq] at h
          exact ⟨a, b, ih hp, ih hq, h.symm⟩
    | prob r p q =>
      simp only [runT_prob] at h
      split_ifs at h with hr
      · exact Or.inl ⟨hr, ih h⟩
      · exact Or.inr ⟨lt_of_le_of_lt (not_lt.mp hr) zero_lt_one, ih h⟩

/-- **Completeness on the deterministic fragment**: every timed execution of a
program without a choice is a run with enough fuel. -/
theorem exists_runT_of_evalT [DetDefs Var Val] {p : Prog Var Val} (hp : Det p)
    {st st' : TState Var Val} (h : EvalT p st st') : ∃ f, runT f p st = some st' := by
  induction h with
  | ok => exact ⟨1, rfl⟩
  | assign => exact ⟨1, rfl⟩
  | seq _ _ ihp ihq =>
    obtain ⟨f₁, h₁⟩ := ihp hp.1
    obtain ⟨f₂, h₂⟩ := ihq hp.2
    refine ⟨max f₁ f₂ + 1, ?_⟩
    rw [runT_seq, runT_le h₁ (le_max_left f₁ f₂), Option.bind_some]
    exact runT_le h₂ (le_max_right f₁ f₂)
  | condTrue hb _ ih =>
    obtain ⟨f, hf⟩ := ih hp.1
    exact ⟨f + 1, by rw [runT_cond, ite_eq_left hb]; exact hf⟩
  | condFalse hb _ ih =>
    obtain ⟨f, hf⟩ := ih hp.2
    exact ⟨f + 1, by rw [runT_cond, ite_eq_right (by simp [hb])]; exact hf⟩
  | whileTrue hb _ _ ihp ihw =>
    obtain ⟨f₁, h₁⟩ := ihp hp
    obtain ⟨f₂, h₂⟩ := ihw hp
    refine ⟨max f₁ f₂ + 1, ?_⟩
    rw [runT_whileDo, ite_eq_left hb, runT_le h₁ (le_max_left f₁ f₂), Option.bind_some]
    exact runT_le h₂ (le_max_right f₁ f₂)
  | whileFalse hb => exact ⟨1, by rw [runT_whileDo, ite_eq_right (by simp [hb])]⟩
  | newLocal _ ih =>
    obtain ⟨f, hf⟩ := ih hp
    exact ⟨f + 1, by rw [runT_newLocal, hf, Option.map_some]⟩
  | assignAt => exact ⟨1, rfl⟩
  | ensure hb => exact ⟨1, by rw [runT_ensure, ite_eq_left hb]⟩
  | orLeft => exact hp.elim
  | orRight => exact hp.elim
  | tick => exact ⟨1, rfl⟩
  | assertTrue hb => exact ⟨1, by rw [runT_assert, ite_eq_left hb]⟩
  | assertFalse hb => exact ⟨1, by rw [runT_assert, ite_eq_right (by simp [hb])]⟩
  | call _ ih =>
    obtain ⟨f, hf⟩ := ih (DetDefs.det _)
    exact ⟨f + 1, by rw [runT_call]; exact hf⟩
  | par _ _ ihp ihq =>
    obtain ⟨f₁, h₁⟩ := ihp hp.1
    obtain ⟨f₂, h₂⟩ := ihq hp.2
    refine ⟨max f₁ f₂ + 1, ?_⟩
    rw [runT_par, runT_le h₁ (le_max_left f₁ f₂), runT_le h₂ (le_max_right f₁ f₂)]
    rfl
  | probLeft => exact hp.elim
  | probRight => exact hp.elim

/-- The same, for the timed denotation. -/
theorem exists_runT_of_denoteT [DetDefs Var Val] {p : Prog Var Val} (hp : Det p)
    {st st' : TState Var Val} (h : denoteT p st st') : ∃ f, runT f p st = some st' :=
  exists_runT_of_evalT hp (evalT_iff_denoteT.mpr h)

/-! ### The searching timed interpreter

`runT` resolves a choice by taking its left branch, as `run` does. `runAllT` is
`runAll` with a clock: it keeps every branch, so it finds each timed behaviour of
every program, the choice included (`mem_runAllT_iff_denoteT`). -/

/-- `runAllT fuel p st` is the list of every timed state `p` can reach from `st`
within the fuel. -/
def runAllT : ℕ → Prog Var Val → TState Var Val → List (TState Var Val)
  | 0, _, _ => []
  | _ + 1, .ok, st => [st]
  | _ + 1, .assign x e, st => [⟨Function.update st.mem x (e st.mem), st.t⟩]
  | n + 1, .seq p q, st => (runAllT n p st).flatMap (runAllT n q)
  | n + 1, .cond b p q, st => if b st.mem then runAllT n p st else runAllT n q st
  | n + 1, .whileDo b p, st =>
      if b st.mem then (runAllT n p st).flatMap (runAllT n (.whileDo b p)) else [st]
  | n + 1, .newLocal x e p, st =>
      (runAllT n p ⟨Function.update st.mem x (e st.mem), st.t⟩).map
        fun u => ⟨Function.update u.mem x (st.mem x), u.t⟩
  | _ + 1, .assignAt x e, st => [⟨Function.update st.mem (x st.mem) (e st.mem), st.t⟩]
  | _ + 1, .ensure b, st => if b st.mem then [st] else []
  | n + 1, .or p q, st => runAllT n p st ++ runAllT n q st
  | _ + 1, .tick, st => [⟨st.mem, st.t + 1⟩]
  | _ + 1, .assert b, st => if b st.mem then [st] else [⟨st.mem, ⊤⟩]
  | n + 1, .call k, st => runAllT n (Defs.body k) st
  | n + 1, .par own p q, st =>
      (runAllT n p st).flatMap fun a => (runAllT n q st).map fun b => mergeT own a b
  | n + 1, .prob r p q, st =>
      (if 0 < r st.mem then runAllT n p st else []) ++
        (if r st.mem < 1 then runAllT n q st else [])

@[simp] theorem runAllT_zero (p : Prog Var Val) (st : TState Var Val) :
    runAllT 0 p st = [] := by cases p <;> rfl

@[simp] theorem runAllT_ok (n : ℕ) (st : TState Var Val) :
    runAllT (n + 1) .ok st = [st] := rfl

@[simp] theorem runAllT_assign (n : ℕ) (x : Var) (e : Spec.State Var Val → Val)
    (st : TState Var Val) :
    runAllT (n + 1) (.assign x e) st = [⟨Function.update st.mem x (e st.mem), st.t⟩] := rfl

@[simp] theorem runAllT_seq (n : ℕ) (p q : Prog Var Val) (st : TState Var Val) :
    runAllT (n + 1) (.seq p q) st = (runAllT n p st).flatMap (runAllT n q) := rfl

@[simp] theorem runAllT_cond (n : ℕ) (b : Spec.State Var Val → Bool) (p q : Prog Var Val)
    (st : TState Var Val) :
    runAllT (n + 1) (.cond b p q) st = if b st.mem then runAllT n p st else runAllT n q st :=
  rfl

@[simp] theorem runAllT_whileDo (n : ℕ) (b : Spec.State Var Val → Bool) (p : Prog Var Val)
    (st : TState Var Val) :
    runAllT (n + 1) (.whileDo b p) st =
      if b st.mem then (runAllT n p st).flatMap (runAllT n (.whileDo b p)) else [st] := rfl

@[simp] theorem runAllT_newLocal (n : ℕ) (x : Var) (e : Spec.State Var Val → Val)
    (p : Prog Var Val) (st : TState Var Val) :
    runAllT (n + 1) (.newLocal x e p) st =
      (runAllT n p ⟨Function.update st.mem x (e st.mem), st.t⟩).map
        fun u => ⟨Function.update u.mem x (st.mem x), u.t⟩ := rfl

@[simp] theorem runAllT_assignAt (n : ℕ) (x : Spec.State Var Val → Var)
    (e : Spec.State Var Val → Val) (st : TState Var Val) :
    runAllT (n + 1) (.assignAt x e) st =
      [⟨Function.update st.mem (x st.mem) (e st.mem), st.t⟩] := rfl

@[simp] theorem runAllT_ensure (n : ℕ) (b : Spec.State Var Val → Bool) (st : TState Var Val) :
    runAllT (n + 1) (.ensure b) st = if b st.mem then [st] else [] := rfl

@[simp] theorem runAllT_or (n : ℕ) (p q : Prog Var Val) (st : TState Var Val) :
    runAllT (n + 1) (.or p q) st = runAllT n p st ++ runAllT n q st := rfl

@[simp] theorem runAllT_tick (n : ℕ) (st : TState Var Val) :
    runAllT (n + 1) (Prog.tick : Prog Var Val) st = [⟨st.mem, st.t + 1⟩] := rfl

@[simp] theorem runAllT_assert (n : ℕ) (b : Spec.State Var Val → Bool) (st : TState Var Val) :
    runAllT (n + 1) (.assert b) st = if b st.mem then [st] else [⟨st.mem, ⊤⟩] := rfl

@[simp] theorem runAllT_call (n k : ℕ) (st : TState Var Val) :
    runAllT (n + 1) (.call k) st = runAllT n (Defs.body k) st := rfl

@[simp] theorem runAllT_par (n : ℕ) (own : Var → Bool) (p q : Prog Var Val)
    (st : TState Var Val) :
    runAllT (n + 1) (.par own p q) st =
      (runAllT n p st).flatMap fun a => (runAllT n q st).map fun b => mergeT own a b := rfl

@[simp] theorem runAllT_prob (n : ℕ) (r : Spec.State Var Val → ℚ) (p q : Prog Var Val)
    (st : TState Var Val) :
    runAllT (n + 1) (.prob r p q) st =
      (if 0 < r st.mem then runAllT n p st else []) ++
        (if r st.mem < 1 then runAllT n q st else []) := rfl

/-- More fuel never loses a result of the timed search. -/
theorem runAllT_le : ∀ {f g : ℕ} {p : Prog Var Val} {st st' : TState Var Val},
    st' ∈ runAllT f p st → f ≤ g → st' ∈ runAllT g p st := by
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
      simp only [runAllT_seq, List.mem_flatMap] at h ⊢
      obtain ⟨u, hu, hq⟩ := h
      exact ⟨u, ih hu hnm, ih hq hnm⟩
    | cond b p q =>
      simp only [runAllT_cond] at h ⊢
      split_ifs at h ⊢ with hb
      · exact ih h hnm
      · exact ih h hnm
    | whileDo b p =>
      simp only [runAllT_whileDo] at h ⊢
      split_ifs at h ⊢ with hb
      · simp only [List.mem_flatMap] at h ⊢
        obtain ⟨u, hu, hw⟩ := h
        exact ⟨u, ih hu hnm, ih hw hnm⟩
      · exact h
    | newLocal x e p =>
      simp only [runAllT_newLocal, List.mem_map] at h ⊢
      obtain ⟨u, hu, hst⟩ := h
      exact ⟨u, ih hu hnm, hst⟩
    | assignAt x e => simpa using h
    | ensure b =>
      simp only [runAllT_ensure] at h ⊢
      split_ifs at h ⊢ with hb
      · exact h
      · simp at h
    | or p q =>
      simp only [runAllT_or, List.mem_append] at h ⊢
      exact h.imp (fun hp => ih hp hnm) fun hq => ih hq hnm
    | tick => simpa using h
    | assert b =>
      simp only [runAllT_assert] at h ⊢
      split_ifs at h ⊢ with hb <;> exact h
    | call k =>
      simp only [runAllT_call] at h ⊢
      exact ih h hnm
    | par own p q =>
      simp only [runAllT_par, List.mem_flatMap, List.mem_map] at h ⊢
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact ⟨a, ih ha hnm, b, ih hb hnm, rfl⟩
    | prob r p q =>
      simp only [runAllT_prob, List.mem_append] at h ⊢
      rcases h with h | h
      · left; split_ifs at h ⊢ with hr
        · exact ih h hnm
        · simp at h
      · right; split_ifs at h ⊢ with hr
        · exact ih h hnm
        · simp at h

/-- **Soundness of the timed search**: every timed state it finds is an
execution. -/
theorem evalT_of_mem_runAllT : ∀ {f : ℕ} {p : Prog Var Val} {st st' : TState Var Val},
    st' ∈ runAllT f p st → EvalT p st st' := by
  intro f
  induction f with
  | zero => intro p st st' h; simp at h
  | succ n ih =>
    intro p st st' h
    cases p with
    | ok =>
      simp only [runAllT_ok, List.mem_singleton] at h
      subst h; exact .ok
    | assign x e =>
      simp only [runAllT_assign, List.mem_singleton] at h
      subst h; exact .assign
    | seq p q =>
      simp only [runAllT_seq, List.mem_flatMap] at h
      obtain ⟨u, hu, hq⟩ := h
      exact .seq (ih hu) (ih hq)
    | cond b p q =>
      simp only [runAllT_cond] at h
      split_ifs at h with hb
      · exact .condTrue hb (ih h)
      · exact .condFalse (by simpa using hb) (ih h)
    | whileDo b p =>
      simp only [runAllT_whileDo] at h
      split_ifs at h with hb
      · simp only [List.mem_flatMap] at h
        obtain ⟨u, hu, hw⟩ := h
        exact .whileTrue hb (ih hu) (ih hw)
      · simp only [List.mem_singleton] at h
        subst h; exact .whileFalse (by simpa using hb)
    | newLocal x e p =>
      simp only [runAllT_newLocal, List.mem_map] at h
      obtain ⟨u, hu, hst⟩ := h
      subst hst
      exact .newLocal (ih hu)
    | assignAt x e =>
      simp only [runAllT_assignAt, List.mem_singleton] at h
      subst h; exact .assignAt
    | ensure b =>
      simp only [runAllT_ensure] at h
      split_ifs at h with hb
      · simp only [List.mem_singleton] at h
        subst h; exact .ensure hb
      · simp at h
    | or p q =>
      simp only [runAllT_or, List.mem_append] at h
      exact h.elim (fun hp => .orLeft (ih hp)) fun hq => .orRight (ih hq)
    | tick =>
      simp only [runAllT_tick, List.mem_singleton] at h
      subst h; exact .tick
    | assert b =>
      simp only [runAllT_assert] at h
      split_ifs at h with hb
      · simp only [List.mem_singleton] at h
        subst h; exact .assertTrue hb
      · simp only [List.mem_singleton] at h
        subst h; exact .assertFalse (by simpa using hb)
    | call k =>
      simp only [runAllT_call] at h
      exact .call (ih h)
    | par own p q =>
      simp only [runAllT_par, List.mem_flatMap, List.mem_map] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .par (ih ha) (ih hb)
    | prob r p q =>
      simp only [runAllT_prob, List.mem_append] at h
      rcases h with h | h
      · split_ifs at h with hr
        · exact .probLeft hr (ih h)
        · simp at h
      · split_ifs at h with hr
        · exact .probRight hr (ih h)
        · simp at h

/-- **Completeness of the timed search**, for the whole language: every timed
execution is found with enough fuel. -/
theorem exists_mem_runAllT_of_evalT : ∀ {p : Prog Var Val} {st st' : TState Var Val},
    EvalT p st st' → ∃ f, st' ∈ runAllT f p st := by
  intro p st st' h
  induction h with
  | ok => exact ⟨1, by simp⟩
  | assign => exact ⟨1, by simp⟩
  | @seq p q st u st' _ _ ihp ihq =>
    obtain ⟨f₁, h₁⟩ := ihp
    obtain ⟨f₂, h₂⟩ := ihq
    refine ⟨max f₁ f₂ + 1, ?_⟩
    simp only [runAllT_seq, List.mem_flatMap]
    exact ⟨u, runAllT_le h₁ (le_max_left _ _), runAllT_le h₂ (le_max_right _ _)⟩
  | condTrue hb _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simpa [hb] using hf⟩
  | condFalse hb _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simpa [hb] using hf⟩
  | @whileTrue b p st u st' hb _ _ ihp ihw =>
    obtain ⟨f₁, h₁⟩ := ihp
    obtain ⟨f₂, h₂⟩ := ihw
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hmem : st' ∈ (runAllT (max f₁ f₂) p st).flatMap
        (runAllT (max f₁ f₂) (.whileDo b p)) := by
      simp only [List.mem_flatMap]
      exact ⟨u, runAllT_le h₁ (le_max_left _ _), runAllT_le h₂ (le_max_right _ _)⟩
    simpa [hb] using hmem
  | whileFalse hb => exact ⟨1, by simp [hb]⟩
  | @newLocal x e p st u _ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    simp only [runAllT_newLocal, List.mem_map]
    exact ⟨u, hf, rfl⟩
  | assignAt => exact ⟨1, by simp⟩
  | ensure hb => exact ⟨1, by simp [hb]⟩
  | orLeft _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simp only [runAllT_or, List.mem_append]; exact Or.inl hf⟩
  | orRight _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simp only [runAllT_or, List.mem_append]; exact Or.inr hf⟩
  | tick => exact ⟨1, by simp⟩
  | assertTrue hb => exact ⟨1, by simp [hb]⟩
  | assertFalse hb => exact ⟨1, by simp [hb]⟩
  | call _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simpa using hf⟩
  | @par own p q st a b _ _ ihp ihq =>
    obtain ⟨f₁, h₁⟩ := ihp
    obtain ⟨f₂, h₂⟩ := ihq
    refine ⟨max f₁ f₂ + 1, ?_⟩
    simp only [runAllT_par, List.mem_flatMap, List.mem_map]
    exact ⟨a, runAllT_le h₁ (le_max_left _ _), b, runAllT_le h₂ (le_max_right _ _), rfl⟩
  | probLeft hr _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simp only [runAllT_prob, List.mem_append, ite_eq_left hr]; exact Or.inl hf⟩
  | probRight hr _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simp only [runAllT_prob, List.mem_append, ite_eq_left hr]; exact Or.inr hf⟩

/-- The timed search computes exactly the timed specification, for every program
— the choice is searched, not resolved, so no `Det` hypothesis is needed. -/
theorem mem_runAllT_iff_denoteT {p : Prog Var Val} {st st' : TState Var Val} :
    (∃ f, st' ∈ runAllT f p st) ↔ denoteT p st st' :=
  ⟨fun ⟨_, h⟩ => evalT_iff_denoteT.mp (evalT_of_mem_runAllT h),
    fun h => exists_mem_runAllT_of_evalT (evalT_iff_denoteT.mpr h)⟩

/-! ### The untimed interpreter is what a finite-time observer sees -/

/-- An untimed execution from a finite time is a timed one ending at a finite
time. -/
theorem evalT_of_eval {p : Prog Var Val} {s s' : Spec.State Var Val} (h : Eval p s s') :
    ∀ t : ℕ∞, t ≠ ⊤ → ∃ t' : ℕ∞, t' ≠ ⊤ ∧ EvalT p ⟨s, t⟩ ⟨s', t'⟩ := by
  induction h with
  | ok => exact fun t ht => ⟨t, ht, .ok⟩
  | assign => exact fun t ht => ⟨t, ht, .assign⟩
  | seq _ _ ihp ihq =>
    intro t ht
    obtain ⟨tu, htu, hp⟩ := ihp t ht
    obtain ⟨t', ht', hq⟩ := ihq tu htu
    exact ⟨t', ht', .seq hp hq⟩
  | condTrue hb _ ih =>
    intro t ht
    obtain ⟨t', ht', h⟩ := ih t ht
    exact ⟨t', ht', .condTrue hb h⟩
  | condFalse hb _ ih =>
    intro t ht
    obtain ⟨t', ht', h⟩ := ih t ht
    exact ⟨t', ht', .condFalse hb h⟩
  | whileTrue hb _ _ ihp ihw =>
    intro t ht
    obtain ⟨tu, htu, hp⟩ := ihp t ht
    obtain ⟨t', ht', hw⟩ := ihw tu htu
    exact ⟨t', ht', .whileTrue hb hp hw⟩
  | whileFalse hb => exact fun t ht => ⟨t, ht, .whileFalse hb⟩
  | newLocal _ ih =>
    intro t ht
    obtain ⟨t', ht', h⟩ := ih t ht
    exact ⟨t', ht', EvalT.newLocal (st := ⟨_, t⟩) (u := ⟨_, t'⟩) h⟩
  | assignAt => exact fun t ht => ⟨t, ht, .assignAt⟩
  | ensure hb => exact fun t ht => ⟨t, ht, .ensure hb⟩
  | orLeft _ ih =>
    intro t ht
    obtain ⟨t', ht', h⟩ := ih t ht
    exact ⟨t', ht', .orLeft h⟩
  | orRight _ ih =>
    intro t ht
    obtain ⟨t', ht', h⟩ := ih t ht
    exact ⟨t', ht', .orRight h⟩
  | tick => exact fun t ht => ⟨t + 1, by simpa using ht, .tick⟩
  | assert hb => exact fun t ht => ⟨t, ht, .assertTrue hb⟩
  | call _ ih =>
    intro t ht
    obtain ⟨t', ht', h⟩ := ih t ht
    exact ⟨t', ht', .call h⟩
  | par _ _ ihp ihq =>
    intro t ht
    obtain ⟨t₁, ht₁, h₁⟩ := ihp t ht
    obtain ⟨t₂, ht₂, h₂⟩ := ihq t ht
    exact ⟨max t₁ t₂, (max_lt (lt_top_iff_ne_top.mpr ht₁) (lt_top_iff_ne_top.mpr ht₂)).ne,
      EvalT.par (st₁ := ⟨_, t₁⟩) (st₂ := ⟨_, t₂⟩) h₁ h₂⟩
  | probLeft hr _ ih =>
    intro t ht
    obtain ⟨t', ht', h⟩ := ih t ht
    exact ⟨t', ht', .probLeft hr h⟩
  | probRight hr _ ih =>
    intro t ht
    obtain ⟨t', ht', h⟩ := ih t ht
    exact ⟨t', ht', .probRight hr h⟩

/-- A timed execution that starts and ends at finite times is an untimed one. -/
theorem eval_of_evalT {p : Prog Var Val} {st st' : TState Var Val} (h : EvalT p st st') :
    st.t ≠ ⊤ → st'.t ≠ ⊤ → Eval p st.mem st'.mem := by
  induction h with
  | ok => exact fun _ _ => .ok
  | assign => exact fun _ _ => .assign
  | @seq p q st u st' _ hq ihp ihq =>
    intro hs hs'
    have hu : u.t ≠ ⊤ := fun htop => hs' (top_le_iff.mp (htop ▸ time_le_of_evalT hq))
    exact .seq (ihp hs hu) (ihq hu hs')
  | condTrue hb _ ih => exact fun hs hs' => .condTrue hb (ih hs hs')
  | condFalse hb _ ih => exact fun hs hs' => .condFalse hb (ih hs hs')
  | @whileTrue b p st u st' hb _ hw ihp ihw =>
    intro hs hs'
    have hu : u.t ≠ ⊤ := fun htop => hs' (top_le_iff.mp (htop ▸ time_le_of_evalT hw))
    exact .whileTrue hb (ihp hs hu) (ihw hu hs')
  | whileFalse hb => exact fun _ _ => .whileFalse hb
  | newLocal _ ih => exact fun hs hs' => .newLocal (ih hs hs')
  | assignAt => exact fun _ _ => .assignAt
  | ensure hb => exact fun _ _ => .ensure hb
  | orLeft _ ih => exact fun hs hs' => .orLeft (ih hs hs')
  | orRight _ ih => exact fun hs hs' => .orRight (ih hs hs')
  | tick => exact fun _ _ => .tick
  | assertTrue hb => exact fun _ _ => .assert hb
  | assertFalse _ => exact fun _ hs' => absurd rfl hs'
  | call _ ih => exact fun hs hs' => .call (ih hs hs')
  | @par own p q st a b _ _ ihp ihq =>
    intro hs hs'
    have ha : a.t ≠ ⊤ := fun h => hs' (by simp [mergeT, h])
    have hb : b.t ≠ ⊤ := fun h => hs' (by simp [mergeT, h])
    exact .par (ihp hs ha) (ihq hs hb)
  | probLeft hr _ ih => exact fun hs hs' => .probLeft hr (ih hs hs')
  | probRight hr _ ih => exact fun hs hs' => .probRight hr (ih hs hs')

/-- **The projection theorem.** From a state at finite time, the behaviours the
untimed interpreter has are exactly the timed behaviours that end in finite
time. So the untimed development of `Interpreter` is not a rival account of the
same programs but this one with the clock forgotten, and the identification it
makes of `assert` with `ensure` is exactly right for an observer without a
clock. This is `Assertions.assert_finite` for every program instead of one
assertion. -/
theorem denote_iff_denoteT (p : Prog Var Val) {s s' : Spec.State Var Val} {t : ℕ∞}
    (ht : t ≠ ⊤) : denote p s s' ↔ ∃ t' : ℕ∞, t' ≠ ⊤ ∧ denoteT p ⟨s, t⟩ ⟨s', t'⟩ := by
  rw [← eval_eq_denote]
  constructor
  · intro h
    obtain ⟨t', ht', hT⟩ := evalT_of_eval h t ht
    exact ⟨t', ht', evalT_iff_denoteT.mp hT⟩
  · rintro ⟨t', ht', hT⟩
    exact eval_of_evalT (evalT_iff_denoteT.mpr hT) ht ht'

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

/-- The backtracking example `s:= 0 or s:= 1. ensure s=1` on the clock: the
timed search finds its one poststate, at the time it started, where `runT`
takes the left branch and finds none. -/
theorem backtrack_runAllT :
    (runAllT 10 backtrack ⟨start 3, 0⟩).map (fun st => (st.mem Vr.s, st.t)) = [(1, 0)] := rfl

theorem backtrack_runT : runT 10 backtrack ⟨start 3, 0⟩ = none := rfl

/-- `tick or (tick. tick)`: a choice between a quick and a slow branch, which
the timed search reports with both of their times. -/
def quickOrSlow : P := .or .tick (.seq .tick .tick)

theorem quickOrSlow_runAllT :
    (runAllT 10 quickOrSlow ⟨start 0, 0⟩).map TState.t = [1, 2] := rfl

end Demonstration

end Timed

end LaPToP.ProgramTheory.Interpreter
