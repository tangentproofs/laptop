import LaPToP.ProgramTheory.Programs
import LaPToP.ProgramTheory.WhileLoop

/-!
# An interpreter for the programming notations

Chapters 4 and 5 give the programming notations *as specifications*: `ok`,
`x:= e`, `if b then P else Q`, `P. Q` are relations between prestate and
poststate, and the while-loop is a refinement notation (`Spec.WhileRefines`).
Nothing in those modules *runs*. This module adds the missing executable layer:
an abstract syntax of programs as Lean data, a computable `run` that executes
them, a denotation `denote : Prog → Spec` into the theory of Chapter 4, and the
soundness theorem that ties the two together.

## The model

`Prog Var Val` is the core abstract syntax: `ok`, `assign x e`, `seq p q`,
`cond b p q`, `whileDo b p`. `run fuel p s` executes `p` from state `s` and
returns `some s'` on success, `none` when the fuel runs out. Fuel is a budget
for the *depth of the execution tree* (not only for loop iterations), which
makes `run` structurally recursive, hence kernel-reducible: the demonstration
results below are proved by `rfl`, not merely observed by `#eval`.

`denote` maps the syntax onto exactly the Chapter 4 specifications, so the
interpreter is interpreting *this* theory and no other:

| `Prog`            | `denote`                                   |
| ----------------- | ------------------------------------------ |
| `.ok`             | `Spec.ok`                                  |
| `.assign x e`     | `Spec.assign x e`                          |
| `.seq p q`        | `Spec.seq`                                 |
| `.cond b p q`     | `Spec.cond`                                |
| `.whileDo b p`    | `Spec.whileRel` (see below)                |

For the loop we need a specification where the book has only a refinement
notation. `Spec.whileRel b R` is the inductively defined relation of the
*terminating* runs of the loop: either the condition fails and nothing happens,
or the condition holds, `R` takes one step, and the loop relates the result to
the final state. It is a fixed point of the book's unfolding
(`Spec.whileRel_unfold`), so `W ⇐ while b do P od` holds for it
(`Spec.whileRefines_whileRel`); and it is the *strongest* solution in the sense
that any `W` satisfying the book's while-refinement is refined by it
(`Spec.refines_whileRel`). That theorem is what makes a run of a loop trustworthy:
whatever a while-refinement proof establishes about `W` holds of every run that
terminates (`Interpreter.run_while_sound`).

The three soundness/completeness facts are:

* `Interpreter.denote_of_run` — every successful run satisfies the denotation;
* `Interpreter.exists_run_of_denote` — every behaviour of the denotation is a
  successful run for some fuel (so the interpreter is not weaker than its spec);
* `Interpreter.deterministic_denote` — hence each denoted program is
  deterministic, as an executed program must be.

`Interpreter.run_sound` combines the first with refinement: if `W ⇐ denote p`
has been proved, then every successful run of `p` satisfies `W`. That is the
bridge from a Chapter 4 development to an actual execution.

## Honest deviations and scope

* Expressions are *semantic*: `e : State Var Val → Val` and `b : State Var Val → Bool`,
  matching `Spec.assign`, which takes any function of the prestate. So `Prog` is
  data only up to its embedded expression functions. The `Interpreter.Demo`
  namespace closes that gap for the demonstrations with a first-order syntax
  (`Exp`, `Bexp` over integer variables) and its own evaluator, so the example
  programs there are honest data.
* `whileDo` is the only unbounded construct, and it is executed with fuel; a
  fuel-free partial-correctness execution (and the tie to the least-fixed-point
  account of Section 6.1.1) is not done here.
* Out of scope in this round, and not claimed anywhere below: concurrency (`||`),
  the time variable `t`, channels and interaction, variable declaration and
  framing, assertions, the full surface syntax of the book, and a command-line
  binary outside Lean.
-/

namespace LaPToP.ProgramTheory

universe u v

namespace Spec

variable {σ : Type u}

/-! ### The terminating runs of a loop (a specification for `while`) -/

/-- The relation of the *terminating* executions of `while b do R od`: either
`b` fails and the state is unchanged, or `b` holds, `R` takes one step, and the
loop continues from there. This is the specification the interpreter's loop
implements; the book gives the while-loop only as the refinement notation
`Spec.WhileRefines`. -/
inductive whileRel (b : σ → Prop) (R : Spec σ) : σ → σ → Prop
  /-- The loop exits: `¬b` and the state is unchanged. -/
  | exit {s : σ} (hb : ¬ b s) : whileRel b R s s
  /-- One iteration: `b` holds, `R` goes from `s` to `t`, the loop from `t` to `s'`. -/
  | step {s t s' : σ} (hb : b s) (hR : R s t) (hW : whileRel b R t s') : whileRel b R s s'

variable (b : σ → Prop) (R : Spec σ)

/-- `while b do R od = if b then R. while b do R od else ok`: the loop relation
is a fixed point of the book's unfolding. -/
theorem whileRel_unfold : whileRel b R = cond b (seq R (whileRel b R)) ok := by
  refine Spec.ext fun s s' => ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | exit hb => exact Or.inr ⟨hb, rfl⟩
    | step hb hR hW => exact Or.inl ⟨hb, _, hR, hW⟩
  · rcases h with ⟨hb, t, hR, hW⟩ | ⟨hb, hok⟩
    · exact whileRel.step hb hR hW
    · rw [show s' = s from hok]; exact whileRel.exit hb

/-- `while b do R od ⇐ while b do R od` in the book's notation: the loop
relation satisfies the while-refinement it is meant to satisfy. -/
theorem whileRefines_whileRel : WhileRefines (whileRel b R) b R := by
  rintro s s' (⟨hb, t, hR, hW⟩ | ⟨hb, hok⟩)
  · exact whileRel.step hb hR hW
  · rw [show s' = s from hok]; exact whileRel.exit hb

/-- The loop relation is the *strongest* solution of the book's while-refinement:
if `W ⇐ while b do R od` then `W ⇐ whileRel b R`. So anything proved of `W` by
the while-refinement rule holds of every terminating execution of the loop. -/
theorem refines_whileRel {W : Spec σ} (h : WhileRefines W b R) : Refines W (whileRel b R) := by
  intro s s' hw
  induction hw with
  | exit hb => exact h _ _ (Or.inr ⟨hb, rfl⟩)
  | step hb hR _ ih => exact h _ _ (Or.inl ⟨hb, _, hR, ih⟩)

/-- A loop whose condition never holds relates each state to itself. -/
theorem whileRel_of_not (hb : ∀ s, ¬ b s) : whileRel b R = ok :=
  Spec.ext fun s s' => ⟨fun h => by cases h with
      | exit => rfl
      | step h' => exact absurd h' (hb _),
    fun h => by rw [show s' = s from h]; exact whileRel.exit (hb s)⟩

end Spec

namespace Interpreter

variable {Var : Type u} {Val : Type v}

/-! ### Abstract syntax -/

/-- The abstract syntax of the core programming notations: `ok`, assignment,
sequential composition, `if`, and `while`. Expressions and conditions are
functions of the prestate, as in `Spec.assign` and `Spec.cond`; conditions are
`Bool`-valued so that they can be executed. -/
inductive Prog (Var : Type u) (Val : Type v) : Type (max u v) where
  /-- `ok`. -/
  | ok : Prog Var Val
  /-- `x:= e`. -/
  | assign (x : Var) (e : Spec.State Var Val → Val) : Prog Var Val
  /-- `p. q`. -/
  | seq (p q : Prog Var Val) : Prog Var Val
  /-- `if b then p else q`. -/
  | cond (b : Spec.State Var Val → Bool) (p q : Prog Var Val) : Prog Var Val
  /-- `while b do p od`. -/
  | whileDo (b : Spec.State Var Val → Bool) (p : Prog Var Val) : Prog Var Val

/-- Programs without loops: the four notations of Section 4.0.3 that are
programs outright. -/
inductive LoopFree : Prog Var Val → Prop
  /-- `ok` is loop-free. -/
  | ok : LoopFree .ok
  /-- `x:= e` is loop-free. -/
  | assign (x : Var) (e : Spec.State Var Val → Val) : LoopFree (.assign x e)
  /-- `p. q` is loop-free when `p` and `q` are. -/
  | seq {p q : Prog Var Val} : LoopFree p → LoopFree q → LoopFree (.seq p q)
  /-- `if b then p else q` is loop-free when `p` and `q` are. -/
  | cond (b : Spec.State Var Val → Bool) {p q : Prog Var Val} :
      LoopFree p → LoopFree q → LoopFree (.cond b p q)

/-! ### The interpreter -/

/-- `run fuel p s` executes `p` from state `s`, returning `none` if the fuel is
exhausted. One unit of fuel is spent per level of the execution tree, so a loop
iteration costs at least one unit; `run` is therefore structurally recursive on
the fuel, and reduces in the kernel. -/
def run [DecidableEq Var] :
    ℕ → Prog Var Val → Spec.State Var Val → Option (Spec.State Var Val)
  | 0, _, _ => none
  | _ + 1, .ok, s => some s
  | _ + 1, .assign x e, s => some (Function.update s x (e s))
  | n + 1, .seq p q, s => (run n p s).bind (run n q)
  | n + 1, .cond b p q, s => if b s then run n p s else run n q s
  | n + 1, .whileDo b p, s =>
      if b s then (run n p s).bind (run n (.whileDo b p)) else some s

variable [DecidableEq Var]

@[simp] theorem run_zero (p : Prog Var Val) (s : Spec.State Var Val) : run 0 p s = none := by
  cases p <;> rfl

@[simp] theorem run_ok (n : ℕ) (s : Spec.State Var Val) : run (n + 1) .ok s = some s := rfl

@[simp] theorem run_assign (n : ℕ) (x : Var) (e : Spec.State Var Val → Val)
    (s : Spec.State Var Val) :
    run (n + 1) (.assign x e) s = some (Function.update s x (e s)) := rfl

@[simp] theorem run_seq (n : ℕ) (p q : Prog Var Val) (s : Spec.State Var Val) :
    run (n + 1) (.seq p q) s = (run n p s).bind (run n q) := rfl

@[simp] theorem run_cond (n : ℕ) (b : Spec.State Var Val → Bool) (p q : Prog Var Val)
    (s : Spec.State Var Val) :
    run (n + 1) (.cond b p q) s = if b s then run n p s else run n q s := rfl

@[simp] theorem run_whileDo (n : ℕ) (b : Spec.State Var Val → Bool) (p : Prog Var Val)
    (s : Spec.State Var Val) :
    run (n + 1) (.whileDo b p) s =
      if b s then (run n p s).bind (run n (.whileDo b p)) else some s := rfl

/-- More fuel never spoils a successful run. -/
theorem run_le : ∀ {f g : ℕ} {p : Prog Var Val} {s s' : Spec.State Var Val},
    run f p s = some s' → f ≤ g → run g p s = some s' := by
  intro f
  induction f with
  | zero => intro g p s s' h _; simp at h
  | succ n ih =>
    intro g p s s' h hle
    obtain ⟨m, rfl⟩ : ∃ m, g = m + 1 := ⟨g - 1, by omega⟩
    have hnm : n ≤ m := by omega
    cases p with
    | ok => simpa using h
    | assign x e => simpa using h
    | seq p q =>
      simp only [run_seq] at h ⊢
      cases hp : run n p s with
      | none => simp [hp] at h
      | some t =>
        simp only [hp, Option.bind_some] at h
        simp only [ih hp hnm, Option.bind_some]
        exact ih h hnm
    | cond b p q =>
      simp only [run_cond] at h ⊢
      split_ifs at h ⊢ with hb
      · exact ih h hnm
      · exact ih h hnm
    | whileDo b p =>
      simp only [run_whileDo] at h ⊢
      split_ifs at h ⊢ with hb
      · cases hp : run n p s with
        | none => simp [hp] at h
        | some t =>
          simp only [hp, Option.bind_some] at h
          simp only [ih hp hnm, Option.bind_some]
          exact ih h hnm
      · exact h

/-! ### Denotation into the theory of Chapter 4 -/

/-- The denotation of a program as a specification: exactly the notations of
Section 4.0, with the loop denoted by its terminating-run relation. -/
def denote : Prog Var Val → Spec (Spec.State Var Val)
  | .ok => Spec.ok
  | .assign x e => Spec.assign x e
  | .seq p q => Spec.seq (denote p) (denote q)
  | .cond b p q => Spec.cond (fun s => b s = true) (denote p) (denote q)
  | .whileDo b p => Spec.whileRel (fun s => b s = true) (denote p)

@[simp] theorem denote_ok : denote (Var := Var) (Val := Val) .ok = Spec.ok := rfl

@[simp] theorem denote_assign (x : Var) (e : Spec.State Var Val → Val) :
    denote (.assign x e) = Spec.assign x e := rfl

@[simp] theorem denote_seq (p q : Prog Var Val) :
    denote (.seq p q) = Spec.seq (denote p) (denote q) := rfl

@[simp] theorem denote_cond (b : Spec.State Var Val → Bool) (p q : Prog Var Val) :
    denote (.cond b p q) = Spec.cond (fun s => b s = true) (denote p) (denote q) := rfl

@[simp] theorem denote_whileDo (b : Spec.State Var Val → Bool) (p : Prog Var Val) :
    denote (.whileDo b p) = Spec.whileRel (fun s => b s = true) (denote p) := rfl

/-- A loop-free program denotes a program in the sense of Section 4.0.3. -/
theorem isProgram_denote {p : Prog Var Val} (h : LoopFree p) : Spec.IsProgram (denote p) := by
  induction h with
  | ok => exact Spec.IsProgram.ok
  | assign x e => exact Spec.IsProgram.assign x e
  | seq _ _ ihp ihq => exact Spec.IsProgram.seq ihp ihq
  | cond b _ _ ihp ihq => exact Spec.IsProgram.cond _ ihp ihq

/-! ### Soundness and completeness of the interpreter -/

/-- **Soundness**: a successful run satisfies the denoted specification. -/
theorem denote_of_run : ∀ {f : ℕ} {p : Prog Var Val} {s s' : Spec.State Var Val},
    run f p s = some s' → denote p s s' := by
  intro f
  induction f with
  | zero => intro p s s' h; simp at h
  | succ n ih =>
    intro p s s' h
    cases p with
    | ok =>
      simp only [run_ok, Option.some.injEq] at h
      exact h.symm
    | assign x e =>
      simp only [run_assign, Option.some.injEq] at h
      exact h.symm
    | seq p q =>
      simp only [run_seq] at h
      cases hp : run n p s with
      | none => simp [hp] at h
      | some t =>
        simp only [hp, Option.bind_some] at h
        exact ⟨t, ih hp, ih h⟩
    | cond b p q =>
      simp only [run_cond] at h
      split_ifs at h with hb
      · exact Or.inl ⟨hb, ih h⟩
      · exact Or.inr ⟨hb, ih h⟩
    | whileDo b p =>
      simp only [run_whileDo] at h
      split_ifs at h with hb
      · cases hp : run n p s with
        | none => simp [hp] at h
        | some t =>
          simp only [hp, Option.bind_some] at h
          exact Spec.whileRel.step hb (ih hp) (ih h)
      · simp only [Option.some.injEq] at h
        subst h
        exact Spec.whileRel.exit hb

/-- **Completeness**: every behaviour allowed by the denotation is achieved by
a run with enough fuel. -/
theorem exists_run_of_denote : ∀ {p : Prog Var Val} {s s' : Spec.State Var Val},
    denote p s s' → ∃ f, run f p s = some s' := by
  intro p
  induction p with
  | ok =>
    intro s s' h
    exact ⟨1, by rw [run_ok, show s' = s from h]⟩
  | assign x e =>
    intro s s' h
    exact ⟨1, by rw [run_assign, show s' = Function.update s x (e s) from h]⟩
  | seq p q ihp ihq =>
    intro s s' h
    obtain ⟨t, hp, hq⟩ : ∃ t, denote p s t ∧ denote q t s' := h
    obtain ⟨f₁, h₁⟩ := ihp hp
    obtain ⟨f₂, h₂⟩ := ihq hq
    refine ⟨max f₁ f₂ + 1, ?_⟩
    rw [run_seq, run_le h₁ (le_max_left f₁ f₂), Option.bind_some]
    exact run_le h₂ (le_max_right f₁ f₂)
  | cond b p q ihp ihq =>
    intro s s' h
    obtain ⟨hb, h⟩ | ⟨hb, h⟩ :
        ((b s = true) ∧ denote p s s') ∨ (¬ (b s = true) ∧ denote q s s') := h
    · obtain ⟨f, hf⟩ := ihp h
      exact ⟨f + 1, by rw [run_cond, ite_eq_left hb]; exact hf⟩
    · obtain ⟨f, hf⟩ := ihq h
      exact ⟨f + 1, by rw [run_cond, ite_eq_right hb]; exact hf⟩
  | whileDo b p ihp =>
    intro s s' h
    replace h : Spec.whileRel (fun s => b s = true) (denote p) s s' := h
    induction h with
    | exit hb => exact ⟨1, by rw [run_whileDo, ite_eq_right hb]⟩
    | step hb hR _ ihLoop =>
      obtain ⟨f₁, h₁⟩ := ihp hR
      obtain ⟨f₂, h₂⟩ := ihLoop
      refine ⟨max f₁ f₂ + 1, ?_⟩
      rw [run_whileDo, ite_eq_left hb, run_le h₁ (le_max_left f₁ f₂), Option.bind_some]
      exact run_le h₂ (le_max_right f₁ f₂)

/-- Each denoted program is deterministic: the interpreter computes a function
of the prestate, so the specification it implements has at most one poststate. -/
theorem deterministic_denote (p : Prog Var Val) (s : Spec.State Var Val) :
    Spec.Deterministic (denote p) s := by
  intro s₁ s₂ h₁ h₂
  obtain ⟨f₁, hf₁⟩ := exists_run_of_denote h₁
  obtain ⟨f₂, hf₂⟩ := exists_run_of_denote h₂
  have e₁ := run_le hf₁ (le_max_left f₁ f₂)
  have e₂ := run_le hf₂ (le_max_right f₁ f₂)
  simpa using e₁.symm.trans e₂

/-- The bridge from a Chapter 4 development to an execution: if `W ⇐ denote p`
has been proved, then every successful run of `p` satisfies `W`. -/
theorem run_sound {W : Spec (Spec.State Var Val)} {p : Prog Var Val}
    (hW : Spec.Refines W (denote p)) {f : ℕ} {s s' : Spec.State Var Val}
    (h : run f p s = some s') : W s s' :=
  hW s s' (denote_of_run h)

/-- The same for a loop developed the book's way: if `W ⇐ while b do p od` in
the refinement notation of Section 5.2.0, then every terminating run of the
loop satisfies `W`. -/
theorem run_while_sound {W : Spec (Spec.State Var Val)} {b : Spec.State Var Val → Bool}
    {p : Prog Var Val} (hW : Spec.WhileRefines W (fun s => b s = true) (denote p))
    {f : ℕ} {s s' : Spec.State Var Val} (h : run f (.whileDo b p) s = some s') : W s s' :=
  Spec.refines_whileRel _ _ hW s s' (denote_of_run h)


/-! ### A first-order syntax, and executable demonstrations

The core `Prog` above keeps expressions semantic, as `Spec.assign` does. For
demonstrations we want programs that are *data* all the way down, so here is a
tiny first-order expression syntax over three integer variables, its evaluator,
and two programs written in it. The results below are proved by `rfl`: the
kernel itself runs the interpreter.
-/

namespace Demo

/-- The demonstration state variables: the bound `n`, the index `i`, and the
accumulator `s`. -/
inductive Vr
  /-- The bound `n`. -/
  | n
  /-- The index `i`. -/
  | i
  /-- The accumulator `s`. -/
  | s
  deriving DecidableEq, Repr

/-- States over the three integer variables. -/
abbrev St := Spec.State Vr ℤ

/-- Integer expressions of the state. -/
inductive Exp where
  /-- A literal. -/
  | lit (v : ℤ) : Exp
  /-- A variable. -/
  | var (x : Vr) : Exp
  /-- Addition. -/
  | add (a b : Exp) : Exp
  /-- Subtraction. -/
  | sub (a b : Exp) : Exp
  /-- Multiplication. -/
  | mul (a b : Exp) : Exp
  deriving Repr

/-- The value of an expression in a state. -/
def Exp.eval : Exp → St → ℤ
  | .lit v, _ => v
  | .var x, s => s x
  | .add a b, s => a.eval s + b.eval s
  | .sub a b, s => a.eval s - b.eval s
  | .mul a b, s => a.eval s * b.eval s

/-- Binary expressions of the state. -/
inductive Bexp where
  /-- Equality of two expressions. -/
  | eq (a b : Exp) : Bexp
  /-- Order of two expressions. -/
  | le (a b : Exp) : Bexp
  /-- Negation. -/
  | neg (c : Bexp) : Bexp
  /-- Conjunction. -/
  | conj (c d : Bexp) : Bexp
  deriving Repr

/-- The value of a binary expression in a state. -/
def Bexp.eval : Bexp → St → Bool
  | .eq a b, s => decide (a.eval s = b.eval s)
  | .le a b, s => decide (a.eval s ≤ b.eval s)
  | .neg c, s => !c.eval s
  | .conj c d, s => c.eval s && d.eval s

/-- Programs over the demonstration state. -/
abbrev P := Prog Vr ℤ

/-- `x:= e`, with `e` in the first-order syntax. -/
def set (x : Vr) (e : Exp) : P := .assign x e.eval

/-- `if c then p else q`, with `c` in the first-order syntax. -/
def ifThen (c : Bexp) (p q : P) : P := .cond c.eval p q

/-- `while c do p od`, with `c` in the first-order syntax. -/
def loop (c : Bexp) (p : P) : P := .whileDo c.eval p

/-- The initial state: `n` as given, `i` and `s` zero. -/
def start (n : ℤ) : St := fun v => match v with | .n => n | _ => 0

/-! #### Summing `1,..n+1` -/

/-- `i:= 0. s:= 0. while i ⧧ n do (i:= i+1. s:= s+i) od`. -/
def sumTo : P :=
  .seq (set .i (.lit 0))
    (.seq (set .s (.lit 0))
      (loop (.neg (.eq (.var .i) (.var .n)))
        (.seq (set .i (.add (.var .i) (.lit 1)))
          (set .s (.add (.var .s) (.var .i))))))

-- The interpreter runs: the final state after `sumTo` from `n = 10` is `(10, 55)`.
#eval (run 100 sumTo (start 10)).map fun st => (st .i, st .s)

/-- `1 + ... + 10 = 55`, computed by the interpreter and checked by the kernel. -/
theorem sumTo_ten : (run 100 sumTo (start 10)).map (fun st => st .s) = some 55 := rfl

/-- `1 + ... + 20 = 210`. -/
theorem sumTo_twenty : (run 100 sumTo (start 20)).map (fun st => st .s) = some 210 := rfl

/-- Too little fuel is reported honestly rather than silently: the run fails. -/
theorem sumTo_no_fuel : run 5 sumTo (start 10) = none := rfl

/-! #### A loop with a proved specification

The book develops a loop by proving a while-refinement; this shows the whole
path from such a proof to an execution. -/

/-- The loop body `i:= i+1. s:= s+1`. -/
def countBody : P :=
  .seq (set .i (.add (.var .i) (.lit 1))) (set .s (.add (.var .s) (.lit 1)))

/-- The loop condition `i ⧧ n`. -/
def countCond : Bexp := .neg (.eq (.var .i) (.var .n))

/-- `while i ⧧ n do (i:= i+1. s:= s+1) od`. -/
def count : P := loop countCond countBody

/-- The specification of the counting loop: `i ≤ n ⇒ s′ = s + (n – i)`. -/
def W : Spec St := fun st st' => st .i ≤ st .n → st' .s = st .s + (st .n - st .i)

/-- The loop condition says exactly `i ⧧ n`. -/
theorem countCond_eval (st : St) : countCond.eval st = true ↔ st Vr.i ≠ st Vr.n := by
  constructor
  · intro h heq
    simp [countCond, Bexp.eval, Exp.eval, heq] at h
  · intro h
    simp [countCond, Bexp.eval, Exp.eval, h]

/-- `s′ = s + (n – i) ⇐ while i ⧧ n do (i:= i+1. s:= s+1) od`, proved the book's
way: one case for the body followed by the loop, one for the exit. -/
theorem whileRefines_W :
    Spec.WhileRefines W (fun st => countCond.eval st = true) (denote countBody) := by
  rintro st st' (⟨hb, t, hbody, hW⟩ | ⟨hb, hok⟩) hle
  · have hne : st Vr.i ≠ st Vr.n := (countCond_eval st).mp hb
    obtain ⟨u, hu, ht⟩ :
        ∃ u, Spec.assign Vr.i (Exp.eval (.add (.var .i) (.lit 1))) st u ∧
          Spec.assign Vr.s (Exp.eval (.add (.var .s) (.lit 1))) u t := hbody
    rw [Spec.assign_iff] at hu ht
    have hui : u Vr.i = st Vr.i + 1 := by simpa [Exp.eval] using hu.1
    have hun : u Vr.n = st Vr.n := hu.2 Vr.n (by decide)
    have hus : u Vr.s = st Vr.s := hu.2 Vr.s (by decide)
    have hts : t Vr.s = u Vr.s + 1 := by simpa [Exp.eval] using ht.1
    have hti : t Vr.i = u Vr.i := ht.2 Vr.i (by decide)
    have htn : t Vr.n = u Vr.n := ht.2 Vr.n (by decide)
    have hfin := hW (show t Vr.i ≤ t Vr.n by omega)
    omega
  · have heq : st Vr.i = st Vr.n := not_not.mp fun hne => hb ((countCond_eval st).mpr hne)
    rw [show st' = st from hok]
    omega

/-- The payoff: every terminating run of the counting loop satisfies the
specification proved for it. -/
theorem count_sound {f : ℕ} {st st' : St} (h : run f count st = some st')
    (hle : st Vr.i ≤ st Vr.n) : st' Vr.s = st Vr.s + (st Vr.n - st Vr.i) :=
  run_while_sound whileRefines_W h hle

-- And it does run: from `n = 7` the final state is `(7, 7)`.
#eval (run 100 count (start 7)).map fun st => (st .i, st .s)

/-- The same fact, instantiated at `n = 7` and checked by the kernel. -/
theorem count_seven : (run 100 count (start 7)).map (fun st => st .s) = some 7 := rfl

/-- A loop-free program denotes a program in the sense of Section 4.0.3. -/
example : Spec.IsProgram (denote (.seq (set .i (.lit 0)) (set .s (.lit 0)) : P)) :=
  isProgram_denote (.seq (.assign _ _) (.assign _ _))

end Demo

end Interpreter

end LaPToP.ProgramTheory
