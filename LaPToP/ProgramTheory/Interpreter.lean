import LaPToP.ProgramTheory.Programs
import LaPToP.ProgramTheory.WhileLoop
import LaPToP.ProgramTheory.Scope
import LaPToP.ProgramTheory.Arrays
import LaPToP.ProgramTheory.Assertions

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
| `.newLocal x e p` | `Spec.newLocal` (see below)                |
| `.assignAt x e`   | `Spec.assignAt` (see below)                |
| `.ensure b`       | `Spec.ensure`                              |
| `.or p q`         | `Spec.or`                                  |

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

The last two hold on the *deterministic fragment* `Interpreter.Det`, which is
every notation but the choice `p or q`: a choice has two behaviours where `run`
computes one, so no deterministic interpreter can be complete for it. The
searching interpreter `Interpreter.runAll` is (`mem_runAll_iff_eval`).

`Interpreter.run_sound` combines the first with refinement: if `W ⇐ denote p`
has been proved, then every successful run of `p` satisfies `W`. That is the
bridge from a Chapter 4 development to an actual execution.

## Fuel-free execution

Fuel is an artefact of Lean's termination checking, not of the theory.
`Interpreter.Eval p s s'` is the big-step operational semantics of `Prog` with
no budget anywhere: a nonterminating computation is simply one that relates its
prestate to no poststate. It coincides with the denotation
(`Interpreter.eval_eq_denote`) and with the fuelled interpreter
(`Interpreter.eval_iff_exists_run`, on the deterministic fragment), so all three
accounts of a program are one relation. The theorems about it are *partial correctness* — they constrain the
executions that terminate and claim nothing about termination:
`Interpreter.eval_sound`, `Interpreter.eval_while_sound`, and the loop invariant
rule `Interpreter.eval_while_invariant`, which needs no fuel and no variant.
`Interpreter.Diverges` names the computations with no poststate; the interpreter
reports them honestly by failing for every fuel
(`Interpreter.run_eq_none_of_diverges`, with the converse on the deterministic
fragment).

## Frames and local declarations

Section 5.0.1's frame notation says what a computation does *not* do, and
Section 5.0.0 declares a local variable beside the nonlocal state. Both are made
executable here. `writes p` reads a program's write set off its syntax, and
`frame_denote` proves `frame xs· denote p = denote p` whenever `writes p ⊆ xs`,
so a framed specification is discharged by a syntactic check rather than by an
argument about behaviour. `Prog.newLocal x e p` borrows the state slot `x` for
the duration of `p`, initializing it to `e` and putting back what it found;
`Spec.newLocal_eq` identifies its denotation with the book's initializing
declaration `new x: Val := e· P` under the frame that restores the slot, and
`refines_newVar_denote` shows that what is executed refines the book's
`new x: Val· P`, whose initial value is arbitrary where a machine must choose
one.

## Arrays

Section 5.1.0 warns that the Substitution Law fails for array element
assignment, because the name assigned to is not fixed by the syntax:
`A i:= e` writes the slot that `i` names in the *prestate*. `Prog.assignAt`
is that construct — assignment to a computed name — and `Spec.assignAt_seq` is
the substitution that does work, the book's "change `A i:= e` to `A:= i→e | A`
before applying any programming theory". An array on a flat state is the family
of slots it indexes, and `denote_assignAt_arr` proves that assignment to a
computed slot of such a family is exactly the book's definition of `A i:= e`
(`Spec.assignArr`, tied back to `Arrays.assignElem` on the book's record state
by `Arrays.assignElem_iff_assignArr`). `Prog.assign` is the special case with a
constant name, where the Substitution Law is sound. The write set of an element
assignment is the range of the computed name, so the frame machinery covers
arrays unchanged.

## Assertions and choice

`Prog.ensure b` succeeds without changing anything when `b` holds, and has no
poststate when it does not — the book's "when `b` is false, ... this is
unimplementable". `Interpreter.assert b` is the same program: the else-branch of
`assert` prints a message and waits until `∞`, and a machine with no clock and
no screen cannot tell that from producing nothing.
`Assertions.assert_finite` makes the identification precise — from a state at
finite time, the behaviours of `assert b` that end in finite time are exactly
`ensure b` — so the difference between the two lives entirely in the time
variable this state has not got.

`Prog.or p q` is the choice of Section 5.4.0, whose point is that an
implementation "must choose the right one to satisfy a later binary
expression". `run` resolves it as a refinement by taking the left branch
(`refines_denote_or_left`), which is sound but cannot backtrack. `runAll`
searches: it returns every poststate reachable within the fuel, so a choice
branches and a later `ensure` filters, and it is sound and complete for the
whole language (`mem_runAll_iff_eval`, `mem_runAll_iff_denote`).

## Honest deviations and scope

* Expressions are *semantic*: `e : State Var Val → Val` and `b : State Var Val → Bool`,
  matching `Spec.assign`, which takes any function of the prestate. So `Prog` is
  data only up to its embedded expression functions. The `Interpreter.Demo`
  namespace closes that gap for the demonstrations with a first-order syntax
  (`Exp`, `Bexp` over integer variables) and its own evaluator, so the example
  programs there are honest data.
* `whileDo` is the only unbounded construct. `run` executes it with fuel and
  `Eval` without; neither claims termination, and no variant/termination
  argument is formalized here. The tie to the least-fixed-point account of loops
  in Section 6.1.1 is proved in `LaPToP.RecursiveDefinition.LoopBridge`, over
  the state `ZS` that carries the time variable those axioms mention; the
  interpreter's own state has no time variable, so the bridge is at the level of
  `Spec.whileRel`, the specification `denote` gives a `whileDo`.
* A local declaration reuses a state slot, because the interpreter's state is
  flat; the book puts the local beside the nonlocal state. The two are related
  by `Spec.newLocal_eq`, at the cost of the frame condition that the slot is
  restored. Whether a declaration is a *program* in the sense of Section 4.0.3
  is not claimed: `Spec.IsProgram` has no rule for it, and restoring a borrowed
  slot is not expressible in the four notations, so `LoopFree` has no case for
  `newLocal`.
* An array is the family of state slots it indexes, not a single variable
  holding a list as in `Arrays.AS` — a flat state has no room for a list value.
  The two readings are related by `Arrays.assignElem_iff_assignArr`. Arrays of
  two dimensions and records are not given syntax of their own; on this encoding
  they are the same construct with a different index type, but that is said, not
  proved here.
* `assert` and `ensure` are the same program here, because the state has no time
  variable and no output; the book distinguishes them, and `assert` alone is
  implementable. What is proved is that a finite-time observer cannot tell them
  apart, not that they are equal.
* Out of scope in this round, and not claimed anywhere below: concurrency (`||`),
  the time variable `t`, channels and interaction, the full surface syntax of the
  book, and a command-line binary outside Lean.
-/

namespace LaPToP.ProgramTheory

universe u v w

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

/-- A loop whose condition always holds has no terminating runs: the relation of
terminating executions is `⊥`. -/
theorem whileRel_of_always (hb : ∀ s, b s) : whileRel b R = bot := by
  refine Spec.ext fun s s' => ⟨fun h => ?_, False.elim⟩
  show False
  induction h with
  | exit hb' => exact hb' (hb _)
  | step _ _ _ ih => exact ih

/-- **Partial correctness of a loop by an invariant**: if `I` holds of the
prestate and is preserved by each iteration, then every terminating execution
ends in a state satisfying `I` in which the condition is false. Nothing here
asks the loop to terminate; the conclusion is about the runs that do. -/
theorem whileRel_invariant {I : σ → Prop} (hI : ∀ s t, I s → b s → R s t → I t) :
    ∀ {s s' : σ}, whileRel b R s s' → I s → I s' ∧ ¬ b s' := by
  intro s s' h
  induction h with
  | exit hb => exact fun hs => ⟨hs, hb⟩
  | step hb hR _ ih => exact fun hs => ih (hI _ _ hs hb hR)

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
  /-- `new x: Val := e· p`: the local variable of `p` is the state slot `x`,
  initialized to `e` and restored when the scope ends. -/
  | newLocal (x : Var) (e : Spec.State Var Val → Val) (p : Prog Var Val) : Prog Var Val
  /-- `A i:= e`: assignment whose target name is computed from the prestate. -/
  | assignAt (x : Spec.State Var Val → Var) (e : Spec.State Var Val → Val) : Prog Var Val
  /-- `ensure b`: "make `b` true without changing anything". -/
  | ensure (b : Spec.State Var Val → Bool) : Prog Var Val
  /-- `p or q`, the choice of Section 5.4.0, resolved by backtracking. -/
  | or (p q : Prog Var Val) : Prog Var Val

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

/-- The deterministic fragment: every notation but the choice `p or q`. A
program in it has at most one poststate, and the fuelled `run` computes it; the
choice is the one construct for which a machine must search (`runAll`). -/
def Det : Prog Var Val → Prop
  | .ok => True
  | .assign _ _ => True
  | .assignAt _ _ => True
  | .ensure _ => True
  | .seq p q => Det p ∧ Det q
  | .cond _ p q => Det p ∧ Det q
  | .whileDo _ p => Det p
  | .newLocal _ _ p => Det p
  | .or _ _ => False

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
  | n + 1, .newLocal x e p, s =>
      (run n p (Function.update s x (e s))).map fun t => Function.update t x (s x)
  | _ + 1, .assignAt x e, s => some (Function.update s (x s) (e s))
  | _ + 1, .ensure b, s => if b s then some s else none
  | n + 1, .or p _q, s => run n p s

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

@[simp] theorem run_newLocal (n : ℕ) (x : Var) (e : Spec.State Var Val → Val) (p : Prog Var Val)
    (s : Spec.State Var Val) :
    run (n + 1) (.newLocal x e p) s =
      (run n p (Function.update s x (e s))).map fun t => Function.update t x (s x) := rfl

@[simp] theorem run_assignAt (n : ℕ) (x : Spec.State Var Val → Var)
    (e : Spec.State Var Val → Val) (s : Spec.State Var Val) :
    run (n + 1) (.assignAt x e) s = some (Function.update s (x s) (e s)) := rfl

@[simp] theorem run_ensure (n : ℕ) (b : Spec.State Var Val → Bool) (s : Spec.State Var Val) :
    run (n + 1) (.ensure b) s = if b s then some s else none := rfl

@[simp] theorem run_or (n : ℕ) (p q : Prog Var Val) (s : Spec.State Var Val) :
    run (n + 1) (.or p q) s = run n p s := rfl

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
    | newLocal x e p =>
      simp only [run_newLocal] at h ⊢
      cases hp : run n p (Function.update s x (e s)) with
      | none => rw [hp] at h; simp at h
      | some t => rw [hp] at h; rw [ih hp hnm]; exact h
    | assignAt x e => simpa using h
    | ensure b =>
      simp only [run_ensure] at h ⊢
      split_ifs at h ⊢ with hb
      exact h
    | or p q =>
      simp only [run_or] at h ⊢
      exact ih h hnm

/-! ### Denotation into the theory of Chapter 4 -/

/-- The denotation of a program as a specification: exactly the notations of
Section 4.0, with the loop denoted by its terminating-run relation. -/
def denote : Prog Var Val → Spec (Spec.State Var Val)
  | .ok => Spec.ok
  | .assign x e => Spec.assign x e
  | .seq p q => Spec.seq (denote p) (denote q)
  | .cond b p q => Spec.cond (fun s => b s = true) (denote p) (denote q)
  | .whileDo b p => Spec.whileRel (fun s => b s = true) (denote p)
  | .newLocal x e p => Spec.newLocal x e (denote p)
  | .assignAt x e => Spec.assignAt x e
  | .ensure b => Spec.ensure fun s => b s = true
  | .or p q => Spec.or (denote p) (denote q)

@[simp] theorem denote_ok : denote (Var := Var) (Val := Val) .ok = Spec.ok := rfl

@[simp] theorem denote_assign (x : Var) (e : Spec.State Var Val → Val) :
    denote (.assign x e) = Spec.assign x e := rfl

@[simp] theorem denote_seq (p q : Prog Var Val) :
    denote (.seq p q) = Spec.seq (denote p) (denote q) := rfl

@[simp] theorem denote_cond (b : Spec.State Var Val → Bool) (p q : Prog Var Val) :
    denote (.cond b p q) = Spec.cond (fun s => b s = true) (denote p) (denote q) := rfl

@[simp] theorem denote_whileDo (b : Spec.State Var Val → Bool) (p : Prog Var Val) :
    denote (.whileDo b p) = Spec.whileRel (fun s => b s = true) (denote p) := rfl

@[simp] theorem denote_newLocal (x : Var) (e : Spec.State Var Val → Val) (p : Prog Var Val) :
    denote (.newLocal x e p) = Spec.newLocal x e (denote p) := rfl

@[simp] theorem denote_assignAt (x : Spec.State Var Val → Var) (e : Spec.State Var Val → Val) :
    denote (.assignAt x e) = Spec.assignAt x e := rfl

@[simp] theorem denote_ensure (b : Spec.State Var Val → Bool) :
    denote (.ensure b) = Spec.ensure (fun s => b s = true) := rfl

@[simp] theorem denote_or (p q : Prog Var Val) :
    denote (.or p q) = Spec.or (denote p) (denote q) := rfl

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
    | newLocal x e p =>
      simp only [run_newLocal] at h
      cases hp : run n p (Function.update s x (e s)) with
      | none => rw [hp] at h; simp at h
      | some t =>
        rw [hp] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨t, ih hp, h.symm⟩
    | assignAt x e =>
      simp only [run_assignAt, Option.some.injEq] at h
      exact h.symm
    | ensure b =>
      simp only [run_ensure] at h
      split_ifs at h with hb
      simp only [Option.some.injEq] at h
      exact ⟨hb, h.symm⟩
    | or p q =>
      simp only [run_or] at h
      exact Or.inl (ih h)

/-- **Completeness on the deterministic fragment**: every behaviour allowed by
the denotation of a program without a choice is achieved by a run with enough
fuel. The choice is exactly the construct `run` cannot be complete for — it
takes the left branch (`Spec.or_refines_left`, "normally this choice is made as
a refinement") where the specification allows both; `runAll` searches. -/
theorem exists_run_of_denote : ∀ {p : Prog Var Val}, Det p →
    ∀ {s s' : Spec.State Var Val}, denote p s s' → ∃ f, run f p s = some s' := by
  intro p
  induction p with
  | ok =>
    intro _ s s' h
    exact ⟨1, by rw [run_ok, show s' = s from h]⟩
  | assign x e =>
    intro _ s s' h
    exact ⟨1, by rw [run_assign, show s' = Function.update s x (e s) from h]⟩
  | seq p q ihp ihq =>
    intro hd s s' h
    obtain ⟨t, hp, hq⟩ : ∃ t, denote p s t ∧ denote q t s' := h
    obtain ⟨f₁, h₁⟩ := ihp hd.1 hp
    obtain ⟨f₂, h₂⟩ := ihq hd.2 hq
    refine ⟨max f₁ f₂ + 1, ?_⟩
    rw [run_seq, run_le h₁ (le_max_left f₁ f₂), Option.bind_some]
    exact run_le h₂ (le_max_right f₁ f₂)
  | cond b p q ihp ihq =>
    intro hd s s' h
    obtain ⟨hb, h⟩ | ⟨hb, h⟩ :
        ((b s = true) ∧ denote p s s') ∨ (¬ (b s = true) ∧ denote q s s') := h
    · obtain ⟨f, hf⟩ := ihp hd.1 h
      exact ⟨f + 1, by rw [run_cond, ite_eq_left hb]; exact hf⟩
    · obtain ⟨f, hf⟩ := ihq hd.2 h
      exact ⟨f + 1, by rw [run_cond, ite_eq_right hb]; exact hf⟩
  | whileDo b p ihp =>
    intro hd s s' h
    replace h : Spec.whileRel (fun s => b s = true) (denote p) s s' := h
    induction h with
    | exit hb => exact ⟨1, by rw [run_whileDo, ite_eq_right hb]⟩
    | step hb hR _ ihLoop =>
      obtain ⟨f₁, h₁⟩ := ihp hd hR
      obtain ⟨f₂, h₂⟩ := ihLoop
      refine ⟨max f₁ f₂ + 1, ?_⟩
      rw [run_whileDo, ite_eq_left hb, run_le h₁ (le_max_left f₁ f₂), Option.bind_some]
      exact run_le h₂ (le_max_right f₁ f₂)
  | newLocal x e p ihp =>
    intro hd s s' h
    obtain ⟨t, hp, ht⟩ :
        ∃ t, denote p (Function.update s x (e s)) t ∧ s' = Function.update t x (s x) := h
    obtain ⟨f, hf⟩ := ihp hd hp
    exact ⟨f + 1, by rw [run_newLocal, hf, Option.map_some, ht]⟩
  | assignAt x e =>
    intro _ s s' h
    exact ⟨1, by rw [run_assignAt, show s' = Function.update s (x s) (e s) from h]⟩
  | ensure b =>
    intro _ s s' h
    obtain ⟨hb, hok⟩ : (b s = true) ∧ s' = s := h
    exact ⟨1, by rw [run_ensure, ite_eq_left hb, hok]⟩
  | or p q _ _ => intro hd; exact hd.elim

/-- Each denoted program is deterministic: the interpreter computes a function
of the prestate, so the specification it implements has at most one poststate. -/
theorem deterministic_denote {p : Prog Var Val} (hp : Det p) (s : Spec.State Var Val) :
    Spec.Deterministic (denote p) s := by
  intro s₁ s₂ h₁ h₂
  obtain ⟨f₁, hf₁⟩ := exists_run_of_denote hp h₁
  obtain ⟨f₂, hf₂⟩ := exists_run_of_denote hp h₂
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


/-! ### Fuel-free execution

`run` needs a fuel budget to be a total Lean function. That is an artefact of
Lean's termination checking, not of the theory: execution itself is a relation
between a program, a prestate and a poststate, and a nonterminating computation
is simply one that relates the prestate to nothing. `Eval` is that relation —
the big-step operational semantics of `Prog`, defined without any budget — and
it coincides exactly with `denote` (`eval_eq_denote`), so the fuel-free account
of execution and the Chapter 4 account of the same program are the same
relation. Fuelled runs are the derivations of `Eval` that a budget can reach
(`eval_iff_exists_run`).

What this gives, and what it does not: `Eval p s s'` says that `p` *can* finish
in `s'`, so the theorems below are partial correctness — they constrain the runs
that terminate and say nothing about whether a run terminates. A program with no
poststate at all is `Diverges`, and its `run` fails for every fuel.
-/

/-- `Eval p s s'`: started in state `s`, the program `p` terminates in state
`s'`. The fuel-free account of execution: a budget appears nowhere, and
nontermination is the absence of a derivation rather than a failure value. -/
inductive Eval : Prog Var Val → Spec.State Var Val → Spec.State Var Val → Prop
  /-- `ok` terminates immediately in the prestate. -/
  | ok {s : Spec.State Var Val} : Eval .ok s s
  /-- `x:= e` terminates in the state with `x` replaced by the value of `e`. -/
  | assign {x : Var} {e : Spec.State Var Val → Val} {s : Spec.State Var Val} :
      Eval (.assign x e) s (Function.update s x (e s))
  /-- `p. q` terminates by terminating `p` and then `q`. -/
  | seq {p q : Prog Var Val} {s t s' : Spec.State Var Val} :
      Eval p s t → Eval q t s' → Eval (.seq p q) s s'
  /-- `if b then p else q` with `b` true terminates as `p` does. -/
  | condTrue {b : Spec.State Var Val → Bool} {p q : Prog Var Val}
      {s s' : Spec.State Var Val} (hb : b s = true) :
      Eval p s s' → Eval (.cond b p q) s s'
  /-- `if b then p else q` with `b` false terminates as `q` does. -/
  | condFalse {b : Spec.State Var Val → Bool} {p q : Prog Var Val}
      {s s' : Spec.State Var Val} (hb : b s = false) :
      Eval q s s' → Eval (.cond b p q) s s'
  /-- `while b do p od` with `b` true takes one iteration and continues. -/
  | whileTrue {b : Spec.State Var Val → Bool} {p : Prog Var Val}
      {s t s' : Spec.State Var Val} (hb : b s = true) :
      Eval p s t → Eval (.whileDo b p) t s' → Eval (.whileDo b p) s s'
  /-- `while b do p od` with `b` false exits at once. -/
  | whileFalse {b : Spec.State Var Val → Bool} {p : Prog Var Val}
      {s : Spec.State Var Val} (hb : b s = false) : Eval (.whileDo b p) s s
  /-- `new x := e· p` runs `p` with the slot `x` holding `e`, and puts back what
  the slot held before. -/
  | newLocal {x : Var} {e : Spec.State Var Val → Val} {p : Prog Var Val}
      {s t : Spec.State Var Val} :
      Eval p (Function.update s x (e s)) t →
        Eval (.newLocal x e p) s (Function.update t x (s x))
  /-- `A i:= e` computes its target name from the prestate and assigns to it. -/
  | assignAt {x : Spec.State Var Val → Var} {e : Spec.State Var Val → Val}
      {s : Spec.State Var Val} : Eval (.assignAt x e) s (Function.update s (x s) (e s))
  /-- `ensure b` succeeds without changing anything when `b` holds, and has no
  poststate at all when it does not. -/
  | ensure {b : Spec.State Var Val → Bool} {s : Spec.State Var Val} (hb : b s = true) :
      Eval (.ensure b) s s
  /-- `p or q` can behave as `p`. -/
  | orLeft {p q : Prog Var Val} {s s' : Spec.State Var Val} :
      Eval p s s' → Eval (.or p q) s s'
  /-- `p or q` can behave as `q`. -/
  | orRight {p q : Prog Var Val} {s s' : Spec.State Var Val} :
      Eval q s s' → Eval (.or p q) s s'

/-- A fuelled run is an execution: the budget only restricts which derivations
are reachable, not what they mean. -/
theorem eval_of_run : ∀ {f : ℕ} {p : Prog Var Val} {s s' : Spec.State Var Val},
    run f p s = some s' → Eval p s s' := by
  intro f
  induction f with
  | zero => intro p s s' h; simp at h
  | succ n ih =>
    intro p s s' h
    cases p with
    | ok =>
      simp only [run_ok, Option.some.injEq] at h
      exact h ▸ .ok
    | assign x e =>
      simp only [run_assign, Option.some.injEq] at h
      exact h ▸ .assign
    | seq p q =>
      simp only [run_seq] at h
      cases hp : run n p s with
      | none => simp [hp] at h
      | some t =>
        simp only [hp, Option.bind_some] at h
        exact .seq (ih hp) (ih h)
    | cond b p q =>
      simp only [run_cond] at h
      split_ifs at h with hb
      · exact .condTrue hb (ih h)
      · exact .condFalse (by simpa using hb) (ih h)
    | whileDo b p =>
      simp only [run_whileDo] at h
      split_ifs at h with hb
      · cases hp : run n p s with
        | none => simp [hp] at h
        | some t =>
          simp only [hp, Option.bind_some] at h
          exact .whileTrue hb (ih hp) (ih h)
      · simp only [Option.some.injEq] at h
        exact h ▸ .whileFalse (by simpa using hb)
    | newLocal x e p =>
      simp only [run_newLocal] at h
      cases hp : run n p (Function.update s x (e s)) with
      | none => rw [hp] at h; simp at h
      | some t =>
        rw [hp] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        exact .newLocal (ih hp)
    | assignAt x e =>
      simp only [run_assignAt, Option.some.injEq] at h
      exact h ▸ .assignAt
    | ensure b =>
      simp only [run_ensure] at h
      split_ifs at h with hb
      simp only [Option.some.injEq] at h
      exact h ▸ .ensure hb
    | or p q =>
      simp only [run_or] at h
      exact .orLeft (ih h)

/-- **Partial correctness**: an execution that terminates satisfies the denoted
specification. -/
theorem denote_of_eval : ∀ {p : Prog Var Val} {s s' : Spec.State Var Val},
    Eval p s s' → denote p s s' := by
  intro p s s' h
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

/-- **Completeness**: every behaviour the denotation allows is a terminating
execution. Together with `denote_of_eval`, execution and denotation are the same
relation. -/
theorem eval_of_denote : ∀ {p : Prog Var Val} {s s' : Spec.State Var Val},
    denote p s s' → Eval p s s' := by
  intro p
  induction p with
  | ok => intro s s' h; exact h ▸ .ok
  | assign x e => intro s s' h; exact h ▸ .assign
  | seq p q ihp ihq =>
    intro s s' h
    obtain ⟨t, hp, hq⟩ : ∃ t, denote p s t ∧ denote q t s' := h
    exact .seq (ihp hp) (ihq hq)
  | cond b p q ihp ihq =>
    intro s s' h
    obtain ⟨hb, h⟩ | ⟨hb, h⟩ :
        ((b s = true) ∧ denote p s s') ∨ (¬ (b s = true) ∧ denote q s s') := h
    · exact .condTrue hb (ihp h)
    · exact .condFalse (by simpa using hb) (ihq h)
  | whileDo b p ihp =>
    intro s s' h
    replace h : Spec.whileRel (fun s => b s = true) (denote p) s s' := h
    induction h with
    | exit hb => exact .whileFalse (by simpa using hb)
    | step hb hR _ ihw => exact .whileTrue hb (ihp hR) ihw
  | newLocal x e p ihp =>
    intro s s' h
    obtain ⟨t, hp, ht⟩ :
        ∃ t, denote p (Function.update s x (e s)) t ∧ s' = Function.update t x (s x) := h
    subst ht
    exact .newLocal (ihp hp)
  | assignAt x e =>
    intro s s' h
    exact h ▸ .assignAt
  | ensure b =>
    intro s s' h
    obtain ⟨hb, hok⟩ : (b s = true) ∧ s' = s := h
    subst hok
    exact .ensure hb
  | or p q ihp ihq =>
    intro s s' h
    exact h.elim (fun hp => .orLeft (ihp hp)) fun hq => .orRight (ihq hq)

/-- Execution *is* the denotation: the fuel-free operational semantics and the
Chapter 4 specification of a program are one relation. -/
theorem eval_eq_denote (p : Prog Var Val) : Eval p = denote p :=
  Spec.ext fun _ _ => ⟨denote_of_eval, eval_of_denote⟩

/-- A terminating execution is reached by some fuel. -/
theorem exists_run_of_eval {p : Prog Var Val} (hp : Det p) {s s' : Spec.State Var Val}
    (h : Eval p s s') : ∃ f, run f p s = some s' :=
  exists_run_of_denote hp (denote_of_eval h)

/-- The fuelled interpreter computes exactly the fuel-free executions. -/
theorem eval_iff_exists_run {p : Prog Var Val} (hp : Det p) {s s' : Spec.State Var Val} :
    Eval p s s' ↔ ∃ f, run f p s = some s' :=
  ⟨exists_run_of_eval hp, fun ⟨_, h⟩ => eval_of_run h⟩

/-- Execution is deterministic. -/
theorem eval_unique {p : Prog Var Val} (hp : Det p) {s s₁ s₂ : Spec.State Var Val}
    (h₁ : Eval p s s₁) (h₂ : Eval p s s₂) : s₁ = s₂ :=
  deterministic_denote hp s s₁ s₂ (denote_of_eval h₁) (denote_of_eval h₂)

/-- The fuel-free counterpart of `run_sound`: if `W ⇐ denote p` has been proved,
then every terminating execution of `p` satisfies `W`. This is partial
correctness — it says nothing about whether `p` terminates. -/
theorem eval_sound {W : Spec (Spec.State Var Val)} {p : Prog Var Val}
    (hW : Spec.Refines W (denote p)) {s s' : Spec.State Var Val} (h : Eval p s s') : W s s' :=
  hW s s' (denote_of_eval h)

/-- The fuel-free counterpart of `run_while_sound`: a loop developed the book's
way satisfies its specification on every terminating execution. -/
theorem eval_while_sound {W : Spec (Spec.State Var Val)} {b : Spec.State Var Val → Bool}
    {p : Prog Var Val} (hW : Spec.WhileRefines W (fun s => b s = true) (denote p))
    {s s' : Spec.State Var Val} (h : Eval (.whileDo b p) s s') : W s s' :=
  Spec.refines_whileRel _ _ hW s s' (denote_of_eval h)

/-- **The loop invariant rule**, fuel-free: if `I` holds of the prestate and each
iteration preserves it, then every terminating execution of the loop ends in a
state satisfying `I` with the condition false. No termination argument, and no
fuel, enters the statement or the proof. -/
theorem eval_while_invariant {b : Spec.State Var Val → Bool} {p : Prog Var Val}
    {I : Spec.State Var Val → Prop} (hI : ∀ s t, I s → b s = true → Eval p s t → I t)
    {s s' : Spec.State Var Val} (h : Eval (.whileDo b p) s s') (hs : I s) :
    I s' ∧ b s' = false := by
  have h' : Spec.whileRel (fun s => b s = true) (denote p) s s' := denote_of_eval h
  obtain ⟨hI', hb⟩ :=
    Spec.whileRel_invariant _ _ (fun u v hu hb hd => hI u v hu hb (eval_of_denote hd)) h' hs
  exact ⟨hI', by simpa using hb⟩

/-- `p` produces nothing from `s`: no state is a poststate. For a loop that is
nontermination; for `ensure b` with `b` false it is unimplementability — the
book's "when `b` is false, ... this is unimplementable". A machine cannot tell
the two apart, and the name is chosen for the first. -/
def Diverges (p : Prog Var Val) (s : Spec.State Var Val) : Prop := ∀ s', ¬ Eval p s s'

/-- A computation with no poststate is reported honestly by the interpreter: the
run fails for every fuel, rather than returning a wrong answer. -/
theorem run_eq_none_of_diverges {p : Prog Var Val} {s : Spec.State Var Val}
    (h : Diverges p s) (f : ℕ) : run f p s = none := by
  cases hr : run f p s with
  | none => rfl
  | some s' => exact absurd (eval_of_run hr) (h s')

/-- And on the deterministic fragment the converse holds: a run that fails for
every fuel is a computation with no poststate. (With a choice it need not: the
fuelled interpreter takes the left branch, so its failure says nothing about the
right one.) -/
theorem diverges_iff {p : Prog Var Val} (hp : Det p) {s : Spec.State Var Val} :
    Diverges p s ↔ ∀ f, run f p s = none := by
  refine ⟨run_eq_none_of_diverges, fun h s' he => ?_⟩
  obtain ⟨f, hf⟩ := exists_run_of_eval hp he
  rw [h f] at hf
  simp at hf

/-- A loop whose condition always holds diverges. -/
theorem diverges_whileDo {b : Spec.State Var Val → Bool} {p : Prog Var Val}
    (hb : ∀ s, b s = true) (s : Spec.State Var Val) : Diverges (.whileDo b p) s := by
  intro s' h
  have := denote_of_eval h
  rw [denote_whileDo, Spec.whileRel_of_always _ _ fun s => hb s] at this
  exact this

/-! ### Assertions, choice, and search

Section 5.4 defines `assert b = if b then ok else screen! "error". wait until ∞`
and Section 5.4.0 `ensure b = b ∧ ok`, together with the choice `P or Q`, whose
point is that an implementation "must choose the right one to satisfy a later
binary expression". All three are now syntax.

`ensure b` is `Prog.ensure`: it succeeds without changing anything when `b`
holds, and has no poststate when it does not — the book's "when `b` is false,
... this is unimplementable". `assert b` is the same program: its else-branch
prints a message and waits until `∞`, and a machine with no clock and no screen
cannot distinguish that from producing nothing. `Assertions.assert_finite` is
that identification made precise — from a state at finite time, the behaviours
of `assert b` that end in finite time are exactly `ensure b` — so the difference
between an assertion (implementable, by waiting forever) and an `ensure`
(unimplementable) lives entirely in the time variable this state has not got.

The choice is `Prog.or`. It is the one construct the fuelled `run` cannot be
complete for: `run` takes the left branch, which is the book's "normally this
choice is made as a refinement" — sound, but unable to backtrack. `runAll`
searches instead, returning every poststate reachable within the fuel, so a
choice branches and a later `ensure` filters; it is complete for the whole
language (`mem_runAll_iff_eval`).
-/

/-- `assert b`, as a machine with no clock executes it. The error message is not
modelled and the wait until `∞` is indistinguishable from producing nothing, so
what is left is `ensure b`; `Assertions.assert_finite` proves that this is all of
`assert b` that a finite-time observer can see. -/
def assert (b : Spec.State Var Val → Bool) : Prog Var Val := .ensure b

/-- The deterministic interpreter resolves a choice as a refinement: what it runs
implements the choice (`Spec.or_refines_left`), but only the left branch of it. -/
theorem refines_denote_or_left (p q : Prog Var Val) :
    Spec.Refines (denote (.or p q)) (denote p) :=
  Spec.or_refines_left _ _

/-- `runAll fuel p s` is the list of every state `p` can reach from `s` within
the fuel: a choice branches, an `ensure` filters, and the other notations are as
in `run`. -/
def runAll : ℕ → Prog Var Val → Spec.State Var Val → List (Spec.State Var Val)
  | 0, _, _ => []
  | _ + 1, .ok, s => [s]
  | _ + 1, .assign x e, s => [Function.update s x (e s)]
  | n + 1, .seq p q, s => (runAll n p s).flatMap (runAll n q)
  | n + 1, .cond b p q, s => if b s then runAll n p s else runAll n q s
  | n + 1, .whileDo b p, s =>
      if b s then (runAll n p s).flatMap (runAll n (.whileDo b p)) else [s]
  | n + 1, .newLocal x e p, s =>
      (runAll n p (Function.update s x (e s))).map fun t => Function.update t x (s x)
  | _ + 1, .assignAt x e, s => [Function.update s (x s) (e s)]
  | _ + 1, .ensure b, s => if b s then [s] else []
  | n + 1, .or p q, s => runAll n p s ++ runAll n q s

@[simp] theorem runAll_zero (p : Prog Var Val) (s : Spec.State Var Val) :
    runAll 0 p s = [] := by cases p <;> rfl

@[simp] theorem runAll_ok (n : ℕ) (s : Spec.State Var Val) : runAll (n + 1) .ok s = [s] := rfl

@[simp] theorem runAll_assign (n : ℕ) (x : Var) (e : Spec.State Var Val → Val)
    (s : Spec.State Var Val) :
    runAll (n + 1) (.assign x e) s = [Function.update s x (e s)] := rfl

@[simp] theorem runAll_seq (n : ℕ) (p q : Prog Var Val) (s : Spec.State Var Val) :
    runAll (n + 1) (.seq p q) s = (runAll n p s).flatMap (runAll n q) := rfl

@[simp] theorem runAll_cond (n : ℕ) (b : Spec.State Var Val → Bool) (p q : Prog Var Val)
    (s : Spec.State Var Val) :
    runAll (n + 1) (.cond b p q) s = if b s then runAll n p s else runAll n q s := rfl

@[simp] theorem runAll_whileDo (n : ℕ) (b : Spec.State Var Val → Bool) (p : Prog Var Val)
    (s : Spec.State Var Val) :
    runAll (n + 1) (.whileDo b p) s =
      if b s then (runAll n p s).flatMap (runAll n (.whileDo b p)) else [s] := rfl

@[simp] theorem runAll_newLocal (n : ℕ) (x : Var) (e : Spec.State Var Val → Val)
    (p : Prog Var Val) (s : Spec.State Var Val) :
    runAll (n + 1) (.newLocal x e p) s =
      (runAll n p (Function.update s x (e s))).map fun t => Function.update t x (s x) := rfl

@[simp] theorem runAll_assignAt (n : ℕ) (x : Spec.State Var Val → Var)
    (e : Spec.State Var Val → Val) (s : Spec.State Var Val) :
    runAll (n + 1) (.assignAt x e) s = [Function.update s (x s) (e s)] := rfl

@[simp] theorem runAll_ensure (n : ℕ) (b : Spec.State Var Val → Bool) (s : Spec.State Var Val) :
    runAll (n + 1) (.ensure b) s = if b s then [s] else [] := rfl

@[simp] theorem runAll_or (n : ℕ) (p q : Prog Var Val) (s : Spec.State Var Val) :
    runAll (n + 1) (.or p q) s = runAll n p s ++ runAll n q s := rfl

/-- More fuel never loses a result of the search. -/
theorem runAll_le : ∀ {f g : ℕ} {p : Prog Var Val} {s s' : Spec.State Var Val},
    s' ∈ runAll f p s → f ≤ g → s' ∈ runAll g p s := by
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
      simp only [runAll_seq, List.mem_flatMap] at h ⊢
      obtain ⟨t, ht, hq⟩ := h
      exact ⟨t, ih ht hnm, ih hq hnm⟩
    | cond b p q =>
      simp only [runAll_cond] at h ⊢
      split_ifs at h ⊢ with hb
      · exact ih h hnm
      · exact ih h hnm
    | whileDo b p =>
      simp only [runAll_whileDo] at h ⊢
      split_ifs at h ⊢ with hb
      · simp only [List.mem_flatMap] at h ⊢
        obtain ⟨t, ht, hw⟩ := h
        exact ⟨t, ih ht hnm, ih hw hnm⟩
      · exact h
    | newLocal x e p =>
      simp only [runAll_newLocal, List.mem_map] at h ⊢
      obtain ⟨t, ht, hst⟩ := h
      exact ⟨t, ih ht hnm, hst⟩
    | assignAt x e => simpa using h
    | ensure b =>
      simp only [runAll_ensure] at h ⊢
      split_ifs at h ⊢ with hb
      · exact h
      · simp at h
    | or p q =>
      simp only [runAll_or, List.mem_append] at h ⊢
      exact h.imp (fun hp => ih hp hnm) fun hq => ih hq hnm

/-- **Soundness of the search**: every state it finds is an execution. -/
theorem eval_of_mem_runAll : ∀ {f : ℕ} {p : Prog Var Val} {s s' : Spec.State Var Val},
    s' ∈ runAll f p s → Eval p s s' := by
  intro f
  induction f with
  | zero => intro p s s' h; simp at h
  | succ n ih =>
    intro p s s' h
    cases p with
    | ok =>
      simp only [runAll_ok, List.mem_singleton] at h
      subst h; exact .ok
    | assign x e =>
      simp only [runAll_assign, List.mem_singleton] at h
      subst h; exact .assign
    | seq p q =>
      simp only [runAll_seq, List.mem_flatMap] at h
      obtain ⟨t, ht, hq⟩ := h
      exact .seq (ih ht) (ih hq)
    | cond b p q =>
      simp only [runAll_cond] at h
      split_ifs at h with hb
      · exact .condTrue hb (ih h)
      · exact .condFalse (by simpa using hb) (ih h)
    | whileDo b p =>
      simp only [runAll_whileDo] at h
      split_ifs at h with hb
      · simp only [List.mem_flatMap] at h
        obtain ⟨t, ht, hw⟩ := h
        exact .whileTrue hb (ih ht) (ih hw)
      · simp only [List.mem_singleton] at h
        subst h; exact .whileFalse (by simpa using hb)
    | newLocal x e p =>
      simp only [runAll_newLocal, List.mem_map] at h
      obtain ⟨t, ht, hst⟩ := h
      subst hst
      exact .newLocal (ih ht)
    | assignAt x e =>
      simp only [runAll_assignAt, List.mem_singleton] at h
      subst h; exact .assignAt
    | ensure b =>
      simp only [runAll_ensure] at h
      split_ifs at h with hb
      · simp only [List.mem_singleton] at h
        subst h; exact .ensure hb
      · simp at h
    | or p q =>
      simp only [runAll_or, List.mem_append] at h
      exact h.elim (fun hp => .orLeft (ih hp)) fun hq => .orRight (ih hq)

/-- **Completeness of the search**, for the whole language, the choice included:
every execution is found with enough fuel. -/
theorem exists_mem_runAll_of_eval : ∀ {p : Prog Var Val} {s s' : Spec.State Var Val},
    Eval p s s' → ∃ f, s' ∈ runAll f p s := by
  intro p s s' h
  induction h with
  | ok => exact ⟨1, by simp⟩
  | assign => exact ⟨1, by simp⟩
  | @seq p q s t s' _ _ ihp ihq =>
    obtain ⟨f₁, h₁⟩ := ihp
    obtain ⟨f₂, h₂⟩ := ihq
    refine ⟨max f₁ f₂ + 1, ?_⟩
    simp only [runAll_seq, List.mem_flatMap]
    exact ⟨t, runAll_le h₁ (le_max_left _ _), runAll_le h₂ (le_max_right _ _)⟩
  | condTrue hb _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simpa [hb] using hf⟩
  | condFalse hb _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simpa [hb] using hf⟩
  | @whileTrue b p s t s' hb _ _ ihp ihw =>
    obtain ⟨f₁, h₁⟩ := ihp
    obtain ⟨f₂, h₂⟩ := ihw
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hmem : s' ∈ (runAll (max f₁ f₂) p s).flatMap (runAll (max f₁ f₂) (.whileDo b p)) := by
      simp only [List.mem_flatMap]
      exact ⟨t, runAll_le h₁ (le_max_left _ _), runAll_le h₂ (le_max_right _ _)⟩
    simpa [hb] using hmem
  | whileFalse hb => exact ⟨1, by simp [hb]⟩
  | @newLocal x e p s t _ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    simp only [runAll_newLocal, List.mem_map]
    exact ⟨t, hf, rfl⟩
  | assignAt => exact ⟨1, by simp⟩
  | ensure hb => exact ⟨1, by simp [hb]⟩
  | orLeft _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simp only [runAll_or, List.mem_append]; exact Or.inl hf⟩
  | orRight _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f + 1, by simp only [runAll_or, List.mem_append]; exact Or.inr hf⟩

/-- The searching interpreter computes exactly the executions — and so, by
`eval_eq_denote`, exactly the denotation. Unlike `run`, it needs no hypothesis:
the choice is searched, not resolved. -/
theorem mem_runAll_iff_eval {p : Prog Var Val} {s s' : Spec.State Var Val} :
    (∃ f, s' ∈ runAll f p s) ↔ Eval p s s' :=
  ⟨fun ⟨_, h⟩ => eval_of_mem_runAll h, exists_mem_runAll_of_eval⟩

/-- Hence the search is sound and complete for the specification a program
denotes. -/
theorem mem_runAll_iff_denote {p : Prog Var Val} {s s' : Spec.State Var Val} :
    (∃ f, s' ∈ runAll f p s) ↔ denote p s s' :=
  mem_runAll_iff_eval.trans ⟨denote_of_eval, eval_of_denote⟩

/-! ### Frames and local declarations

Section 5.0.1 writes `frame x, y· P` for "`P`, and all other variables are
unchanged", and Section 5.0.0 declares a local variable beside the nonlocal
state. Neither is executable as it stands: a frame is a claim about what a
computation does *not* do, and a machine with one flat state has no room beside
it. Both become executable here.

The frame is discharged statically. `writes p` is the set of variables a program
can assign to — computed from the syntax, with a local declaration hiding its own
variable — and `frame_denote` says that for `writes p ⊆ xs` the framed
specification and the program's denotation are the same relation. So
`frame xs· P ⇐ p` needs no proof about `p`'s behaviour beyond a syntactic check.

The declaration borrows a slot. `Prog.newLocal x e p` runs `p` with the state
slot `x` holding `e`, and puts back what the slot held before; its denotation is
`Spec.newLocal`, which `Spec.newLocal_eq` identifies with the book's
initializing declaration `new x: Val := e· P` framed to restore the slot. Since
the interpreter must choose the local's initial value where the book leaves it
arbitrary, what is executed *refines* the book's `new x: Val· P`
(`refines_newVar_denote`); that is the honest direction, and it is the direction
a development needs.
-/

/-- The variables a program can assign to, read off its syntax. A local
declaration hides its own variable: whatever `p` writes to `x` inside
`new x := e· p` is put back when the scope ends. -/
def writes : Prog Var Val → Set Var
  | .ok => ∅
  | .assign x _ => {x}
  | .seq p q => writes p ∪ writes q
  | .cond _ p q => writes p ∪ writes q
  | .whileDo _ p => writes p
  | .newLocal x _ p => writes p \ {x}
  | .assignAt x _ => Set.range x
  | .ensure _ => ∅
  | .or p q => writes p ∪ writes q

omit [DecidableEq Var] in
@[simp] theorem writes_ok : writes (Prog.ok : Prog Var Val) = ∅ := rfl

omit [DecidableEq Var] in
@[simp] theorem writes_assign (x : Var) (e : Spec.State Var Val → Val) :
    writes (.assign x e) = {x} := rfl

omit [DecidableEq Var] in
@[simp] theorem writes_seq (p q : Prog Var Val) : writes (.seq p q) = writes p ∪ writes q := rfl

omit [DecidableEq Var] in
@[simp] theorem writes_cond (b : Spec.State Var Val → Bool) (p q : Prog Var Val) :
    writes (.cond b p q) = writes p ∪ writes q := rfl

omit [DecidableEq Var] in
@[simp] theorem writes_whileDo (b : Spec.State Var Val → Bool) (p : Prog Var Val) :
    writes (.whileDo b p) = writes p := rfl

omit [DecidableEq Var] in
@[simp] theorem writes_newLocal (x : Var) (e : Spec.State Var Val → Val) (p : Prog Var Val) :
    writes (.newLocal x e p) = writes p \ {x} := rfl

omit [DecidableEq Var] in
@[simp] theorem writes_assignAt (x : Spec.State Var Val → Var) (e : Spec.State Var Val → Val) :
    writes (.assignAt x e) = Set.range x := rfl

omit [DecidableEq Var] in
@[simp] theorem writes_ensure (b : Spec.State Var Val → Bool) :
    writes (.ensure b) = (∅ : Set Var) := rfl

omit [DecidableEq Var] in
@[simp] theorem writes_or (p q : Prog Var Val) : writes (.or p q) = writes p ∪ writes q := rfl

/-- A terminating execution changes no variable outside the program's write set.
This is the frame condition of Section 5.0.1, established once and for all from
the syntax. -/
theorem unchanged_of_eval : ∀ {p : Prog Var Val} {s s' : Spec.State Var Val},
    Eval p s s' → ∀ v ∉ writes p, s' v = s v := by
  intro p s s' h
  induction h with
  | ok => intro _ _; rfl
  | @assign x e s =>
    intro v hv
    simp only [writes_assign, Set.mem_singleton_iff] at hv
    exact Function.update_of_ne hv _ _
  | seq _ _ ihp ihq =>
    intro v hv
    simp only [writes_seq, Set.mem_union, not_or] at hv
    exact (ihq v hv.2).trans (ihp v hv.1)
  | condTrue _ _ ih =>
    intro v hv
    simp only [writes_cond, Set.mem_union, not_or] at hv
    exact ih v hv.1
  | condFalse _ _ ih =>
    intro v hv
    simp only [writes_cond, Set.mem_union, not_or] at hv
    exact ih v hv.2
  | whileTrue _ _ _ ihp ihw =>
    intro v hv
    simp only [writes_whileDo] at hv ⊢
    exact (ihw v hv).trans (ihp v hv)
  | whileFalse => intro _ _; rfl
  | @newLocal x e p s t _ ih =>
    intro v hv
    simp only [writes_newLocal, Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not] at hv
    by_cases hvx : v = x
    · subst hvx; simp
    · have hp : v ∉ writes p := fun hw => hvx (hv hw)
      rw [Function.update_of_ne hvx, ih v hp, Function.update_of_ne hvx]
  | @assignAt x e s =>
    intro v hv
    simp only [writes_assignAt, Set.mem_range, not_exists] at hv
    exact Function.update_of_ne (Ne.symm (hv s)) _ _
  | ensure => intro _ _; rfl
  | orLeft _ ih =>
    intro v hv
    simp only [writes_or, Set.mem_union, not_or] at hv
    exact ih v hv.1
  | orRight _ ih =>
    intro v hv
    simp only [writes_or, Set.mem_union, not_or] at hv
    exact ih v hv.2

/-- **The frame of a program**: for a program whose writes lie inside `xs`, the
framed specification and the denotation are the same relation,
`frame xs· denote p = denote p`. -/
theorem frame_denote {p : Prog Var Val} {xs : Set Var} (h : writes p ⊆ xs) :
    Spec.frame xs (denote p) = denote p :=
  Spec.ext fun _ _ =>
    ⟨And.left, fun hd => ⟨hd, fun v hv => unchanged_of_eval (eval_of_denote hd) v fun hw => hv (h hw)⟩⟩

/-- `frame xs· denote p ⇐ p`: a program that writes only inside the frame
implements the framed specification, by a syntactic check on the program. -/
theorem refines_frame_denote {p : Prog Var Val} {xs : Set Var} (h : writes p ⊆ xs) :
    Spec.Refines (Spec.frame xs (denote p)) (denote p) := fun _ _ hd => by
  rw [frame_denote h]; exact hd

/-- The denotation of a local declaration is the book's initializing declaration
of Section 5.0.0 under the frame notation of Section 5.0.1. -/
theorem denote_newLocal_eq (x : Var) (e : Spec.State Var Val → Val) (p : Prog Var Val) :
    denote (.newLocal x e p) =
      Spec.frame {x}ᶜ (Spec.newVarInit e (Spec.inScope x (denote p))) :=
  Spec.newLocal_eq x e (denote p)

/-- What is executed refines the book's declaration: the interpreter chooses the
local's initial value, where `new x: Val· P` leaves it arbitrary. -/
theorem refines_newVar_denote (x : Var) (e : Spec.State Var Val → Val) (p : Prog Var Val) :
    Spec.Refines (Spec.frame {x}ᶜ (Spec.newVar (Spec.inScope x (denote p))))
      (denote (.newLocal x e p)) :=
  Spec.newLocal_refines_newVar x e (denote p)

/-- A local declaration does not leak: after `new x := e· p` the slot `x` holds
what it held before, whatever `p` did to it. -/
theorem eval_newLocal_self {x : Var} {e : Spec.State Var Val → Val} {p : Prog Var Val}
    {s s' : Spec.State Var Val} (h : Eval (.newLocal x e p) s s') : s' x = s x :=
  Spec.newLocal_self x e (denote p) (denote_of_eval h)

/-- Assignment to a fixed name is the special case of assignment to a computed
one: `Prog.assign` is `Prog.assignAt` with a constant name. -/
theorem denote_assignAt_const (x : Var) (e : Spec.State Var Val → Val) :
    denote (.assignAt (fun _ => x) e) = denote (.assign x e) := rfl

/-- **Array element assignment.** An array on a flat state is the family of slots
`arr` it indexes, and `A i:= e` is assignment to the slot the index names — the
book's `A′i=e ∧ (∀j· j⧧i ⇒ A′j = A j) ∧ x′=x ∧ ...` of Section 5.1.0, executed. -/
theorem denote_assignAt_arr {Idx : Type w} {arr : Idx → Var} (harr : Function.Injective arr)
    (idx : Spec.State Var Val → Idx) (e : Spec.State Var Val → Val) :
    denote (.assignAt (fun s => arr (idx s)) e) = Spec.assignArr arr idx e :=
  (Spec.assignArr_eq_assignAt harr idx e).symm

omit [DecidableEq Var] in
/-- An array element assignment writes inside the array: its frame is the family
of slots, so every variable outside the array is unchanged. -/
theorem writes_assignAt_arr {Idx : Type w} (arr : Idx → Var)
    (idx : Spec.State Var Val → Idx) (e : Spec.State Var Val → Val) :
    writes (.assignAt (fun s => arr (idx s)) e) ⊆ Set.range arr := by
  rintro v ⟨s, rfl⟩
  exact ⟨idx s, rfl⟩

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

/-- `new x: int := e· p`, with `e` in the first-order syntax. -/
def declare (x : Vr) (e : Exp) (p : P) : P := .newLocal x e.eval p

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

/-! #### Partial correctness, with no fuel and no termination argument

The same loop developed by an invariant instead: `s = i` is preserved by the
body, and the loop exits only when `i = n`, so every terminating execution ends
with `s = n`. Nothing in this development mentions fuel, and nothing claims the
loop terminates. -/

/-- The body `i:= i+1. s:= s+1` preserves `s = i`. -/
theorem countBody_preserves {u v : St} (h : Eval countBody u v) (hu : u Vr.s = u Vr.i) :
    v Vr.s = v Vr.i := by
  obtain ⟨w, hw, hv⟩ :
      ∃ w, Spec.assign Vr.i (Exp.eval (.add (.var .i) (.lit 1))) u w ∧
        Spec.assign Vr.s (Exp.eval (.add (.var .s) (.lit 1))) w v := denote_of_eval h
  rw [Spec.assign_iff] at hw hv
  have hwi : w Vr.i = u Vr.i + 1 := by simpa [Exp.eval] using hw.1
  have hws : w Vr.s = u Vr.s := hw.2 Vr.s (by decide)
  have hvs : v Vr.s = w Vr.s + 1 := by simpa [Exp.eval] using hv.1
  have hvi : v Vr.i = w Vr.i := hv.2 Vr.i (by decide)
  omega

/-- Partial correctness of the counting loop by the invariant rule: from `s = i`,
every terminating execution ends with `s = n`. -/
theorem count_partial {st st' : St} (h : Eval count st st') (hst : st Vr.s = st Vr.i) :
    st' Vr.s = st' Vr.n := by
  obtain ⟨hinv, hb⟩ :=
    eval_while_invariant (I := fun u => u Vr.s = u Vr.i)
      (fun _ _ hu _ hbody => countBody_preserves hbody hu) h hst
  have hin : st' Vr.i = st' Vr.n := by
    by_contra hne
    rw [(countCond_eval st').mpr hne] at hb
    exact Bool.noConfusion hb
  omega

/-- `while 0 ≤ 0 do ok od` diverges: it has no poststate at all. -/
theorem forever_diverges (st : St) : Diverges (loop (.le (.lit 0) (.lit 0)) .ok) st :=
  diverges_whileDo (fun _ => by simp [Bexp.eval, Exp.eval]) st

/-- So the interpreter fails on it for every fuel, rather than returning a wrong
answer. -/
theorem forever_run_none (f : ℕ) (st : St) :
    run f (loop (.le (.lit 0) (.lit 0)) .ok) st = none :=
  run_eq_none_of_diverges (forever_diverges st) f

/-! #### A local declaration that does not leak

`new i: int := 5· s:= s+i` borrows the slot of `i`, uses it, and puts back what
it found. The frame of the whole declaration is therefore `s` alone: the local's
variable is hidden by its own declaration. -/

/-- `new i: int := 5· s:= s+i`. -/
def withLocal : P := declare .i (.lit 5) (set .s (.add (.var .s) (.var .i)))

-- The interpreter runs it: from `n = 3` the final state has `i = 0` and `s = 5`.
#eval (run 10 withLocal (start 3)).map fun st => (st .i, st .s)

/-- The local is 5 inside the scope and `i` is 0 again outside it, computed by
the interpreter and checked by the kernel. -/
theorem withLocal_run :
    (run 10 withLocal (start 3)).map (fun st => (st .i, st .s)) = some (0, 5) := rfl

/-- From any prestate: `i` is as it was, and `s` has gained the local's value. -/
theorem withLocal_no_leak {st st' : St} (h : Eval withLocal st st') :
    st' Vr.i = st Vr.i ∧ st' Vr.s = st Vr.s + 5 := by
  refine ⟨eval_newLocal_self h, ?_⟩
  obtain ⟨t, hd, ht⟩ :
      ∃ t, Spec.assign Vr.s (Exp.eval (.add (.var .s) (.var .i)))
        (Function.update st Vr.i (5 : ℤ)) t ∧ st' = Function.update t Vr.i (st Vr.i) :=
    denote_of_eval h
  rw [Spec.assign_iff] at hd
  have hts : t Vr.s = st Vr.s + 5 := by
    have h1 := hd.1
    simp only [Exp.eval, Function.update_of_ne (by decide : Vr.s ≠ Vr.i),
      Function.update_self] at h1
    exact h1
  rw [ht, Function.update_of_ne (by decide : Vr.s ≠ Vr.i), hts]

/-- The declaration writes only `s`. -/
theorem writes_withLocal : writes withLocal = {Vr.s} := by
  ext v
  simp only [withLocal, declare, set, writes_newLocal, writes_assign, Set.mem_sdiff,
    Set.mem_singleton_iff]
  exact ⟨And.left, fun h => ⟨h, by rw [h]; decide⟩⟩

/-- So the framed specification of Section 5.0.1 is exactly what it implements:
`frame s· new i := 5· s:= s+i = new i := 5· s:= s+i`. -/
theorem frame_withLocal : Spec.frame {Vr.s} (denote withLocal) = denote withLocal :=
  frame_denote (by rw [writes_withLocal])

/-! #### Backtracking: `s:= 0 or s:= 1. ensure s=1`

The example of Section 5.4.0, in the demonstration syntax: "although an
implementation is given a choice between `x:= 0` and `x:= 1`, it must choose the
right one to satisfy a later binary expression". The searching interpreter finds
the one poststate; the deterministic one, which resolves the choice as a
refinement by taking the left branch, finds none. -/

/-- The condition `s = 1`. -/
def isOne : Bexp := .eq (.var .s) (.lit 1)

/-- The condition says exactly `s = 1`. -/
theorem isOne_eval (st : St) : isOne.eval st = true ↔ st Vr.s = 1 := by
  constructor
  · intro h
    by_contra hne
    simp [isOne, Bexp.eval, Exp.eval, hne] at h
  · intro h
    simp [isOne, Bexp.eval, Exp.eval, h]

/-- `s:= 0 or s:= 1`. -/
def choice : P := .or (set .s (.lit 0)) (set .s (.lit 1))

/-- `s:= 0 or s:= 1. ensure s=1`. -/
def backtrack : P := .seq choice (.ensure isOne.eval)

-- The search finds exactly one poststate, the one with `s = 1`.
#eval (runAll 10 backtrack (start 3)).map fun st => st Vr.s

/-- `s:= 0 or s:= 1. ensure s=1 = s:= 1`, the book's example, by the `ensure`
laws of Section 5.4.0. -/
theorem denote_backtrack : denote backtrack = denote (set .s (.lit 1)) := by
  rw [backtrack, denote_seq, denote_ensure, Spec.seq_ensure]
  refine Spec.ext fun st st' => ⟨?_, ?_⟩
  · rintro ⟨h | h, hb⟩
    · replace h : Spec.assign Vr.s (Exp.eval (.lit 0)) st st' := h
      rw [Spec.assign_iff] at h
      have h0 : st' Vr.s = 0 := by simpa [Exp.eval] using h.1
      have h1 : st' Vr.s = 1 := (isOne_eval st').mp hb
      omega
    · exact h
  · intro h
    refine ⟨Or.inr h, (isOne_eval st').mpr ?_⟩
    replace h : Spec.assign Vr.s (Exp.eval (.lit 1)) st st' := h
    rw [Spec.assign_iff] at h
    simpa [Exp.eval] using h.1

/-- The searching interpreter finds the one poststate the specification allows,
computed by the kernel. -/
theorem runAll_backtrack : (runAll 10 backtrack (start 3)).map (fun st => st Vr.s) = [1] := rfl

/-- The deterministic interpreter cannot backtrack: it takes the left branch,
where the `ensure` fails, and finds nothing. -/
theorem run_backtrack : run 10 backtrack (start 3) = none := rfl

/-- That is not a defect of the fuel: the example is outside the deterministic
fragment, which is exactly why `run` is incomplete for it. -/
theorem not_det_backtrack : ¬ Det backtrack := fun h => h.1

/-- The counting loop, by contrast, is in the deterministic fragment, so the
completeness and determinism theorems apply to it. -/
theorem det_count : Det count := ⟨trivial, trivial⟩

/-- And every execution of the example ends with `s = 1`, from any prestate. -/
theorem eval_backtrack {st st' : St} (h : Eval backtrack st st') :
    st' = Function.update st Vr.s 1 := by
  have hd := denote_of_eval h
  rw [denote_backtrack] at hd
  exact hd

/-- A loop-free program denotes a program in the sense of Section 4.0.3. -/
example : Spec.IsProgram (denote (.seq (set .i (.lit 0)) (set .s (.lit 0)) : P)) :=
  isProgram_denote (.seq (.assign _ _) (.assign _ _))

end Demo

/-! ### Arrays: the book's two examples, executed

Section 5.1.0 shows that the Substitution Law fails for array element
assignment, with two examples. `Arrays.example₁` and `Arrays.example₂` prove
what those programs mean; here the same two programs are *run*. On a flat state
the array `A` is the family of slots `a 0, a 1, ...`, so `A i:= e` is an
assignment whose target name is computed from the prestate — which is exactly
why substituting into the syntax does not work.
-/

namespace ArrayDemo

/-- The state variables: an index `i`, another variable `x`, and the array `A`
as the family of slots `a k`. -/
inductive AVr
  /-- The index variable `i`. -/
  | i
  /-- Another variable `x`. -/
  | x
  /-- The array slot `A k`. -/
  | a (k : ℕ)
  deriving DecidableEq, Repr

/-- States over the array variables, integer-valued. -/
abbrev ASt := Spec.State AVr ℤ

/-- Distinct indices name distinct slots, so the array is an array. -/
theorem a_injective : Function.Injective AVr.a := fun _ _ h => by cases h; rfl

/-- `A i:= e`, with the index and the value expressions of the prestate. -/
def setElem (idx : ASt → ℕ) (e : ASt → ℤ) : Prog AVr ℤ :=
  .assignAt (fun s => AVr.a (idx s)) e

/-- `A i:= e` denotes the book's array element assignment. -/
theorem denote_setElem (idx : ASt → ℕ) (e : ASt → ℤ) :
    denote (setElem idx e) = Spec.assignArr AVr.a idx e :=
  denote_assignAt_arr a_injective idx e

/-- The state in which every variable is zero. -/
def zero : ASt := fun _ => 0

/-! #### `A 2:= 3. i:= 2. A i:= 4. A i = A 2` -/

/-- The three assignments of the book's first example. -/
def ex₁ : Prog AVr ℤ :=
  .seq (setElem (fun _ => 2) fun _ => 3)
    (.seq (.assign AVr.i fun _ => 2) (setElem (fun s => (s AVr.i).toNat) fun _ => 4))

-- After the three assignments `i = 2` and `A 2 = 4`, so `A i = A 2` holds.
#eval (run 10 ex₁ zero).map fun s => (s AVr.i, s (AVr.a 2))

/-- `i = 2` and `A 2 = 4` after the three assignments, so the example's final
test `A i = A 2` holds and the program is just the assignments, as
`Arrays.example₁` says. Checked by the kernel. -/
theorem ex₁_run : (run 10 ex₁ zero).map (fun s => (s AVr.i, s (AVr.a 2))) = some (2, 4) := rfl

/-- What the Substitution Law would have given: after `A 2:= 3` alone `A 2` is 3,
not 4, so the substituted test `4 = A 2` is `⊥` (`Arrays.example₁_naive`). -/
theorem ex₁_naive :
    (run 5 (setElem (fun _ => 2) fun _ => 3) zero).map (fun s => s (AVr.a 2)) = some 3 := rfl

/-! #### `A 2:= 2. A(A 2):= 3. A 2 = 2` -/

/-- The two assignments of the book's second example. -/
def ex₂ : Prog AVr ℤ :=
  .seq (setElem (fun _ => 2) fun _ => 2) (setElem (fun s => (s (AVr.a 2)).toNat) fun _ => 3)

-- `A 2 = 3` afterwards, so the example's final test `A 2 = 2` fails.
#eval (run 10 ex₂ zero).map fun s => s (AVr.a 2)

/-- From *any* prestate, `A 2 = 3` after the two assignments — the second one
writes the slot the first one set. So the example's final test `A 2 = 2` fails
and the program is `⊥`, "because `A 2 = 3` just before the final binary
expression" (`Arrays.example₂`), whereas the Substitution Law would have left
`A 2:= 2`. -/
theorem ex₂_result {s s' : ASt} (h : Eval ex₂ s s') : s' (AVr.a 2) = 3 := by
  obtain ⟨t, ht, hs'⟩ :
      ∃ t, Spec.assignAt (fun _ => AVr.a 2) (fun _ => (2 : ℤ)) s t ∧
        Spec.assignAt (fun u : ASt => AVr.a (u (AVr.a 2)).toNat) (fun _ => (3 : ℤ)) t s' :=
    denote_of_eval h
  subst ht
  rw [hs']
  simp

/-- And the kernel agrees. -/
theorem ex₂_run : (run 10 ex₂ zero).map (fun s => s (AVr.a 2)) = some 3 := rfl

/-! #### The frame of an array program -/

/-- Neither example touches `x`: every slot they write is in the array or is `i`. -/
theorem writes_ex₁ : writes ex₁ ⊆ {v : AVr | v ≠ AVr.x} := by
  rintro v hv
  simp only [ex₁, setElem, writes_seq, writes_assignAt, writes_assign, Set.mem_union,
    Set.mem_range, Set.mem_singleton_iff] at hv
  rcases hv with ⟨s, rfl⟩ | rfl | ⟨s, rfl⟩ <;> simp

/-- So `x` is unchanged by it, by the static frame check alone. -/
theorem frame_ex₁ : Spec.frame {v : AVr | v ≠ AVr.x} (denote ex₁) = denote ex₁ :=
  frame_denote writes_ex₁

end ArrayDemo

end Interpreter

end LaPToP.ProgramTheory
