import LaPToP.Concurrency.Composition
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Interactive variables

This module formalizes Section 9.0 (Interactive Variables) of Eric Hehner's
*A Practical Theory of Programming* (aPToP).

"Let the notation `new x: time→T· S` declare `x` to be an interactive variable
of type `T` and scope `S`. It is defined as follows. `new x: time→T· S = ∃x:
time→T· S` where `time` is the domain of time, either the extended naturals or
the nonnegative extended reals. An interactive variable is a function of time.
The value of variable `x` at time `t` is `x t`. ... Suppose `a` and `b` are
boundary variables, `x` and `y` are interactive variables, and `t` is time.
The definition of `ok` says that the boundary variables and time are
unchanged. `ok = a′=a ∧ b′=b ∧ t′=t`. ... `a:= e = a′=e ∧ b′=b ∧ t′=t`.
Assignment to an interactive variable cannot be instantaneous because it is
time that distinguishes its values. `x:= e = a′=a ∧ b′=b ∧ x′=e ∧ (∀t″· t≤t″≤t′
⇒ y″=y) ∧ t′ = t+(the time required to evaluate and store e)`. ... Sequential
composition hides the intermediate values of the boundary and time variables,
leaving the intermediate values of the interactive variables visible. ...
`P. Q = ∃a″, b″, t″· ⟨a′, b′, t′· P⟩ a″ b″ t″ ∧ ⟨a, b, t· Q⟩ a″ b″ t″`. For
concurrent composition we partition all the variables, both boundary and
interactive (but not time). Suppose `a` and `x` belong to `P`, and `b` and `y`
belong to `Q`. `P||Q = ∃tP, tQ· ⟨t′· P⟩ tP ∧ (∀t″· tP≤t″≤t′ ⇒ x″ = x(tP)) ∧ ⟨t′· Q⟩ tQ
∧ (∀t″· tQ≤t″≤t′ ⇒ y″ = y(tQ)) ∧ t′ = tP↑tQ`. ... Most of the specification laws
and refinement laws survive the addition of interactive variables, but sadly,
the Substitution Law no longer works."

## The model

Time is `ℕ∞` (the book also allows the nonnegative extended reals). The
boundary variables `a`, `b` and the time `t` form the before/after state `BT`;
an interactive variable is a function `ℕ∞ → ℤ`, and a specification in the
interactive variables `x`, `y` is a function of them: `ISpec := IVar → IVar →
Spec BT`. Thus `x′` is `x t′`, unprimed `x` is `x t`, and the intermediate
values of `x` remain visible through sequential composition, exactly as the
book describes. `new x: time→T· S = ∃x· S` is `newX`. The time an assignment
takes is a parameter `d`.

Following the book's Exercise 496, where "x is a variable in the left process
and y is a variable in the right process" and each process's assignments are
expanded in its own variables only, the assignments come in two forms: the
general one in all four variables (`assignX`, with "`y` remains unchanged
throughout the duration"), and the process-local ones `assignXP` (process `P`,
variables `a`, `x`) and `assignYQ` (process `Q`, variables `b`, `y`), which say
nothing about the other process's variables. In `par P Q` the process `P` is
evaluated with `Q`'s boundary variable `b` at its initial value ("its value,
as seen in `P`, is its initial value, regardless of whether `Q` has assigned to
it").

The Substitution Law is shown to fail by a counterexample: substituting the
constant `2` for the interactive variable `x` in `ok` gives `ok`, but
`x:= 2. ok` is not `ok` — the assignment takes time. Exercise 496 is proved as
the book states it, for a finite initial time.
-/

namespace LaPToP.Interaction

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

/-- The boundary variables `a`, `b` and the time `t`. -/
structure BT where
  /-- The time. -/
  t : ℕ∞
  /-- The boundary variable `a`. -/
  a : ℤ
  /-- The boundary variable `b`. -/
  b : ℤ

/-- An interactive variable: "a function of time". -/
abbrev IVar := ℕ∞ → ℤ

/-- A specification in the boundary variables `a`, `b`, the time `t`, and the
interactive variables `x`, `y`. -/
abbrev ISpec := IVar → IVar → Spec BT

namespace ISpec

theorem ext {P Q : ISpec} (h : ∀ x y s s', P x y s s' ↔ Q x y s s') : P = Q :=
  funext fun x => funext fun y => Spec.ext (h x y)

/-- `new x: time→T· S = ∃x: time→T· S`. -/
def newX (S : ISpec) : IVar → Spec BT := fun y s s' => ∃ x, S x y s s'

/-- `ok = a′=a ∧ b′=b ∧ t′=t`. -/
def ok : ISpec := fun _ _ s s' => s' = s

/-- `a:= e = a′=e ∧ b′=b ∧ t′=t`, instantaneous. -/
def assignA (e : BT → IVar → IVar → ℤ) : ISpec := fun x y s s' => s' = { s with a := e s x y }

/-- `x:= e = a′=a ∧ b′=b ∧ x′=e ∧ (∀t″· t≤t″≤t′ ⇒ y″=y) ∧ t′ = t+d`, where `d` is "the
time required to evaluate and store `e`"; `e` is evaluated in the initial state. -/
def assignX (e : BT → IVar → IVar → ℤ) (d : ℕ∞) : ISpec := fun x y s s' =>
  s'.a = s.a ∧ s'.b = s.b ∧ s'.t = s.t + d ∧ x s'.t = e s x y ∧ ∀ t'', s.t ≤ t'' → t'' ≤ s'.t → y t'' = y s.t

/-- `x:= e` in the process `P` owning `a` and `x`: `a′=a ∧ x′=e ∧ t′=t+d`. -/
def assignXP (e : BT → IVar → IVar → ℤ) (d : ℕ∞) : ISpec := fun x y s s' =>
  s'.a = s.a ∧ s'.t = s.t + d ∧ x s'.t = e s x y

/-- `y:= e` in the process `Q` owning `b` and `y`: `b′=b ∧ y′=e ∧ t′=t+d`. -/
def assignYQ (e : BT → IVar → IVar → ℤ) (d : ℕ∞) : ISpec := fun x y s s' =>
  s'.b = s.b ∧ s'.t = s.t + d ∧ y s'.t = e s x y

/-- `P. Q = ∃a″, b″, t″· ⟨a′, b′, t′· P⟩ a″ b″ t″ ∧ ⟨a, b, t· Q⟩ a″ b″ t″`: the interactive
variables are shared, their intermediate values visible. -/
def seq (P Q : ISpec) : ISpec := fun x y s s' => ∃ s'', P x y s s'' ∧ Q x y s'' s'

/-- `P||Q` with `a`, `x` belonging to `P` and `b`, `y` to `Q`:
`∃tP, tQ· ⟨t′· P⟩ tP ∧ (∀t″· tP≤t″≤t′ ⇒ x″ = x(tP)) ∧ ⟨t′· Q⟩ tQ ∧ (∀t″· tQ≤t″≤t′ ⇒ y″ = y(tQ)) ∧ t′ = tP↑tQ`.
`P` sees `b` at its initial value and `Q` sees `a` at its initial value. -/
def par (P Q : ISpec) : ISpec := fun x y s s' =>
  ∃ tP tQ : ℕ∞,
    P x y s ⟨tP, s'.a, s.b⟩ ∧ (∀ t'', tP ≤ t'' → t'' ≤ s'.t → x t'' = x tP) ∧
    Q x y s ⟨tQ, s.a, s'.b⟩ ∧ (∀ t'', tQ ≤ t'' → t'' ≤ s'.t → y t'' = y tQ) ∧
    s'.t = max tP tQ

/-! ### Laws that survive -/

theorem ok_seq (P : ISpec) : seq ok P = P :=
  ext fun _ _ s _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨s, rfl, hP⟩⟩

theorem seq_ok (P : ISpec) : seq P ok = P :=
  ext fun _ _ _ s' => ⟨fun ⟨_, hP, h⟩ => h ▸ hP, fun hP => ⟨s', hP, rfl⟩⟩

theorem seq_assoc (P Q R : ISpec) : seq P (seq Q R) = seq (seq P Q) R :=
  ext fun _ _ _ _ =>
    ⟨fun ⟨u, hP, v, hQ, hR⟩ => ⟨v, ⟨u, hP, hQ⟩, hR⟩, fun ⟨v, ⟨u, hP, hQ⟩, hR⟩ => ⟨u, hP, v, hQ, hR⟩⟩

/-- The Substitution Law for the boundary variable `a` still holds. -/
theorem assignA_seq (e : BT → IVar → IVar → ℤ) (P : ISpec) :
    seq (assignA e) P = fun x y s s' => P x y { s with a := e s x y } s' :=
  ext fun _ _ _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-! ### "Sadly, the Substitution Law no longer works" -/

/-- "Substitute `e` for `x` in `P`": `P` with the interactive variable `x` replaced
by the constant function with value `e` (evaluated in the initial state). -/
def substX (e : BT → IVar → IVar → ℤ) (P : ISpec) : ISpec := fun x y s s' => P (fun _ => e s x y) y s s'

/-- The Substitution Law `x:= e. P = (substitute e for x in P)` fails for interactive
variables: with `P = ok`, the right side is `ok` but the left side takes time. -/
theorem not_substitution_law : seq (assignX (fun _ _ _ => 2) 1) ok ≠ substX (fun _ _ _ => 2) ok := by
  intro h
  have := congrFun (congrFun (congrFun (congrFun h fun _ => 0) fun _ => 0) ⟨0, 0, 0⟩) ⟨0, 0, 0⟩
  simp only [seq, assignX, ok, substX, eq_iff_iff, iff_true] at this
  obtain ⟨_, ⟨-, -, ht, -, -⟩, rfl⟩ := this
  simp at ht

/-! ### Exercise 496 -/

/-- The left process `x:= 2. x:= x+y. x:= x+y`, each assignment taking time `1`. -/
def leftP : ISpec :=
  seq (assignXP (fun _ _ _ => 2) 1)
    (seq (assignXP (fun s x y => x s.t + y s.t) 1) (assignXP (fun s x y => x s.t + y s.t) 1))

/-- The right process `y:= 3. y:= x+y`. -/
def rightQ : ISpec := seq (assignYQ (fun _ _ _ => 3) 1) (assignYQ (fun s x y => x s.t + y s.t) 1)

/-- `(x:= 2. x:= x+y. x:= x+y) || (y:= 3. y:= x+y) = a′=a ∧ x(t+1)=2 ∧ x(t+2)=5 ∧ x(t+3)=10
∧ b′=b ∧ y(t+1)=3 ∧ y(t+2)=y(t+3)=5 ∧ t′=t+3`, for a finite initial time `t`. -/
theorem exercise_496 (x y : IVar) (t : ℕ) (a b : ℤ) (s' : BT) :
    par leftP rightQ x y ⟨t, a, b⟩ s' ↔
      s'.a = a ∧ x (t + 1) = 2 ∧ x (t + 2) = 5 ∧ x (t + 3) = 10 ∧
        s'.b = b ∧ y (t + 1) = 3 ∧ y (t + 2) = 5 ∧ y (t + 3) = 5 ∧ s'.t = t + 3 := by
  have h12 : ((t : ℕ∞) + 1) + 1 = t + 2 := by norm_cast
  have h23 : ((t : ℕ∞) + 2) + 1 = t + 3 := by norm_cast
  have h32 : max ((t : ℕ∞) + 3) (t + 2) = t + 3 := max_eq_left (by norm_cast; omega)
  constructor
  · rintro ⟨tP, tQ, ⟨s₁, ⟨ha₁, ht₁, hx₁⟩, s₂, ⟨ha₂, ht₂, hx₂⟩, ha₃, ht₃, hx₃⟩, -,
      ⟨u₁, ⟨hb₁, hu₁, hy₁⟩, hb₂, hu₂, hy₂⟩, hy, ht'⟩
    simp only at ha₁ ht₁ hx₁ ha₂ ht₂ hx₂ ha₃ ht₃ hx₃ hb₁ hu₁ hy₁ hb₂ hu₂ hy₂ hy ht'
    rw [ht₁] at hx₁ ht₂ hx₂
    rw [ht₂, h12] at hx₂ ht₃ hx₃
    rw [ht₃, h23] at hx₃ ht'
    rw [hu₁] at hy₁ hu₂ hy₂
    rw [hu₂, h12] at hy₂ ht' hy
    rw [h32] at ht'
    have hy3 : y (t + 3) = y (t + 2) := hy _ (by norm_cast; omega) (le_of_eq ht'.symm)
    refine ⟨ha₃.trans (ha₂.trans ha₁), hx₁, ?_, ?_, hb₂.trans hb₁, hy₁, ?_, ?_, ht'⟩
    · rw [hx₂, hx₁, hy₁]; norm_num
    · rw [hx₃, hx₂, hy₂, hx₁, hy₁]; norm_num
    · rw [hy₂, hx₁, hy₁]; norm_num
    · rw [hy3, hy₂, hx₁, hy₁]; norm_num
  · rintro ⟨ha, hx₁, hx₂, hx₃, hb, hy₁, hy₂, hy₃, ht'⟩
    refine ⟨t + 3, t + 2, ⟨⟨t + 1, a, b⟩, ⟨rfl, rfl, hx₁⟩, ⟨t + 2, a, b⟩, ⟨rfl, h12.symm, ?_⟩, ha, h23.symm, ?_⟩,
      fun t'' h1 h2 => ?_, ⟨⟨t + 1, a, b⟩, ⟨rfl, rfl, hy₁⟩, hb, h12.symm, ?_⟩, fun t'' h1 h2 => ?_, ht'.trans h32.symm⟩
    · simp only; rw [hx₂, hx₁, hy₁]; norm_num
    · simp only; rw [hx₃, hx₂, hy₂]; norm_num
    · rw [ht'] at h2
      rw [le_antisymm h2 h1]
    · simp only; rw [hy₂, hx₁, hy₁]; norm_num
    · rw [ht'] at h2
      rcases eq_or_lt_of_le h1 with rfl | hlt
      · rfl
      · have h3 : (t : ℕ∞) + 3 ≤ t'' := h23 ▸ Order.add_one_le_of_lt hlt
        rw [le_antisymm h2 h3, hy₃, hy₂]

end ISpec

end LaPToP.Interaction
