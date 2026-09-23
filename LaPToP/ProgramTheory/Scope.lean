import LaPToP.ProgramTheory.Programs

/-!
# Scope: variable declaration and variable suspension

This module formalizes Section 5.0.0 (Variable Declaration) and Section 5.0.1
(Variable Suspension) of Eric Hehner's *A Practical Theory of Programming*
(aPToP).

## The model

"We can express a variable declaration together with the specification to
which it applies as a binary expression in the initial and final state:
`new x: T· P = ∃x, x′: T· P`. Specification `P` is an expression in the
initial and final values of all nonlocal (already declared) variables plus the
newly declared local variable. Specification `new x: T· P` is an expression in
the nonlocal variables only."

Inside the scope of `new x: T` the state is the product `σ × T` of the
nonlocal state `σ` and the local variable `x : T`; `Spec.newVar P` is
literally `∃x, x′: T· P`. A nonlocal specification is lifted into the scope by
`liftNonlocal`, which leaves the local variable unchanged (the book's implicit
`x′ = x` for specifications that do not mention `x`); `assignLocal` and
`assignNonlocal` are the two kinds of assignment inside the scope.

"The frame notation is the formal way of saying “and all other variables
(even the ones we cannot say because they are covered by local declarations)
are unchanged”": `frame x, y· P = P ∧ w′=w ∧ z′=z`. On states `State Var Val`,
`Spec.frame xs P` conjoins `P` with `v′ = v` for every variable `v ∉ xs`. The
book's remark that `ok` and `x:= e` "could have been defined formally at the
high level" as `frame· ⊤` and `frame x· x′=e` is proved, as is its example
`s:= ΣL = frame s· new n: nat· s′ = ΣL`.
-/

namespace LaPToP.ProgramTheory

open LaPToP.BasicTheories LaPToP.DataStructures

universe u v w

namespace Spec

/-! ### Variable declaration (aPToP §5.0.0) -/

section Declaration

variable {σ : Type u} {T : Type v}

/-- `new x: T· P = ∃x, x′: T· P`: the specification `P` in the nonlocal state
`σ` together with a local variable `x : T`, with the local variable's initial
and final values existentially quantified. -/
def newVar (P : Spec (σ × T)) : Spec σ := fun s s' => ∃ x x' : T, P (s, x) (s', x')

/-- `new x: T := e· P = ∃x: e· ∃x′: T· P`, an initializing declaration. -/
def newVarInit (e : σ → T) (P : Spec (σ × T)) : Spec σ := fun s s' => ∃ x' : T, P (s, e s) (s', x')

/-- `x:= e` for the local variable `x`, `e` an expression of the whole initial state. -/
def assignLocal (e : σ × T → T) : Spec (σ × T) := fun st st' => st' = (st.1, e st)

/-- A nonlocal specification `Q` inside the scope of a local variable: `Q`
holds of the nonlocal state and the local variable is unchanged. -/
def liftNonlocal (Q : Spec σ) : Spec (σ × T) := fun st st' => Q st.1 st'.1 ∧ st'.2 = st.2

/-- Substitution Law for the local assignment. -/
theorem assignLocal_seq (e : σ × T → T) (P : Spec (σ × T)) :
    seq (assignLocal e) P = fun st st' => P (st.1, e st) st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- "For a variable declaration to be implementable, its type must be
nonempty": `new x: T· P` is implementable when `P` is and `T` is nonempty. -/
theorem implementable_newVar [Nonempty T] {P : Spec (σ × T)} (hP : Implementable P) :
    Implementable (newVar P) := fun s =>
  let ⟨st', h⟩ := hP (s, Classical.arbitrary T)
  ⟨st'.1, Classical.arbitrary T, st'.2, h⟩

/-- With an empty type, no declaration is implementable. -/
theorem not_implementable_newVar [IsEmpty T] [Nonempty σ] (P : Spec (σ × T)) :
    ¬ Implementable (newVar P) := fun h =>
  let ⟨_, x, _, _⟩ := h (Classical.arbitrary σ); IsEmpty.false x

/-- Declaring a variable that a specification does not use changes nothing:
`new x: T· Q = Q` for nonlocal `Q` (and nonempty `T`). -/
theorem newVar_liftNonlocal [Nonempty T] (Q : Spec σ) : newVar (liftNonlocal Q : Spec (σ × T)) = Q :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨_, _, hQ, _⟩ => hQ, fun hQ => ⟨Classical.arbitrary T, Classical.arbitrary T, hQ, rfl⟩⟩

/-- An initializing declaration is a declaration followed by a local
assignment: `new x: T := e· P = new x: T· x:= e. P`. -/
theorem newVarInit_eq [Nonempty T] (e : σ → T) (P : Spec (σ × T)) :
    newVarInit e P = newVar (seq (assignLocal fun st => e st.1) P) := by
  rw [assignLocal_seq]
  exact Spec.ext fun s s' =>
    ⟨fun ⟨x', h⟩ => ⟨Classical.arbitrary T, x', h⟩, fun ⟨_, x', h⟩ => ⟨x', h⟩⟩

/-- Declarations nest: `new x, y: T· P = new x: T· new y: T′· P`. -/
theorem newVar_newVar {T' : Type w} (P : Spec ((σ × T) × T')) :
    newVar (newVar P) = fun s s' => ∃ (x x' : T) (y y' : T'), P ((s, x), y) ((s', x'), y') :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨x, x', y, y', h⟩ => ⟨x, x', y, y', h⟩, fun ⟨x, x', y, y', h⟩ => ⟨x, x', y, y', h⟩⟩

/-- Declaration is monotonic with respect to refinement. -/
theorem newVar_mono {P Q : Spec (σ × T)} (h : Refines P Q) : Refines (newVar P) (newVar Q) :=
  fun _ _ ⟨x, x', hQ⟩ => ⟨x, x', h _ _ hQ⟩

/-- An initializing declaration refines the declaration it initializes:
`new x: T· P ⇐ new x: T := e· P`. "The initial value of the local variable is an
arbitrary value of its type", so fixing it is a refinement. -/
theorem newVar_refines_newVarInit (e : σ → T) (P : Spec (σ × T)) :
    Refines (newVar P) (newVarInit e P) := fun s _ ⟨x', h⟩ => ⟨e s, x', h⟩

/-- An initializing declaration is monotonic with respect to refinement. -/
theorem newVarInit_mono (e : σ → T) {P Q : Spec (σ × T)} (h : Refines P Q) :
    Refines (newVarInit e P) (newVarInit e Q) := fun _ _ ⟨x', hQ⟩ => ⟨x', h _ _ hQ⟩

end Declaration

section DeclarationExamples

variable {Var : Type u} {Val : Type v} {T : Type w} [DecidableEq Var]

/-- `y:= e` for a nonlocal variable `y` inside the scope of a local variable,
`e` an expression of the whole initial state. -/
def assignNonlocal (y : Var) (e : State Var Val × T → Val) : Spec (State Var Val × T) :=
  fun st st' => st' = (Function.update st.1 y (e st), st.2)

/-- Substitution Law for the nonlocal assignment. -/
theorem assignNonlocal_seq (y : Var) (e : State Var Val × T → Val) (P : Spec (State Var Val × T)) :
    seq (assignNonlocal y e) P = fun st st' => P (Function.update st.1 y (e st), st.2) st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

end DeclarationExamples

/-! ### Variable suspension (aPToP §5.0.1) -/

section Frame

variable {Var : Type u} {Val : Type v}

/-- `frame x, y· P = P ∧ w′=w ∧ z′=z`: `P` holds, and every state variable not
in the frame is unchanged. -/
def frame (xs : Set Var) (P : Spec (State Var Val)) : Spec (State Var Val) :=
  fun s s' => P s s' ∧ ∀ v, v ∉ xs → s' v = s v

variable (xs ys : Set Var) (P Q : Spec (State Var Val))

/-- `ok = frame· ⊤`: the empty frame of the trivial specification. -/
theorem frame_empty_top : frame (∅ : Set Var) (top : Spec (State Var Val)) = ok :=
  Spec.ext fun _s _s' =>
    ⟨fun ⟨_, h⟩ => funext fun v => h v (Set.notMem_empty v), fun h => ⟨trivial, fun _v _ => h ▸ rfl⟩⟩

/-- `frame (all variables)· P = P`. -/
theorem frame_univ : frame Set.univ P = P :=
  Spec.ext fun _ _ => ⟨And.left, fun h => ⟨h, fun v hv => absurd (Set.mem_univ v) hv⟩⟩

/-- `frame xs· ok = ok`. -/
theorem frame_ok : frame xs (ok : Spec (State Var Val)) = ok :=
  Spec.ext fun _ _ => ⟨And.left, fun h => ⟨h, fun _ _ => h ▸ rfl⟩⟩

/-- Nested frames intersect: `frame xs· frame ys· P = frame (xs ‘ ys)· P`. -/
theorem frame_frame : frame xs (frame ys P) = frame (xs ∩ ys) P :=
  Spec.ext fun s s' => by
    simp only [frame, Set.mem_inter_iff, not_and_or]
    constructor
    · rintro ⟨⟨hP, hy⟩, hx⟩
      exact ⟨hP, fun v hv => hv.elim (hx v) (hy v)⟩
    · rintro ⟨hP, h⟩
      exact ⟨⟨hP, fun v hv => h v (Or.inr hv)⟩, fun v hv => h v (Or.inl hv)⟩

/-- A frame strengthens: `P ⇐ frame xs· P`. -/
theorem refines_frame : Refines P (frame xs P) := fun _ _ h => h.1

/-- Frames are monotonic with respect to refinement. -/
theorem frame_mono (h : Refines P Q) : Refines (frame xs P) (frame xs Q) :=
  fun s s' ⟨hQ, hv⟩ => ⟨h s s' hQ, hv⟩

/-- A frame distributes over `if`. -/
theorem frame_cond (b : State Var Val → Prop) : frame xs (cond b P Q) = cond b (frame xs P) (frame xs Q) :=
  Spec.ext fun _ _ => by simp only [frame, cond]; tauto

/-- A sequence of framed specifications is a framed sequence:
`frame xs· (P. Q) ⇐ (frame xs· P). (frame xs· Q)`. -/
theorem frame_seq : Refines (frame xs (seq P Q)) (seq (frame xs P) (frame xs Q)) :=
  fun _s _s' ⟨t, ⟨hP, hv⟩, hQ, hv'⟩ => ⟨⟨t, hP, hQ⟩, fun v hv'' => (hv' v hv'').trans (hv v hv'')⟩

variable [DecidableEq Var]

/-- `x:= e = frame x· x′=e`. -/
theorem frame_singleton_eq (x : Var) (e : State Var Val → Val) :
    frame {x} (fun s s' => s' x = e s) = assign x e :=
  Spec.ext fun s s' => by
    rw [assign_iff]
    exact ⟨fun ⟨hx, h⟩ => ⟨hx, fun v hv => h v hv⟩, fun ⟨hx, h⟩ => ⟨hx, fun v hv => h v hv⟩⟩

/-- Assignment to a framed variable is unaffected: `frame xs· x:= e = x:= e` for `x` in `xs`. -/
theorem frame_assign (x : Var) (hx : x ∈ xs) (e : State Var Val → Val) : frame xs (assign x e) = assign x e :=
  Spec.ext fun s s' => by
    constructor
    · exact And.left
    · intro h
      refine ⟨h, fun v hv => ?_⟩
      rw [assign_iff] at h
      exact h.2 v (fun hvx => hv (hvx ▸ hx))

end Frame

/-! ### Declaration on a homogeneous state (aPToP §5.0.0 with §5.0.1)

Section 5.0.0 puts the local variable *beside* the nonlocal state: inside
`new x: T· P` the state is the pair `σ × T`. A machine with one flat state
`State Var Val` has no room beside it, and declares a local by taking a state
slot, using it, and putting back what was there. `newLocal` is that operation,
and it is exactly the book's initializing declaration under the frame notation
of Section 5.0.1 (`newLocal_eq`): nothing new is defined here, the two notations
are combined.
-/

section Local

variable {Var : Type u} {Val : Type v} [DecidableEq Var]

/-- A specification read inside the scope of a local variable held in the state
slot `x`: the pair `(s, a)` is the state `s` with `x` holding `a`. -/
def inScope (x : Var) (P : Spec (State Var Val)) : Spec (State Var Val × Val) :=
  fun st st' => P (Function.update st.1 x st.2) (Function.update st'.1 x st'.2)

/-- `new x: Val := e· P` on a flat state: the slot named `x` holds the local
variable, initialized to `e`, and holds its earlier value again when the scope
ends — so the declaration does not leak. -/
def newLocal (x : Var) (e : State Var Val → Val) (P : Spec (State Var Val)) :
    Spec (State Var Val) :=
  fun s s' => ∃ t, P (Function.update s x (e s)) t ∧ s' = Function.update t x (s x)

/-- A local declaration leaves the slot it borrowed as it found it. -/
theorem newLocal_self (x : Var) (e : State Var Val → Val) (P : Spec (State Var Val))
    {s s' : State Var Val} (h : newLocal x e P s s') : s' x = s x := by
  obtain ⟨t, -, rfl⟩ := h
  simp

/-- `new x := e· P = frame x̄· new x: Val := e· P`: the flat-state declaration is
the book's initializing declaration of Section 5.0.0, framed by Section 5.0.1 so
that the borrowed slot is restored. -/
theorem newLocal_eq (x : Var) (e : State Var Val → Val) (P : Spec (State Var Val)) :
    newLocal x e P = frame {x}ᶜ (newVarInit e (inScope x P)) := by
  refine Spec.ext fun s s' => ⟨?_, ?_⟩
  · rintro ⟨t, hP, rfl⟩
    refine ⟨⟨t x, ?_⟩, fun v hv => ?_⟩
    · simp only [inScope, Function.update_idem, Function.update_eq_self]
      exact hP
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at hv
      subst hv
      simp
  · rintro ⟨⟨x', hP⟩, hv⟩
    have hx : s' x = s x := hv x (by simp)
    refine ⟨Function.update s' x x', hP, ?_⟩
    rw [Function.update_idem, ← hx, Function.update_eq_self]

/-- The declaration on a flat state is monotonic with respect to refinement. -/
theorem newLocal_mono (x : Var) (e : State Var Val → Val) {P Q : Spec (State Var Val)}
    (h : Refines P Q) : Refines (newLocal x e P) (newLocal x e Q) :=
  fun _ _ ⟨t, hQ, ht⟩ => ⟨t, h _ _ hQ, ht⟩

/-- The flat-state declaration refines the book's uninitialized declaration,
framed: `frame x̄· new x: Val· P ⇐ new x: Val := e· P`. Choosing the initial value
of the local is a refinement, which is what makes the declaration executable. -/
theorem newLocal_refines_newVar (x : Var) (e : State Var Val → Val)
    (P : Spec (State Var Val)) :
    Refines (frame {x}ᶜ (newVar (inScope x P))) (newLocal x e P) := by
  rw [newLocal_eq]
  exact frame_mono _ _ _ (newVar_refines_newVarInit e (inScope x P))

end Local

end Spec

/-! ### The book's examples (aPToP §5.0.0–5.0.1) -/

namespace ScopeExamples

open Spec

/-- The nonlocal integer variables `y` and `z`. -/
inductive YZ
  /-- The variable `y`. -/
  | y
  /-- The variable `z`. -/
  | z
  deriving DecidableEq

/-- Nonlocal states. -/
abbrev St := State YZ ℤ

/-- `new x: int· x:= 2. y:= x+z = y′ = 2+z ∧ z′=z`. -/
theorem example₁ :
    newVar (seq (assignLocal fun _ => (2 : ℤ)) (assignNonlocal YZ.y fun st => st.2 + st.1 YZ.z)) =
      fun s s' : St => s' YZ.y = 2 + s YZ.z ∧ s' YZ.z = s YZ.z := by
  rw [assignLocal_seq]
  refine Spec.ext fun s s' => ⟨?_, ?_⟩
  · rintro ⟨x, x', h⟩
    simp only [assignNonlocal, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  · rintro ⟨hy, hz⟩
    refine ⟨0, 2, ?_⟩
    simp only [assignNonlocal, Prod.mk.injEq]
    refine ⟨funext fun v => ?_, trivial⟩
    cases v
    · simp [hy]
    · simp [hz]

/-- `new x: int· y:= x = z′=z`: "the initial value of the local variable is an
arbitrary value of its type", so nothing is known about `y′`. -/
theorem example₂ :
    newVar (assignNonlocal YZ.y fun st : St × ℤ => st.2) = fun s s' : St => s' YZ.z = s YZ.z := by
  refine Spec.ext fun s s' => ⟨?_, ?_⟩
  · rintro ⟨x, x', h⟩
    simp only [assignNonlocal, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  · intro hz
    refine ⟨s' YZ.y, s' YZ.y, ?_⟩
    simp only [assignNonlocal, Prod.mk.injEq]
    refine ⟨funext fun v => ?_, trivial⟩
    cases v
    · simp
    · simp [hz]

/-- `new x: int· y:= x–x = y′=0 ∧ z′=z`. -/
theorem example₃ :
    newVar (assignNonlocal YZ.y fun st : St × ℤ => st.2 - st.2) =
      fun s s' : St => s' YZ.y = 0 ∧ s' YZ.z = s YZ.z := by
  refine Spec.ext fun s s' => ⟨?_, ?_⟩
  · rintro ⟨x, x', h⟩
    simp only [assignNonlocal, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  · rintro ⟨hy, hz⟩
    refine ⟨0, 0, ?_⟩
    simp only [assignNonlocal, Prod.mk.injEq]
    refine ⟨funext fun v => ?_, trivial⟩
    cases v
    · simp [hy]
    · simp [hz]

open ListSummation in
/-- `s:= ΣL = frame s· new n: nat· s′ = ΣL`: "first we reduce the state space to
`s`; ... next we introduce local variable `n`", on the state variables `s`, `n`
of the list summation. -/
theorem assign_sum_eq_frame_newVar (L : HList ℤ) :
    assign SV.s (fun _ => L.contents.sum) =
      frame {SV.s} (newVar fun _ st' : ListSummation.St × ℕ => st'.1 SV.s = L.contents.sum) := by
  refine Spec.ext fun st st' => ?_
  rw [assign_iff]
  constructor
  · rintro ⟨hs, h⟩
    exact ⟨⟨0, 0, hs⟩, fun v hv => h v hv⟩
  · rintro ⟨⟨_, _, hs⟩, h⟩
    exact ⟨hs, fun v hv => h v hv⟩

end ScopeExamples

end LaPToP.ProgramTheory
