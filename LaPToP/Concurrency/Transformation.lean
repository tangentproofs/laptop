import LaPToP.Concurrency.Composition
import LaPToP.RecursiveDefinition.Nat

/-!
# Sequential to concurrent transformation

This module formalizes Section 8.1 (Sequential to Concurrent Transformation)
and Section 8.1.0 (Buffer) of Eric Hehner's *A Practical Theory of
Programming* (aPToP).

"The goal of this section is to transform programs without concurrency into
programs with concurrency. ... Whenever two programs occur in sequence, and
neither assigns to any variable assigned in the other, and no variable
assigned in the first appears in the second, they can be placed in parallel;
a copy must be made of the initial value of any variable appearing in the
first and assigned in the second. Whenever two programs occur in sequence,
and neither assigns to any variable appearing in the other, they can be
placed in parallel without any copying of initial values. This transformation
does not change the result of a computation, but it may decrease the time."

## The model

As in `LaPToP.Concurrency.Composition`, the partition of the variables is a
product `σ₁ × σ₂`. A sequential program that "does not assign to" the
variables `σ₂` is a process on `σ₁` lifted to the product with `σ₂` unchanged
(`liftL`); one that "does not mention" `σ₂` at all is `liftL P`, while one that
reads `σ₂` (as constants) is `liftLWith P` with `P : σ₂ → Spec σ₁`. The two
sentences of the book become equalities of specifications:

* `seq (liftL P) (liftR Q) = par P Q` — no copying of initial values;
* `seq (liftRWith Q) (liftL P) = parWith (fun _ => P) Q` — the first program `Q`
  reads `σ₁`, the second `P` assigns `σ₁`; "a copy must be made of the initial
  value": the copy is exactly the initial-state parameter of `parWith`.

Deviation from the book: the variables are partitioned as product components,
not named variables of a `State Var Val`; "assigns to" and "appears in" are
expressed by the shape of the lifting rather than by syntactic inspection.
The time remark is not formalized here (the transformed programs are equal
as untimed specifications; timing is Section 8.0's `parT`).

The buffer of Section 8.1.0 is a producer `b:= e` and a consumer `x:= b`
executed alternately forever: `control = produce. consume. control`. The
unrolled body `consume. produce` is `consume || produce` with the consumer
reading the initial value of `b` (the copy law), and at source level it is
`c:= b. (consume || produce)` with `consume` now reading `c`. `control` is a
recursively defined specification (Section 6.1), so we state the unrolling
`control = produce. newcontrol`, `newcontrol = consume. produce. newcontrol`
as fixed-point equations. The infinite and cyclic buffers with `w`, `r` are
"not expressible as a source program without additional interactive
constructs (Chapter 9)" and are left informal.
-/

namespace LaPToP.Concurrency

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec LaPToP.RecursiveDefinition

universe u v

variable {σ₁ : Type u} {σ₂ : Type v}

/-! ### Lifting a process to the product state -/

/-- A program on the variables `σ₁` that leaves `σ₂` unchanged. -/
def liftL (P : Spec σ₁) : Spec (σ₁ × σ₂) := fun s s' => P s.1 s'.1 ∧ s'.2 = s.2

/-- A program on the variables `σ₂` that leaves `σ₁` unchanged. -/
def liftR (Q : Spec σ₂) : Spec (σ₁ × σ₂) := fun s s' => Q s.2 s'.2 ∧ s'.1 = s.1

/-- A program assigning only `σ₁` that also reads (the initial values of) `σ₂`. -/
def liftLWith (P : σ₂ → Spec σ₁) : Spec (σ₁ × σ₂) := fun s s' => P s.2 s.1 s'.1 ∧ s'.2 = s.2

/-- A program assigning only `σ₂` that also reads (the initial values of) `σ₁`. -/
def liftRWith (Q : σ₁ → Spec σ₂) : Spec (σ₁ × σ₂) := fun s s' => Q s.1 s.2 s'.2 ∧ s'.1 = s.1

theorem liftL_eq_liftLWith (P : Spec σ₁) : (liftL P : Spec (σ₁ × σ₂)) = liftLWith fun _ => P := rfl

theorem liftR_eq_liftRWith (Q : Spec σ₂) : (liftR Q : Spec (σ₁ × σ₂)) = liftRWith fun _ => Q := rfl

/-! ### The transformation laws (aPToP §8.1) -/

section Laws

variable (P P' : Spec σ₁) (Q : Spec σ₂)

/-- "Whenever two programs occur in sequence, and neither assigns to any
variable appearing in the other, they can be placed in parallel without any
copying of initial values." -/
theorem seq_liftL_liftR : seq (liftL P) (liftR Q) = par P Q :=
  Spec.ext fun s s' =>
    ⟨fun ⟨_u, ⟨hP, hu2⟩, hQ, hu1⟩ => ⟨hu1 ▸ hP, hu2 ▸ hQ⟩,
     fun ⟨hP, hQ⟩ => ⟨(s'.1, s.2), ⟨hP, rfl⟩, hQ, rfl⟩⟩

/-- The same law with the processes in the other order: `P||Q` is also `Q. P`. -/
theorem seq_liftR_liftL : seq (liftR Q) (liftL P) = par P Q :=
  Spec.ext fun s s' =>
    ⟨fun ⟨_u, ⟨hQ, hu1⟩, hP, hu2⟩ => ⟨hu1 ▸ hP, hu2 ▸ hQ⟩,
     fun ⟨hP, hQ⟩ => ⟨(s.1, s'.2), ⟨hQ, rfl⟩, hP, rfl⟩⟩

/-- "Whenever two programs occur in sequence, and neither assigns to any
variable assigned in the other, and no variable assigned in the first appears
in the second, they can be placed in parallel; a copy must be made of the
initial value of any variable appearing in the first and assigned in the
second." The first program `Q` reads `σ₁` and assigns `σ₂`; the second `P`
assigns `σ₁`. The copy is the initial-value parameter of `parWith`. -/
theorem seq_liftRWith_liftL (Q : σ₁ → Spec σ₂) :
    seq (liftRWith Q) (liftL P) = parWith (fun _ => P) Q :=
  Spec.ext fun s s' =>
    ⟨fun ⟨_u, ⟨hQ, hu1⟩, hP, hu2⟩ => ⟨hu1 ▸ hP, hu2 ▸ hQ⟩,
     fun ⟨hP, hQ⟩ => ⟨(s.1, s'.2), ⟨hQ, rfl⟩, hP, rfl⟩⟩

/-- The mirror image: the first program reads `σ₂` and assigns `σ₁`. -/
theorem seq_liftLWith_liftR (P : σ₂ → Spec σ₁) :
    seq (liftLWith P) (liftR Q) = parWith P fun _ => Q :=
  Spec.ext fun s s' =>
    ⟨fun ⟨_u, ⟨hP, hu2⟩, hQ, hu1⟩ => ⟨hu1 ▸ hP, hu2 ▸ hQ⟩,
     fun ⟨hP, hQ⟩ => ⟨(s'.1, s.2), ⟨hP, rfl⟩, hQ, rfl⟩⟩

/-- Absorbing a preceding program into the left process: "Now we have the
first and last assignments next to each other, in sequence; they too can be
executed concurrently." -/
theorem seq_liftLWith_par (P : σ₂ → Spec σ₁) :
    seq (liftLWith P) (par P' Q) = parWith (fun s₂ => seq (P s₂) P') fun _ => Q :=
  Spec.ext fun s _s' =>
    ⟨fun ⟨u, ⟨hP, hu2⟩, hP', hQ⟩ => ⟨⟨u.1, hP, hP'⟩, hu2 ▸ hQ⟩,
     fun ⟨⟨v, hP, hP'⟩, hQ⟩ => ⟨(v, s.2), ⟨hP, rfl⟩, hP', hQ⟩⟩

/-- The mirror image, absorbing into the right process. -/
theorem seq_liftRWith_par (Q : σ₁ → Spec σ₂) (Q' : Spec σ₂) :
    seq (liftRWith Q) (par P Q') = parWith (fun _ => P) fun s₁ => seq (Q s₁) Q' :=
  Spec.ext fun s _s' =>
    ⟨fun ⟨u, ⟨hQ, hu1⟩, hP, hQ'⟩ => ⟨hu1 ▸ hP, ⟨u.2, hQ, hQ'⟩⟩,
     fun ⟨hP, ⟨v, hQ, hQ'⟩⟩ => ⟨(s.1, v), ⟨hQ, rfl⟩, hP, hQ'⟩⟩

end Laws

/-! ### The book's example (aPToP §8.1)

Integer variables `x`, `y`, `z`; the left process owns `x`, the right owns
`y` and `z` (`y` is read by both and assigned by neither). -/

namespace Examples

/-- `x:= y`. -/
def xy : Spec (ℤ × (ℤ × ℤ)) := liftLWith fun yz => assignF fun _ => yz.1

/-- `x:= x+1`. -/
def xinc : Spec (ℤ × (ℤ × ℤ)) := liftL (assignF fun x => x + 1)

/-- `z:= y`. -/
def zy : Spec (ℤ × (ℤ × ℤ)) := liftR (assignF fun yz => (yz.1, yz.1))

/-- `x:= y. x:= x+1. z:= y = x:= y. (x:= x+1 || z:= y)`: "The first two
assignments cannot be executed concurrently, but the last two can". -/
theorem step₁ : seq xy (seq xinc zy) =
    seq xy (par (assignF fun x : ℤ => x + 1) (assignF fun yz : ℤ × ℤ => (yz.1, yz.1))) := by
  rw [xinc, zy, seq_liftL_liftR]

/-- `x:= y. (x:= x+1 || z:= y) = (x:= y. x:= x+1) || z:= y`: "Now we have the
first and last assignments next to each other, in sequence; they too can be
executed concurrently." -/
theorem step₂ : seq xy (par (assignF fun x : ℤ => x + 1) (assignF fun yz : ℤ × ℤ => (yz.1, yz.1))) =
    parWith (fun yz : ℤ × ℤ => seq (assignF fun _ : ℤ => yz.1) (assignF fun x => x + 1))
      fun _ => assignF fun yz : ℤ × ℤ => (yz.1, yz.1) := by
  rw [xy, seq_liftLWith_par]

/-- All three programs compute `x′ = y+1 ∧ y′ = y ∧ z′ = y`: "This transformation
does not change the result of a computation". -/
theorem result : seq xy (seq xinc zy) = fun s s' => s'.1 = s.2.1 + 1 ∧ s'.2 = (s.2.1, s.2.1) := by
  rw [step₁, step₂]
  refine Spec.ext fun s s' => ?_
  simp only [parWith, seq, assignF]
  constructor
  · rintro ⟨⟨_, rfl, h1⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨_, rfl, h1⟩, h2⟩

end Examples

/-! ### Buffer (aPToP §8.1.0) -/

namespace Buffer

variable {α : Type u}

/-- The buffer state: the producer owns `b`; the consumer owns `x` and the
source-level copy `c`. -/
abbrev BS (α : Type u) := α × (α × α)

/-- `produce = ···b:= e···`, with the uninteresting parts elided: the new buffer
value is `e b`. -/
def produce (e : α → α) : Spec (BS α) := liftL (assignF e)

/-- `consume = ···x:= b···`, reading the producer's variable. -/
def consume : Spec (BS α) := liftRWith fun b => assignF fun xc => (b, xc.2)

/-- `consume` at source level, `···x:= c···`, reading the copy. -/
def consumeC : Spec (BS α) := liftR (assignF fun xc => (xc.2, xc.2))

/-- The capture `c:= b`. -/
def copy : Spec (BS α) := liftRWith fun b => assignF fun xc => (xc.1, b)

/-- `consume. produce = consume || produce` where "a compiler will have to
capture a copy of the initial value of `b` for `consume` to use" — the copy
law `seq_liftRWith_liftL`. -/
theorem consume_produce (e : α → α) :
    seq consume (produce e) = parWith (fun _ => assignF e) fun b => assignF fun xc : α × α => (b, xc.2) :=
  seq_liftRWith_liftL _ _

/-- The source-level form `c:= b. (consume || produce)` with `consume` reading `c`:
`b′ = e b ∧ x′ = b ∧ c′ = b`. -/
theorem copy_consumeC_produce (e : α → α) :
    seq copy (par (assignF e) (assignF fun xc : α × α => (xc.2, xc.2))) =
      fun s s' : BS α => s'.1 = e s.1 ∧ s'.2 = (s.1, s.1) := by
  rw [copy, seq_liftRWith_par]
  refine Spec.ext fun s s' => ?_
  simp only [parWith, seq, assignF]
  constructor
  · rintro ⟨h1, _, rfl, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, _, rfl, h2⟩

/-- `consume. produce` computes `b′ = e b ∧ x′ = b ∧ c′ = c`. -/
theorem consume_produce_eq (e : α → α) :
    seq consume (produce e) = fun s s' : BS α => s'.1 = e s.1 ∧ s'.2 = (s.1, s.2.2) := by
  rw [consume_produce]
  rfl

/-- The two forms of the unrolled body agree on the program variables `b` and
`x`; they differ only in the auxiliary copy `c`. -/
theorem consume_produce_eq_copy_par (e : α → α) (s s' : BS α) :
    (∃ c', seq consume (produce e) s (s'.1, s'.2.1, c')) ↔
      ∃ c', seq copy (par (assignF e) (assignF fun xc : α × α => (xc.2, xc.2))) s (s'.1, s'.2.1, c') := by
  rw [consume_produce_eq, copy_consumeC_produce]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨c', h1, h2, -⟩
    exact ⟨s.1, h1, h2, rfl⟩
  · rintro ⟨c', h1, h2, -⟩
    exact ⟨s.2.2, h1, h2, rfl⟩

/-- `control = produce. consume. control`: the body of the recursive definition. -/
def controlBody (e : α → α) (C : Spec (BS α)) : Spec (BS α) := seq (produce e) (seq consume C)

/-- `newcontrol = consume. produce. newcontrol`: the body after unrolling once. -/
def newcontrolBody (e : α → α) (N : Spec (BS α)) : Spec (BS α) := seq consume (seq (produce e) N)

/-- `newcontrol = (consume || produce). newcontrol`: the unrolled body "can be
transformed" into a concurrent one, by the copy law. -/
theorem newcontrolBody_eq (e : α → α) (N : Spec (BS α)) :
    newcontrolBody e N =
      seq (parWith (fun _ => assignF e) fun b => assignF fun xc : α × α => (b, xc.2)) N := by
  rw [newcontrolBody, seq_assoc, consume_produce]

/-- Unrolling: if `newcontrol` solves `newcontrol = consume. produce. newcontrol`,
then `control = produce. newcontrol` solves `control = produce. consume. control`. -/
theorem control_of_newcontrol (e : α → α) {N : Spec (BS α)} (hN : IsFixedPoint (newcontrolBody e) N) :
    IsFixedPoint (controlBody e) (seq (produce e) N) := by
  unfold IsFixedPoint at hN ⊢
  unfold controlBody
  conv_rhs => rw [← hN]
  rfl

end Buffer

end LaPToP.Concurrency
