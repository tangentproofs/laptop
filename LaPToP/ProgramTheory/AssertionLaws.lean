import LaPToP.ProgramTheory.OldTheory
import LaPToP.ProgramTheory.Assertions

/-!
# Assertion laws

This module formalizes the Assertions table of the Reference chapter (Section
11.3.12) of Eric Hehner's *A Practical Theory of Programming* (aPToP),
p. 244, and the remaining sequential-composition distributivity law of
Section 11.3.10.

"Let `P` and `Q` be specifications. Let `A` be an assertion and let `A′` be the
same as `A` but with primes on all the variables.
`A ∧ (P. Q) = A∧P. Q`; `A ⇒ (P.Q) ⇐ A⇒P. Q`; `(P.Q) ∧ A′ = P. Q∧A′`;
`(P.Q) ⇐ A′ ⇐ P. Q⇐A′`; `P. A∧Q = P∧A′. Q`; `P. Q ⇐ P∧A′. A⇒Q`.
`A` is a sufficient precondition for `P` to be refined by `S` if and only if
`A⇒P` is refined by `S`. `A` is a sufficient postcondition for `P` to be refined
by `S` if and only if `A′⇒P` is refined by `S`."

Section 11.3.10: "`P. if b then Q else R = if P. b then P. Q else P. R`
distributivity (unprimed `b`)".

## The model

An assertion is a predicate `A : σ → Prop` on states; `pre A` is `A` read on the
prestate, `post A` is `A′`, read on the poststate. The six laws are equalities
and refinements of `Spec σ`. `P. b` for a binary expression `b` of the
intermediate state is not itself a specification; the distributivity law is
proved in two honest forms: for a deterministic `P` (`det e`, the assignments
of the book), where `P. b` is `b` at the unique intermediate state; and in
general as the case split inside `P. …`
(`P. if b then Q else R = (P∧b′. Q) ∨ (P∧¬b′. R)`).
-/

namespace LaPToP.ProgramTheory

namespace Spec

universe u

variable {σ : Type u}

/-- An assertion `A` read on the prestate. -/
def pre (A : σ → Prop) : Spec σ := fun s _ => A s

/-- The assertion `A′`: `A` read on the poststate. -/
def post (A : σ → Prop) : Spec σ := fun _ s' => A s'

variable (A : σ → Prop) (P Q R S : Spec σ)

/-- `A ∧ (P. Q) = A∧P. Q`. -/
theorem pre_and_seq : and (pre A) (seq P Q) = seq (and (pre A) P) Q :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨hA, s'', hP, hQ⟩ => ⟨s'', ⟨hA, hP⟩, hQ⟩, fun ⟨s'', ⟨hA, hP⟩, hQ⟩ => ⟨hA, s'', hP, hQ⟩⟩

/-- `A ⇒ (P.Q) ⇐ A⇒P. Q`. -/
theorem pre_imp_seq_refines : Refines (fun s s' => A s → seq P Q s s') (seq (fun s s' => A s → P s s') Q) :=
  fun _ _ ⟨s'', hAP, hQ⟩ hA => ⟨s'', hAP hA, hQ⟩

/-- `(P.Q) ∧ A′ = P. Q∧A′`. -/
theorem seq_and_post : and (seq P Q) (post A) = seq P (and Q (post A)) :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨⟨s'', hP, hQ⟩, hA⟩ => ⟨s'', hP, hQ, hA⟩, fun ⟨s'', hP, hQ, hA⟩ => ⟨⟨s'', hP, hQ⟩, hA⟩⟩

/-- `(P.Q) ⇐ A′ ⇐ P. Q⇐A′`. -/
theorem seq_post_imp_refines : Refines (fun s s' => A s' → seq P Q s s') (seq P fun s s' => A s' → Q s s') :=
  fun _ _ ⟨s'', hP, hQ⟩ hA => ⟨s'', hP, hQ hA⟩

/-- `P. A∧Q = P∧A′. Q`: the assertion on the intermediate state can be attached to either side. -/
theorem seq_pre_and : seq P (and (pre A) Q) = seq (and P (post A)) Q :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨s'', hP, hA, hQ⟩ => ⟨s'', ⟨hP, hA⟩, hQ⟩, fun ⟨s'', ⟨hP, hA⟩, hQ⟩ => ⟨s'', hP, hA, hQ⟩⟩

/-- `P. Q ⇐ P∧A′. A⇒Q`. -/
theorem seq_refines_and_post_imp : Refines (seq P Q) (seq (and P (post A)) fun s s' => A s → Q s s') :=
  fun _ _ ⟨s'', ⟨hP, hA⟩, hQ⟩ => ⟨s'', hP, hQ hA⟩

/-- "`A` is a sufficient precondition for `P` to be refined by `S` if and only if `A⇒P` is refined
by `S`." -/
theorem sufficientPre_iff : OldTheory.SufficientPre P S A ↔ Refines (fun s s' => A s → P s s') S :=
  ⟨fun h s s' hS hA => h s hA s' hS, fun h s hA s' hS => h s s' hS hA⟩

/-- "`A` is a sufficient postcondition for `P` to be refined by `S` if and only if `A′⇒P` is refined
by `S`." -/
theorem sufficientPost_iff : OldTheory.SufficientPost P S A ↔ Refines (fun s s' => A s' → P s s') S :=
  ⟨fun h s s' hS hA => h s' hA s hS, fun h s' hA s hS => h s s' hS hA⟩

/-! ### `P. if b then Q else R` (aPToP §11.3.10) -/

variable (b : σ → Prop)

/-- `P. if b then Q else R = (P∧b′. Q) ∨ (P∧¬b′. R)`: the general content of the distributivity law
— the condition is tested on the intermediate state. -/
theorem seq_cond_eq_or :
    seq P (cond b Q R) = or (seq (and P (post b)) Q) (seq (and P (post fun s => ¬ b s)) R) :=
  Spec.ext fun _ _ => by
    constructor
    · rintro ⟨s'', hP, ⟨hb, hQ⟩ | ⟨hb, hR⟩⟩
      · exact Or.inl ⟨s'', ⟨hP, hb⟩, hQ⟩
      · exact Or.inr ⟨s'', ⟨hP, hb⟩, hR⟩
    · rintro (⟨s'', ⟨hP, hb⟩, hQ⟩ | ⟨s'', ⟨hP, hb⟩, hR⟩)
      · exact ⟨s'', hP, Or.inl ⟨hb, hQ⟩⟩
      · exact ⟨s'', hP, Or.inr ⟨hb, hR⟩⟩

/-- A deterministic specification `σ′ = e σ` (the assignments). -/
def det (e : σ → σ) : Spec σ := fun s s' => s' = e s

/-- Substitution Law for `det e`. -/
theorem det_seq (e : σ → σ) : seq (det e) P = fun s s' => P (e s) s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- `P. if b then Q else R = if P. b then P. Q else P. R` for deterministic `P`: `P. b` is `b` at the
unique intermediate state. -/
theorem det_seq_cond (e : σ → σ) :
    seq (det e) (cond b Q R) = cond (fun s => b (e s)) (seq (det e) Q) (seq (det e) R) := by
  rw [det_seq, det_seq, det_seq]
  rfl

end Spec

end LaPToP.ProgramTheory
