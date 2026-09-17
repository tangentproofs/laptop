/-!
# Deferred exercise statements

Chapter 10 of Hehner's *A Practical Theory of Programming* lists the exercises
for Chapters 0–9. This module provides an opaque `Prop`-valued placeholder so
each exercise can be recorded as a theorem *signature* with `sorry`, without
claiming `True` or `False`. Proofs are intentionally deferred (Memnar #1032
standing exception: exercise statement stubs only).
-/

namespace LaPToP.Exercises

/-- Opaque goal for aPToP Chapter 10 exercise `n`. Not provable without `sorry`
or an additional axiom; used only for statement-inventory stubs. -/
opaque Statement (n : Nat) : Prop

end LaPToP.Exercises
