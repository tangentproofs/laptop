/-!
# Deferred exercise statements

Chapter 10 of Hehner's *A Practical Theory of Programming* lists the exercises
for Chapters 0–9. This module provides an opaque `Prop`-valued placeholder so
an exercise not yet formalized can be recorded as a theorem *signature* with
`sorry`, without claiming `True` or `False`. As exercises are formalized, their
stubs are replaced by real statements and proofs (`MISSING.md` §5).
-/

namespace LaPToP.Exercises

/-- Opaque goal for aPToP Chapter 10 exercise `n`. Not provable without `sorry`
or an additional axiom; used only for statement-inventory stubs. -/
opaque Statement (n : Nat) : Prop

end LaPToP.Exercises
