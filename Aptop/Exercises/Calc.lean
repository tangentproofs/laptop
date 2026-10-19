import Ampheck.Twins

/-!
# Exercises written as calculations

The proofs here are written in aPToP's own notation, in the calculation files of
`Aptop/Exercises/calc/`, as the book lays a proof out: one line per step, the
connective in the margin, the law at the end of the line. `ampheck_proofs` checks
each step with the Ampheck kernel and then elaborates each calculation as a Lean
theorem, whose every step Lean proves again (`Ampheck.ToLean`).

A specification and its implementation are separate files: the implementation
`extends` the specification, inherits its state and named specifications, and
must refine every specification it inherits or calls.
-/

namespace Aptop.Exercises.Calc

/-! ### Exercises 121, 136, 137 -/

namespace Ch4
ampheck_proofs "calc/ch4.calc"
end Ch4

namespace Ch4b
ampheck_proofs "calc/ch4b.calc"
end Ch4b

namespace Ch4c
ampheck_proofs "calc/ch4c.calc"
end Ch4c

/-! ### Exercise 139 -/

namespace Ex139
ampheck_proofs "calc/ex139.calc"
end Ex139

/-! ### Exercise 140 -/

ampheck_proofs "calc/sum.spec.calc"
ampheck_proofs "calc/sum.calc"

end Aptop.Exercises.Calc
