import Netty.Twins

/-!
# Exercises written as calculations

The proofs here are written in aPToP's own notation, in the calculation files of
`LaPToP/Exercises/calc/`, as the book lays a proof out: one line per step, the
connective in the margin, the law at the end of the line. `netty_proofs` checks
each step with the Netty kernel and then elaborates each calculation as a Lean
theorem, whose every step Lean proves again (`Netty.ToLean`).

A specification and its implementation are separate files: the implementation
`extends` the specification, inherits its state and named specifications, and
must refine every specification it inherits or calls.
-/

namespace LaPToP.Exercises.Calc

/-! ### Exercises 121, 136, 137 -/

namespace Ch4
netty_proofs "calc/ch4.calc"
end Ch4

namespace Ch4b
netty_proofs "calc/ch4b.calc"
end Ch4b

namespace Ch4c
netty_proofs "calc/ch4c.calc"
end Ch4c

/-! ### Exercise 139 -/

namespace Ex139
netty_proofs "calc/ex139.calc"
end Ex139

/-! ### Exercise 140 -/

netty_proofs "calc/sum.spec.calc"
netty_proofs "calc/sum.calc"

end LaPToP.Exercises.Calc
