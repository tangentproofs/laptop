import LaPToP.ProgramTheory.InterpreterSyntax
import LaPToP.ProgramTheory.NetworkLang
import LaPToP.ProgramTheory.B4Lang
import LaPToP.ProgramTheory.Alloc

/-!
# The source texts, read by the kernel

The parser theorems are stated of token lists (`sumToToks` and its fellows).
Here the kernel runs the tokenizer on each demonstration's source text and
checks that it gives exactly those tokens, so the theorems are about the text
the binary reads. It also reads the allocator's source, through the tokenizer
and `interp --b4`'s parser, as the statement proved in `Alloc`.

`interp --selftest` still runs the same checks, on the binary.
-/

namespace LaPToP.ProgramTheory.Interpreter

/-- **The demonstrations' tokens are their texts'**, for the first syntax. -/
theorem Demo.selfTests_tokenize :
    ∀ x ∈ Demo.selfTests, Demo.tokenize (x.2.1.length + 1) x.2.1.toList = .ok x.2.2 := by
  decide +kernel

/-- **The demonstrations' tokens are their texts'**: the tokenizer takes the
source text of each demonstration, programs and networks, to the token list its
parser theorems are stated of. -/
theorem Lang.Demo.selfTests_tokenize :
    ∀ x ∈ Lang.Demo.selfTests ++ Lang.Demo.netSelfTests,
      Lang.tokenize (x.2.1.length + 1) x.2.1.toList = .ok x.2.2 := by
  decide +kernel

/-- **The allocator's source is the allocator proved**: tokenized and read by
`interp --b4`'s parser, `Alloc.allocSrc` is `Alloc.allocStmt`, the statement of
`Alloc.alloc_sEval` and `Alloc.alloc_on_b4`. -/
theorem Lang.allocSrc_reads :
    (Lang.tokenize (Alloc.allocSrc.length + 1) Alloc.allocSrc.toList >>= Lang.parseB4 ["n", "M"]).map
      (·.procs) = .ok [Alloc.allocStmt] := by
  decide +kernel

end LaPToP.ProgramTheory.Interpreter
