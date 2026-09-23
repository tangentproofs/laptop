import Netty.Expr
import Netty.Parser
import Netty.Law
import Netty.Laws
import Netty.Doc
import Netty.Render
import Netty.Json
import Netty.Script
import Netty.Replay

/-!
# Netty

The kernel of a Netty proof session: the calculational proof tool described in
`Netty_document.pdf` by Eric Hehner, Robert Will, Lev Naiman and David
Kordalewski. Netty is a prover's assistant, not a prover; it keeps the proof,
the direction, the context and the law lists, and it offers *the results of
applying laws* as the suggestions for the next line.

What is here is the document model and the machinery under those three panes,
with no user interface but a script language and `lake exe netty`:

* `Netty.Expr` — the boolean and number fragment of the aPToP grammar, with
  the operand positions and types the direction machinery needs;
* `Netty.Parser` — text to expressions, laws and scripts;
* `Netty.Law` — laws, their six variants, and matching;
* `Netty.Laws` — the boolean law list, read from `Netty/laws/boolean.laws` at
  compile time and checked in Lean to consist of tautologies;
* `Netty.Doc` — the proof document, the zoom stack, the context, the
  suggestions, the commands, and what a finished proof proves;
* `Netty.Render` — the three panes as text;
* `Netty.Json` — saving and loading a proof;
* `Netty.Script` — a session and the script language `lake exe netty` runs;
* `Netty.Replay` — the document's own example, replayed and checked in Lean.

It is deliberately independent of the rest of this repository: it imports
neither Mathlib nor `LaPToP`, so it builds in seconds. The laws it ships with
are the same Binary laws of aPToP §11.3.1 that `LaPToP.BasicTheories.Binary`
proves about `Bool`, transcribed into a law file.
-/