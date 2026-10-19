import Ampheck.Expr
import Ampheck.Parser
import Ampheck.Law
import Ampheck.Laws
import Ampheck.Doc
import Ampheck.Render
import Ampheck.Json
import Ampheck.Script
import Ampheck.Api
import Ampheck.Replay
import Ampheck.Proof
import Ampheck.Lean
import Ampheck.Tactics
import Ampheck.Twins
import Ampheck.Proofs.Demo

/-!
# Ampheck

The kernel of an Ampheck proof session. Ampheck is inspired by Netty, the
calculational prover's assistant designed by Eric Hehner, Robert Will, Lev
Naiman, David Kordalewski and others at the University of Toronto (named for
Netty van Gasteren), and described in the Netty document
(<https://www.cs.toronto.edu/~hehner/Netty.pdf>, also
`Netty_document.pdf`); Ampheck is an independent reimplementation of that
design as a Lean kernel and a web window. Like Netty, it is a prover's
assistant, not a prover; it keeps the proof,
the direction, the context and the law lists, and it offers *the results of
applying laws* as the suggestions for the next line.

What is here is the document model and the machinery under those three panes,
with no user interface but a script language and `lake exe ampheck`:

* `Ampheck.Expr` — the boolean and number fragment of the aPToP grammar, with
  the operand positions and types the direction machinery needs;
* `Ampheck.Parser` — text to expressions, laws and scripts;
* `Ampheck.Law` — laws, their six variants, and matching;
* `Ampheck.Laws` — the boolean law list, read from `Ampheck/laws/boolean.laws` at
  compile time and checked in Lean to consist of tautologies;
* `Ampheck.Doc` — the proof document, the zoom stack, the context, the
  suggestions, the commands, and what a finished proof proves;
* `Ampheck.Render` — the three panes as text;
* `Ampheck.Json` — saving and loading a proof;
* `Ampheck.Script` — a session and the script language `lake exe ampheck` runs;
* `Ampheck.Api` — the same session as one JSON request and one JSON answer, which
  is what a window with three panes talks to;
* `Ampheck.Replay` — the document's own example, replayed and checked in Lean;
* `Ampheck.Proof` — calculations written as the book writes them, in a
  calculation file, read back and checked step by step;
* `Ampheck.Lean` — `ampheck_proofs`, which translates a checked calculation file
  into Lean theorems, every step re-proved by Lean;
* `Ampheck.Proofs.Demo` — a calculation file so translated.

It is deliberately independent of the rest of this repository: it imports
neither Mathlib nor `Aptop`, so it builds in seconds. The laws it ships with
are the same Binary laws of aPToP §11.3.1 that `Aptop.BasicTheories.Binary`
proves about `Bool`, transcribed into a law file.
-/