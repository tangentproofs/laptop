import LaPToP.ProgramTheory.Interpreter

/-!
# A concrete syntax for the demonstration programs

`LaPToP.ProgramTheory.Interpreter.Demo` gives the programming notations a
first-order abstract syntax (`Exp`, `Bexp`, and the helpers `set`, `ifThen`,
`loop`, `declare`) over three integer variables `n`, `i`, `s`, so that the
example programs are data. This module adds the last missing layer for running
them outside Lean: a tokenizer and a recursive-descent parser from text to that
same abstract syntax, plus a rendering of states. The command-line binary
(`InterpMain`, `lake exe interp`) is thin glue over `parseProgram`,
`Interpreter.run` and `Interpreter.runAll`.

Nothing new is denoted here. The parser produces `Demo.P = Prog Vr ℤ`, so a
parsed program is executed by the same `run` / `runAll` and means the same
`denote` as a program written in Lean; the soundness and completeness theorems
apply to it unchanged.

## The grammar

```
program   := choice ('.' choice)* '.'?
choice    := statement ('or' statement)*
statement := 'ok'
           | 'tick'
           | var ':=' exp
           | 'if' cond 'then' program 'else' program 'fi'
           | 'while' cond 'do' program 'od'
           | 'new' var ':=' exp 'in' program 'end'
           | 'ensure' cond
           | 'assert' cond
           | '(' program ')'
cond      := rel ('and' rel)*
rel       := 'not' rel | exp ('=' | '<=' | '!=') exp
exp       := term (('+' | '-') term)*
term      := factor ('*' factor)*
factor    := integer | var | '-' factor | '(' exp ')'
var       := 'n' | 'i' | 's'
```

`.` is the book's sequential composition and binds loosest, so
`s:= 0 or s:= 1. ensure s = 1` is the choice followed by the `ensure`, as in
Section 5.4.0. A condition may not be parenthesized — `not` and the comparisons
give enough grouping — while an expression may.

## Honest scope

This is the surface syntax of the *demonstrations*, not of the book: three
integer variables of fixed names, no declarations of new names, no arrays (the
array demonstration has its own variable type), no concurrency, no time, no
channels, and no output. Parsing is total: the tokenizer and the parser are
structurally recursive on a fuel budget derived from the input, and every
failure is an `Except String` message rather than a partial function.
-/

namespace LaPToP.ProgramTheory.Interpreter.Demo

/-! ### Tokens -/

/-- A token: an integer literal, a word (variable or keyword), or a symbol. -/
inductive Tok where
  /-- An integer literal. -/
  | num (k : Int)
  /-- A word: a variable name or a keyword. -/
  | word (w : String)
  /-- A symbol. -/
  | sym (s : String)
  deriving DecidableEq, Repr

/-- A token as it was written, for error messages. -/
def Tok.render : Tok → String
  | .num k => toString k
  | .word w => w
  | .sym s => s

/-- A list of tokens. -/
abbrev Toks := List Tok

private def isSpaceChar (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

private def isDigitChar (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def isWordChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

/-- The single-character symbols. -/
private def isSymChar (c : Char) : Bool :=
  c == '+' || c == '-' || c == '*' || c == '(' || c == ')' || c == '=' || c == '.'

/-- The value of a run of decimal digits. Written out rather than taken from
`String.toInt?` so that the kernel can reduce it: the agreement between this
parser and the programs written in Lean is a theorem, not a test. -/
private def digitsToNat (acc : Nat) : List Char → Nat
  | [] => acc
  | c :: cs => digitsToNat (acc * 10 + (c.toNat - 48)) cs

/-- Split text into tokens. The fuel bounds the number of tokens; one character
at least is consumed per unit, so the length of the input is always enough. -/
def tokenize : ℕ → List Char → Except String Toks
  | 0, [] => .ok []
  | 0, _ => .error "program too long to tokenize"
  | _ + 1, [] => .ok []
  | f + 1, c :: cs =>
    if isSpaceChar c then tokenize f cs
    else if isDigitChar c then
      let ds := (c :: cs).takeWhile isDigitChar
      let rest := (c :: cs).dropWhile isDigitChar
      do let ts ← tokenize f rest; .ok (.num (Int.ofNat (digitsToNat 0 ds)) :: ts)
    else if isWordChar c then
      let ws := (c :: cs).takeWhile isWordChar
      let rest := (c :: cs).dropWhile isWordChar
      do let ts ← tokenize f rest; .ok (.word (String.ofList ws) :: ts)
    else
      match c, cs with
      | ':', '=' :: rest => do let ts ← tokenize f rest; .ok (.sym ":=" :: ts)
      | '<', '=' :: rest => do let ts ← tokenize f rest; .ok (.sym "<=" :: ts)
      | '!', '=' :: rest => do let ts ← tokenize f rest; .ok (.sym "!=" :: ts)
      | _, _ =>
        if isSymChar c then
          do let ts ← tokenize f cs; .ok (.sym (String.singleton c) :: ts)
        else .error s!"unexpected character '{c}'"

/-! ### The parser -/

private def expectSym (s : String) : Toks → Except String Toks
  | .sym t :: rest => if t == s then .ok rest else .error s!"expected '{s}', found '{t}'"
  | t :: _ => .error s!"expected '{s}', found '{t.render}'"
  | [] => .error s!"expected '{s}', found the end of the program"

private def expectWord (w : String) : Toks → Except String Toks
  | .word v :: rest => if v == w then .ok rest else .error s!"expected '{w}', found '{v}'"
  | t :: _ => .error s!"expected '{w}', found '{t.render}'"
  | [] => .error s!"expected '{w}', found the end of the program"

private def parseVar : Toks → Except String (Vr × Toks)
  | .word "n" :: rest => .ok (.n, rest)
  | .word "i" :: rest => .ok (.i, rest)
  | .word "s" :: rest => .ok (.s, rest)
  | t :: _ => .error s!"expected a variable (n, i or s), found '{t.render}'"
  | [] => .error "expected a variable (n, i or s), found the end of the program"

mutual

/-- `exp := term (('+' | '-') term)*`. -/
def parseExp (fuel : ℕ) (ts : Toks) : Except String (Exp × Toks) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 => do
    let (e, ts) ← parseTerm f ts
    parseExpTail f e ts
termination_by structural fuel

/-- The `+`/`-` tail of an expression, left-associated. -/
def parseExpTail (fuel : ℕ) (e : Exp) (ts : Toks) : Except String (Exp × Toks) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 =>
    match ts with
    | .sym "+" :: ts => do
      let (e₂, ts) ← parseTerm f ts
      parseExpTail f (.add e e₂) ts
    | .sym "-" :: ts => do
      let (e₂, ts) ← parseTerm f ts
      parseExpTail f (.sub e e₂) ts
    | ts => .ok (e, ts)
termination_by structural fuel

/-- `term := factor ('*' factor)*`. -/
def parseTerm (fuel : ℕ) (ts : Toks) : Except String (Exp × Toks) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 => do
    let (e, ts) ← parseFactor f ts
    parseTermTail f e ts
termination_by structural fuel

/-- The `*` tail of a term, left-associated. -/
def parseTermTail (fuel : ℕ) (e : Exp) (ts : Toks) : Except String (Exp × Toks) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 =>
    match ts with
    | .sym "*" :: ts => do
      let (e₂, ts) ← parseFactor f ts
      parseTermTail f (.mul e e₂) ts
    | ts => .ok (e, ts)
termination_by structural fuel

/-- `factor := integer | var | '-' factor | '(' exp ')'`. -/
def parseFactor (fuel : ℕ) (ts : Toks) : Except String (Exp × Toks) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 =>
    match ts with
    | .num k :: ts => .ok (.lit k, ts)
    | .word "n" :: ts => .ok (.var .n, ts)
    | .word "i" :: ts => .ok (.var .i, ts)
    | .word "s" :: ts => .ok (.var .s, ts)
    | .sym "-" :: ts => do
      let (e, ts) ← parseFactor f ts
      .ok (.sub (.lit 0) e, ts)
    | .sym "(" :: ts => do
      let (e, ts) ← parseExp f ts
      let ts ← expectSym ")" ts
      .ok (e, ts)
    | t :: _ => .error s!"expected an expression, found '{t.render}'"
    | [] => .error "expected an expression, found the end of the program"
termination_by structural fuel

end

mutual

/-- `cond := rel ('and' rel)*`. -/
def parseCond (fuel : ℕ) (ts : Toks) : Except String (Bexp × Toks) :=
  match fuel with
  | 0 => .error "condition too long or too deeply nested"
  | f + 1 => do
    let (b, ts) ← parseRel f ts
    parseCondTail f b ts

/-- The `and` tail of a condition, left-associated. -/
def parseCondTail (fuel : ℕ) (b : Bexp) (ts : Toks) : Except String (Bexp × Toks) :=
  match fuel with
  | 0 => .error "condition too long or too deeply nested"
  | f + 1 =>
    match ts with
    | .word "and" :: ts => do
      let (b₂, ts) ← parseRel f ts
      parseCondTail f (.conj b b₂) ts
    | ts => .ok (b, ts)
termination_by structural fuel

/-- `rel := 'not' rel | exp ('=' | '<=' | '!=') exp`. -/
def parseRel (fuel : ℕ) (ts : Toks) : Except String (Bexp × Toks) :=
  match fuel with
  | 0 => .error "condition too long or too deeply nested"
  | f + 1 =>
    match ts with
    | .word "not" :: ts => do
      let (b, ts) ← parseRel f ts
      .ok (.neg b, ts)
    | ts => do
      let (a, ts) ← parseExp f ts
      match ts with
      | .sym "=" :: ts => do let (b, ts) ← parseExp f ts; .ok (.eq a b, ts)
      | .sym "<=" :: ts => do let (b, ts) ← parseExp f ts; .ok (.le a b, ts)
      | .sym "!=" :: ts => do let (b, ts) ← parseExp f ts; .ok (.neg (.eq a b), ts)
      | t :: _ => .error s!"expected '=', '<=' or '!=', found '{t.render}'"
      | [] => .error "expected a comparison, found the end of the program"
termination_by structural fuel

end

/-- The tokens that close an enclosing block, so that a trailing `.` is allowed. -/
private def endsBlock : Toks → Bool
  | [] => true
  | .word "else" :: _ => true
  | .word "fi" :: _ => true
  | .word "od" :: _ => true
  | .word "end" :: _ => true
  | .sym ")" :: _ => true
  | _ => false

mutual

/-- `program := choice ('.' choice)* '.'?`, the book's sequential composition,
which binds loosest. A `.` just before the end of a block is allowed. Composition
is built to the right, as the Lean demonstrations write it; it is associative
(`Spec.seq_assoc`), so the choice of shape is a convenience. -/
def parseProg (fuel : ℕ) (ts : Toks) : Except String (P × Toks) :=
  match fuel with
  | 0 => .error "program too long or too deeply nested"
  | f + 1 => do
    let (p, ts) ← parseChoice f ts
    match ts with
    | .sym "." :: ts₁ =>
      if endsBlock ts₁ then .ok (p, ts₁)
      else do
        let (q, ts₂) ← parseProg f ts₁
        .ok (.seq p q, ts₂)
    | _ => .ok (p, ts)
termination_by structural fuel

/-- `choice := statement ('or' statement)*`, which binds tighter than `.`. -/
def parseChoice (fuel : ℕ) (ts : Toks) : Except String (P × Toks) :=
  match fuel with
  | 0 => .error "program too long or too deeply nested"
  | f + 1 => do
    let (p, ts) ← parseStmt f ts
    match ts with
    | .word "or" :: ts₁ => do
      let (q, ts₂) ← parseChoice f ts₁
      .ok (.or p q, ts₂)
    | _ => .ok (p, ts)
termination_by structural fuel

/-- A single statement. -/
def parseStmt (fuel : ℕ) (ts : Toks) : Except String (P × Toks) :=
  match fuel with
  | 0 => .error "program too long or too deeply nested"
  | f + 1 =>
    match ts with
    | .word "ok" :: ts => .ok (.ok, ts)
    | .word "tick" :: ts => .ok (.tick, ts)
    | .word "ensure" :: ts => do
      let (b, ts) ← parseCond f ts
      .ok (.ensure b.eval, ts)
    | .word "assert" :: ts => do
      let (b, ts) ← parseCond f ts
      .ok (.assert b.eval, ts)
    | .word "if" :: ts => do
      let (b, ts) ← parseCond f ts
      let ts ← expectWord "then" ts
      let (p, ts) ← parseProg f ts
      let ts ← expectWord "else" ts
      let (q, ts) ← parseProg f ts
      let ts ← expectWord "fi" ts
      .ok (ifThen b p q, ts)
    | .word "while" :: ts => do
      let (b, ts) ← parseCond f ts
      let ts ← expectWord "do" ts
      let (p, ts) ← parseProg f ts
      let ts ← expectWord "od" ts
      .ok (loop b p, ts)
    | .word "new" :: ts => do
      let (x, ts) ← parseVar ts
      let ts ← expectSym ":=" ts
      let (e, ts) ← parseExp f ts
      let ts ← expectWord "in" ts
      let (p, ts) ← parseProg f ts
      let ts ← expectWord "end" ts
      .ok (declare x e p, ts)
    | .sym "(" :: ts => do
      let (p, ts) ← parseProg f ts
      let ts ← expectSym ")" ts
      .ok (p, ts)
    | ts => do
      let (x, ts) ← parseVar ts
      let ts ← expectSym ":=" ts
      let (e, ts) ← parseExp f ts
      .ok (set x e, ts)
termination_by structural fuel

end

/-- Parse a whole token list: the fuel is read off its length, and nothing may
be left over. -/
def parseToks (ts : Toks) : Except String P :=
  match parseProg (8 * ts.length + 32) ts with
  | .ok (p, []) => .ok p
  | .ok (_, t :: _) => .error s!"unexpected '{t.render}' after the end of the program"
  | .error e => .error e

/-- Parse a program in the concrete syntax into the abstract syntax the
interpreter runs. Every failure is a message; the function is total. -/
def parseProgram (src : String) : Except String P := do
  parseToks (← tokenize (src.length + 1) src.toList)

/-! ### The parser produces the demonstration programs

`Interpreter.Demo` writes its example programs in Lean and proves things about
them. These theorems say that the concrete syntax of the same programs parses to
*those very terms* — so what the binary runs is what was proved, not a lookalike.

They are stated of the token list, not of the source text. Reducing a string
literal to its characters in the kernel is prohibitively slow, while reducing the
parser is instant; that the tokenizer takes each source below to the tokens
beside it is *checked when the binary runs* (`interp --selftest`), not proved,
and the difference is recorded rather than hidden.
-/

/-- The concrete syntax of `Demo.sumTo`. -/
def sumToSrc : String := "i:= 0. s:= 0. while i != n do i:= i+1. s:= s+i od"

/-- Its tokens. -/
def sumToToks : Toks :=
  [.word "i", .sym ":=", .num 0, .sym ".",
   .word "s", .sym ":=", .num 0, .sym ".",
   .word "while", .word "i", .sym "!=", .word "n", .word "do",
     .word "i", .sym ":=", .word "i", .sym "+", .num 1, .sym ".",
     .word "s", .sym ":=", .word "s", .sym "+", .word "i",
   .word "od"]

/-- The parser turns them into `Demo.sumTo` itself. -/
theorem parseToks_sumTo : parseToks sumToToks = .ok sumTo := rfl

/-- The concrete syntax of `Demo.count`. -/
def countSrc : String := "while i != n do i:= i+1. s:= s+1 od"

/-- Its tokens. -/
def countToks : Toks :=
  [.word "while", .word "i", .sym "!=", .word "n", .word "do",
     .word "i", .sym ":=", .word "i", .sym "+", .num 1, .sym ".",
     .word "s", .sym ":=", .word "s", .sym "+", .num 1,
   .word "od"]

/-- The parser turns them into `Demo.count`, the loop with a proved
specification. -/
theorem parseToks_count : parseToks countToks = .ok count := rfl

/-- The concrete syntax of `Demo.backtrack`, the example of Section 5.4.0. -/
def backtrackSrc : String := "s:= 0 or s:= 1. ensure s = 1"

/-- Its tokens. -/
def backtrackToks : Toks :=
  [.word "s", .sym ":=", .num 0, .word "or", .word "s", .sym ":=", .num 1, .sym ".",
   .word "ensure", .word "s", .sym "=", .num 1]

/-- The parser turns them into `Demo.backtrack`: the choice binds tighter than
the composition, as the book writes it. -/
theorem parseToks_backtrack : parseToks backtrackToks = .ok backtrack := rfl

/-- The concrete syntax of `Demo.withLocal`. -/
def withLocalSrc : String := "new i := 5 in s:= s + i end"

/-- Its tokens. -/
def withLocalToks : Toks :=
  [.word "new", .word "i", .sym ":=", .num 5, .word "in",
   .word "s", .sym ":=", .word "s", .sym "+", .word "i", .word "end"]

/-- The parser turns them into `Demo.withLocal`, the local declaration that does
not leak. -/
theorem parseToks_withLocal : parseToks withLocalToks = .ok withLocal := rfl

/-- The self-test the binary runs: each demonstration program, its source, and
the tokens the theorems above are stated of. Checking that the tokenizer takes
the source to those tokens closes the gap between `parseToks` and
`parseProgram`. -/
def selfTests : List (String × String × Toks) :=
  [("sumTo", sumToSrc, sumToToks), ("count", countSrc, countToks),
   ("backtrack", backtrackSrc, backtrackToks), ("withLocal", withLocalSrc, withLocalToks)]


/-! ### States -/

/-- The state with the given values of `n`, `i` and `s`. -/
def state (n i s : ℤ) : St := fun v => match v with | .n => n | .i => i | .s => s

/-- `start n` is the state with that `n` and everything else zero. -/
theorem state_zero_zero (n : ℤ) : state n 0 0 = start n := by
  funext v; cases v <;> rfl

/-- A state, written out. -/
def renderState (st : St) : String := s!"n = {st Vr.n}, i = {st Vr.i}, s = {st Vr.s}"

end LaPToP.ProgramTheory.Interpreter.Demo
