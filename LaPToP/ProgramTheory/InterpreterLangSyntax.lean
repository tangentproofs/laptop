import LaPToP.ProgramTheory.InterpreterLang
import LaPToP.ProgramTheory.InterpreterSyntax

/-!
# The concrete syntax of the interpreter's language

A tokenizer and a recursive-descent parser from text to `Lang.P`, the programs of
`LaPToP.ProgramTheory.Interpreter.Lang`, together with the table of variable names
the parser builds. As for the demonstration syntax, nothing new is denoted: a
parsed program is a `Prog ℕ Value` and means its `denote`.

## The grammar

```
program   := choice ('.' choice)* '.'?
choice    := statement ('or' statement)*
statement := 'ok' | 'tick'
           | name atom* ':=' exp
           | 'if' exp 'then' program ('else' program)? 'fi'
           | 'while' exp 'do' program 'od'
           | 'new' name ':=' exp 'in' program 'end'
           | 'ensure' exp | 'assert' exp
           | '(' program ')'
exp       := disj ('⇒' exp)?
disj      := conj ('∨' conj)*
conj      := neg (('∧' | 'and') neg)*
neg       := 'not' neg | cmp
cmp       := sum (('=' | '≠' | '<' | '≤' | '>' | '≥') sum)?
sum       := prod (('+' | '-') prod)*
prod      := unary (('×' | '*' | 'div' | 'mod') unary)*
unary     := ('-' | '¬' | '#') unary | pow
pow       := app ('^' unary)?
app       := atom atom*
atom      := integer | '⊤' | '⊥' | name | '(' exp ')'
           | '[' ']' | '[' exp (';' exp)* ']'
           | 'if' exp 'then' exp 'else' exp 'fi'
```

Juxtaposition is indexing, as in the book: `A i` is item `i` of `A`, and
`A i j:= e` assigns an item of a two-dimensional array. Each symbol has an ASCII
spelling: `=>` `\/` `/\` `!=` `<=` `>=` `*` `true` `false`, and `⧧` is accepted
for `≠`. `¬` binds tightest, as in the book, so `¬x = y` is `(¬x) = y`; the word
`not` binds looser than a comparison, so `not x = y` is `¬(x = y)`. A comment
runs from `--` to the end of the line.
-/

namespace LaPToP.ProgramTheory.Interpreter.Lang

open LaPToP.ProgramTheory.Interpreter.Demo (Tok Toks)

/-! ### Tokens -/

private def isSpaceChar (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

private def isDigitChar (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def isWordStart (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

private def isWordChar (c : Char) : Bool := isWordStart c || isDigitChar c

/-- The single-character ASCII symbols. -/
private def isSymChar (c : Char) : Bool :=
  c == '+' || c == '-' || c == '*' || c == '(' || c == ')' || c == '=' || c == '.' ||
  c == '<' || c == '>' || c == '[' || c == ']' || c == ';' || c == ',' || c == '#' || c == '^'

/-- The book's symbols, each as the token of its ASCII spelling. -/
private def unicodeTok : Char → Option Tok
  | '≤' => some (.sym "<=")
  | '≥' => some (.sym ">=")
  | '≠' => some (.sym "!=")
  | '⧧' => some (.sym "!=")
  | '⇒' => some (.sym "=>")
  | '∧' => some (.sym "/\\")
  | '∨' => some (.sym "\\/")
  | '¬' => some (.sym "¬")
  | '×' => some (.sym "*")
  | '⊤' => some (.word "true")
  | '⊥' => some (.word "false")
  | _ => none

private def digitsToNat (acc : Nat) : List Char → Nat
  | [] => acc
  | c :: cs => digitsToNat (acc * 10 + (c.toNat - 48)) cs

/-- Split text into tokens. The fuel bounds the number of steps; one character at
least is consumed per unit, so the length of the input is always enough. -/
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
    else if isWordStart c then
      let ws := (c :: cs).takeWhile isWordChar
      let rest := (c :: cs).dropWhile isWordChar
      do let ts ← tokenize f rest; .ok (.word (String.ofList ws) :: ts)
    else
      match c, cs with
      | '-', '-' :: rest => tokenize f (rest.dropWhile (· != '\n'))
      | ':', '=' :: rest => do let ts ← tokenize f rest; .ok (.sym ":=" :: ts)
      | '<', '=' :: rest => do let ts ← tokenize f rest; .ok (.sym "<=" :: ts)
      | '>', '=' :: rest => do let ts ← tokenize f rest; .ok (.sym ">=" :: ts)
      | '!', '=' :: rest => do let ts ← tokenize f rest; .ok (.sym "!=" :: ts)
      | '=', '>' :: rest => do let ts ← tokenize f rest; .ok (.sym "=>" :: ts)
      | '/', '\\' :: rest => do let ts ← tokenize f rest; .ok (.sym "/\\" :: ts)
      | '\\', '/' :: rest => do let ts ← tokenize f rest; .ok (.sym "\\/" :: ts)
      | _, _ =>
        match unicodeTok c with
        | some t => do let ts ← tokenize f cs; .ok (t :: ts)
        | none =>
          if isSymChar c then
            do let ts ← tokenize f cs; .ok (.sym (String.singleton c) :: ts)
          else .error s!"unexpected character '{c}'"

/-! ### Names -/

/-- The words that are not names. -/
def keywords : List String :=
  ["ok", "tick", "ensure", "assert", "if", "then", "else", "fi", "while", "do", "od",
   "new", "in", "end", "or", "and", "not", "true", "false", "div", "mod",
   "exit", "when", "for", "var", "proc", "print"]

/-- Whether a word is a keyword. -/
def isKeyword (w : String) : Bool := keywords.contains w

/-- The variable a name stands for, adding it to the table if it is new. -/
def intern (w : String) (names : List String) : ℕ × List String :=
  match names.idxOf? w with
  | some k => (k, names)
  | none => (names.length, names ++ [w])

/-- The parser's state: the tokens left and the names seen so far. -/
structure PS where
  /-- The tokens not yet read. -/
  toks : Toks
  /-- The table of names: variable `k` is written `names[k]`. -/
  names : List String


private def expectSym (s : String) (st : PS) : Except String PS :=
  match st.toks with
  | .sym t :: rest => if t == s then .ok ⟨rest, st.names⟩ else .error s!"expected '{s}', found '{t}'"
  | t :: _ => .error s!"expected '{s}', found '{t.render}'"
  | [] => .error s!"expected '{s}', found the end of the program"

private def expectWord (w : String) (st : PS) : Except String PS :=
  match st.toks with
  | .word v :: rest => if v == w then .ok ⟨rest, st.names⟩ else .error s!"expected '{w}', found '{v}'"
  | t :: _ => .error s!"expected '{w}', found '{t.render}'"
  | [] => .error s!"expected '{w}', found the end of the program"

/-- A name, interned. -/
def parseName (st : PS) : Except String (ℕ × PS) :=
  match st.toks with
  | .word w :: rest =>
    if isKeyword w then .error s!"expected a name, found the keyword '{w}'"
    else let (x, names) := intern w st.names; .ok (x, ⟨rest, names⟩)
  | t :: _ => .error s!"expected a name, found '{t.render}'"
  | [] => .error "expected a name, found the end of the program"

/-! ### Expressions -/

/-- Whether a token can begin an atom, so that juxtaposition continues. -/
def startsAtom : Tok → Bool
  | .num _ => true
  | .word w => w == "true" || w == "false" || !isKeyword w
  | .sym s => s == "(" || s == "["

/-- The left-associative operators at each level of precedence: `∨` at 1, `∧` at
2, `+ -` at 4, `× div mod` at 5. -/
def leftOp : ℕ → Tok → Option BinOp
  | 1, .sym "\\/" => some .or
  | 2, .sym "/\\" => some .and
  | 2, .word "and" => some .and
  | 4, .sym "+" => some .add
  | 4, .sym "-" => some .sub
  | 5, .sym "*" => some .mul
  | 5, .word "div" => some .div
  | 5, .word "mod" => some .mod
  | _, _ => none

/-- The comparisons. -/
def cmpOp : Tok → Option BinOp
  | .sym "=" => some .eq
  | .sym "!=" => some .ne
  | .sym "<" => some .lt
  | .sym "<=" => some .le
  | .sym ">" => some .gt
  | .sym ">=" => some .ge
  | _ => none

private def headTok (st : PS) : Option Tok := st.toks.head?

private def advance (st : PS) : PS := ⟨st.toks.tail, st.names⟩

mutual

/-- `exp := disj ('⇒' exp)?`; implication associates to the right. -/
def parseExp (fuel : ℕ) (st : PS) : Except String (Exp × PS) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 => do
    let (a, st) ← parseLeft f 1 st
    match headTok st with
    | some (.sym "=>") => do
      let (b, st) ← parseExp f (advance st)
      .ok (.bin .imp a b, st)
    | _ => .ok (a, st)
termination_by structural fuel

/-- The operand of the operators at level `lvl`. -/
def parseBelow (fuel : ℕ) (lvl : ℕ) (st : PS) : Except String (Exp × PS) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 =>
    match lvl with
    | 1 => parseLeft f 2 st
    | 2 => parseNeg f st
    | 4 => parseLeft f 5 st
    | _ => parseUnary f st
termination_by structural fuel

/-- A left-associated chain of the operators at level `lvl`. -/
def parseLeft (fuel : ℕ) (lvl : ℕ) (st : PS) : Except String (Exp × PS) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 => do
    let (a, st) ← parseBelow f lvl st
    parseLeftTail f lvl a st
termination_by structural fuel

/-- The rest of such a chain. -/
def parseLeftTail (fuel : ℕ) (lvl : ℕ) (a : Exp) (st : PS) : Except String (Exp × PS) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 =>
    match (headTok st).bind (leftOp lvl) with
    | some op => do
      let (b, st) ← parseBelow f lvl (advance st)
      parseLeftTail f lvl (.bin op a b) st
    | none => .ok (a, st)
termination_by structural fuel

/-- `neg := 'not' neg | cmp`. -/
def parseNeg (fuel : ℕ) (st : PS) : Except String (Exp × PS) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 =>
    match headTok st with
    | some (.word "not") => do
      let (a, st) ← parseNeg f (advance st)
      .ok (.un .not a, st)
    | _ => do
      let (a, st) ← parseLeft f 4 st
      match (headTok st).bind cmpOp with
      | some op => do
        let (b, st) ← parseLeft f 4 (advance st)
        .ok (.bin op a b, st)
      | none => .ok (a, st)
termination_by structural fuel

/-- `unary := ('-' | '¬' | '#') unary | pow`, and `pow := app ('^' unary)?`. -/
def parseUnary (fuel : ℕ) (st : PS) : Except String (Exp × PS) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 =>
    match headTok st with
    | some (.sym "-") => do let (a, st) ← parseUnary f (advance st); .ok (.un .neg a, st)
    | some (.sym "¬") => do let (a, st) ← parseUnary f (advance st); .ok (.un .not a, st)
    | some (.sym "#") => do let (a, st) ← parseUnary f (advance st); .ok (.un .len a, st)
    | _ => do
      let (a, st) ← parseAtom f st
      let (a, st) ← parseAppTail f a st
      match headTok st with
      | some (.sym "^") => do
        let (b, st) ← parseUnary f (advance st)
        .ok (.bin .pow a b, st)
      | _ => .ok (a, st)
termination_by structural fuel

/-- Juxtaposition: `a i j ...` indexes `a` by each atom in turn. -/
def parseAppTail (fuel : ℕ) (a : Exp) (st : PS) : Except String (Exp × PS) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 =>
    match headTok st with
    | some t =>
      if startsAtom t then do
        let (i, st) ← parseAtom f st
        parseAppTail f (.index a i) st
      else .ok (a, st)
    | none => .ok (a, st)
termination_by structural fuel

/-- The items of a list literal after its first, up to the closing `]`. -/
def parseItems (fuel : ℕ) (st : PS) : Except String ((List Exp) × PS) :=
  match fuel with
  | 0 => .error "list too long"
  | f + 1 =>
    match headTok st with
    | some (.sym ";") => do
      let (a, st) ← parseExp f (advance st)
      let (as, st) ← parseItems f st
      .ok (a :: as, st)
    | _ => do
      let st ← expectSym "]" st
      .ok ([], st)
termination_by structural fuel

/-- An atom. -/
def parseAtom (fuel : ℕ) (st : PS) : Except String (Exp × PS) :=
  match fuel with
  | 0 => .error "expression too long or too deeply nested"
  | f + 1 =>
    match st.toks with
    | .num k :: ts => .ok (.lit (.int k), ⟨ts, st.names⟩)
    | .word "true" :: ts => .ok (.lit (.bool true), ⟨ts, st.names⟩)
    | .word "false" :: ts => .ok (.lit (.bool false), ⟨ts, st.names⟩)
    | .sym "(" :: ts => do
      let (a, st) ← parseExp f ⟨ts, st.names⟩
      let st ← expectSym ")" st
      .ok (a, st)
    | .sym "[" :: .sym "]" :: ts => .ok (.nil, ⟨ts, st.names⟩)
    | .sym "[" :: ts => do
      let (a, st) ← parseExp f ⟨ts, st.names⟩
      let (as, st) ← parseItems f st
      .ok (Exp.ofList (a :: as), st)
    | .word "if" :: ts => do
      let (c, st) ← parseExp f ⟨ts, st.names⟩
      let st ← expectWord "then" st
      let (a, st) ← parseExp f st
      let st ← expectWord "else" st
      let (b, st) ← parseExp f st
      let st ← expectWord "fi" st
      .ok (.cond c a b, st)
    | .word _ :: _ => do
      let (x, st) ← parseName st
      .ok (.var x, st)
    | t :: _ => .error s!"expected an expression, found '{t.render}'"
    | [] => .error "expected an expression, found the end of the program"
termination_by structural fuel

end

/-! ### Programs -/

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

/-- `program := choice ('.' choice)* '.'?`, built to the right. -/
def parseProg (fuel : ℕ) (st : PS) : Except String (P × PS) :=
  match fuel with
  | 0 => .error "program too long or too deeply nested"
  | f + 1 => do
    let (p, st) ← parseChoice f st
    match st.toks with
    | .sym "." :: ts₁ =>
      if endsBlock ts₁ then .ok (p, ⟨ts₁, st.names⟩)
      else do
        let (q, st) ← parseProg f ⟨ts₁, st.names⟩
        .ok (.seq p q, st)
    | _ => .ok (p, st)
termination_by structural fuel

/-- `choice := statement ('or' statement)*`. -/
def parseChoice (fuel : ℕ) (st : PS) : Except String (P × PS) :=
  match fuel with
  | 0 => .error "program too long or too deeply nested"
  | f + 1 => do
    let (p, st) ← parseStmt f st
    match st.toks with
    | .word "or" :: ts₁ => do
      let (q, st) ← parseChoice f ⟨ts₁, st.names⟩
      .ok (.or p q, st)
    | _ => .ok (p, st)
termination_by structural fuel

/-- The indices of an assignment's target, up to the `:=`. -/
def parseTarget (fuel : ℕ) (st : PS) : Except String ((List Exp) × PS) :=
  match fuel with
  | 0 => .error "assignment target too long"
  | f + 1 =>
    match st.toks with
    | .sym ":=" :: ts => .ok ([], ⟨ts, st.names⟩)
    | _ => do
      let (i, st) ← parseAtom f st
      let (is, st) ← parseTarget f st
      .ok (i :: is, st)
termination_by structural fuel

/-- A single statement. -/
def parseStmt (fuel : ℕ) (st : PS) : Except String (P × PS) :=
  match fuel with
  | 0 => .error "program too long or too deeply nested"
  | f + 1 =>
    match st.toks with
    | .word "ok" :: ts => .ok (.ok, ⟨ts, st.names⟩)
    | .word "tick" :: ts => .ok (.tick, ⟨ts, st.names⟩)
    | .word "ensure" :: ts => do
      let (c, st) ← parseExp f ⟨ts, st.names⟩
      .ok (ensure c, st)
    | .word "assert" :: ts => do
      let (c, st) ← parseExp f ⟨ts, st.names⟩
      .ok (assert c, st)
    | .word "if" :: ts => do
      let (c, st) ← parseExp f ⟨ts, st.names⟩
      let st ← expectWord "then" st
      let (p, st) ← parseProg f st
      match st.toks with
      | .word "else" :: ts => do
        let (q, st) ← parseProg f ⟨ts, st.names⟩
        let st ← expectWord "fi" st
        .ok (ifThen c p q, st)
      | _ => do
        let st ← expectWord "fi" st
        .ok (ifThen c p .ok, st)
    | .word "while" :: ts => do
      let (c, st) ← parseExp f ⟨ts, st.names⟩
      let st ← expectWord "do" st
      let (p, st) ← parseProg f st
      let st ← expectWord "od" st
      .ok (loop c p, st)
    | .word "new" :: ts => do
      let (x, st) ← parseName ⟨ts, st.names⟩
      let st ← expectSym ":=" st
      let (e, st) ← parseExp f st
      let st ← expectWord "in" st
      let (p, st) ← parseProg f st
      let st ← expectWord "end" st
      .ok (declare x e p, st)
    | .sym "(" :: ts => do
      let (p, st) ← parseProg f ⟨ts, st.names⟩
      let st ← expectSym ")" st
      .ok (p, st)
    | _ => do
      let (x, st) ← parseName st
      let (idx, st) ← parseTarget f st
      let (e, st) ← parseExp f st
      match idx with
      | [] => .ok (assign x e, st)
      | _ => .ok (assignIdx x idx e, st)
termination_by structural fuel

end

/-- Parse a whole token list, starting from a table of names already in use. The
fuel is read off its length, and nothing may be left over. -/
def parseToksWith (names : List String) (ts : Toks) : Except String (P × List String) :=
  match parseProg (8 * ts.length + 32) ⟨ts, names⟩ with
  | .ok (p, ⟨[], names⟩) => .ok (p, names)
  | .ok (_, ⟨t :: _, _⟩) => .error s!"unexpected '{t.render}' after the end of the program"
  | .error e => .error e

/-- Parse a whole token list with no names in use. -/
def parseToks (ts : Toks) : Except String (P × List String) := parseToksWith [] ts

/-- Parse a program, given the names already in use, into the abstract syntax and
the extended table of names. -/
def parseProgramWith (names : List String) (src : String) : Except String (P × List String) := do
  parseToksWith names (← tokenize (src.length + 1) src.toList)

/-- Parse a program. -/
def parseProgram (src : String) : Except String (P × List String) := parseProgramWith [] src

/-- Parse a lone expression, given the names in use. -/
def parseExpression (names : List String) (src : String) : Except String (Exp × List String) := do
  let ts ← tokenize (src.length + 1) src.toList
  match parseExp (8 * ts.length + 32) ⟨ts, names⟩ with
  | .ok (e, ⟨[], names⟩) => .ok (e, names)
  | .ok (_, ⟨t :: _, _⟩) => .error s!"unexpected '{t.render}' after the end of the expression"
  | .error e => .error e

/-! ### States -/

/-- A state, written out: each name in the table with its value. -/
def renderState (names : List String) (s : St) : String :=
  ", ".intercalate (names.zipIdx.map fun (w, k) => s!"{w} = {(s k).render}")

/-! ### The parser produces the demonstration programs

As in `InterpreterSyntax`, the agreement of the parser with programs written in
Lean is a theorem about token lists, and the tokenizer's agreement with the
source text is checked by `interp --selftest`. -/

namespace Demo

/-- `i:= 0. s:= 0. while i ≠ n do i:= i+1. s:= s+i od`, with `n` the first name
in use (given on the command line), then `i` and `s`. -/
def sumTo : P :=
  .seq (assign 1 (.lit (.int 0)))
    (.seq (assign 2 (.lit (.int 0)))
      (loop (.bin .ne (.var 1) (.var 0))
        (.seq (assign 1 (.bin .add (.var 1) (.lit (.int 1))))
          (assign 2 (.bin .add (.var 2) (.var 1))))))

/-- Its source. -/
def sumToSrc : String := "i:= 0. s:= 0. while i ≠ n do i:= i+1. s:= s+i od"

/-- Its tokens. -/
def sumToToks : Toks :=
  [.word "i", .sym ":=", .num 0, .sym ".",
   .word "s", .sym ":=", .num 0, .sym ".",
   .word "while", .word "i", .sym "!=", .word "n", .word "do",
     .word "i", .sym ":=", .word "i", .sym "+", .num 1, .sym ".",
     .word "s", .sym ":=", .word "s", .sym "+", .word "i",
   .word "od"]

theorem parse_sumTo : parseToksWith ["n"] sumToToks = .ok (sumTo, ["n", "i", "s"]) := rfl

/-- `1 + ... + 10 = 55`, computed by the interpreter and checked by the kernel. -/
theorem sumTo_ten : (run 100 sumTo (initWith [(0, .int 10)])).map (· 2) = some (.int 55) := by decide +kernel

/-- `s:= 0 or s:= 1. ensure s = 1`, the example of Section 5.4.0. -/
def backtrack : P :=
  .seq (.or (assign 0 (.lit (.int 0))) (assign 0 (.lit (.int 1))))
    (ensure (.bin .eq (.var 0) (.lit (.int 1))))

def backtrackSrc : String := "s:= 0 or s:= 1. ensure s = 1"

def backtrackToks : Toks :=
  [.word "s", .sym ":=", .num 0, .word "or", .word "s", .sym ":=", .num 1, .sym ".",
   .word "ensure", .word "s", .sym "=", .num 1]

theorem parse_backtrack : parseToks backtrackToks = .ok (backtrack, ["s"]) := rfl

/-- The search finds the one poststate; the deterministic run finds none. -/
theorem backtrack_runAll : (runAll 10 backtrack init).map (· 0) = [.int 1] := rfl
theorem backtrack_run : run 10 backtrack init = none := rfl

/-- The two examples of Section 5.1.0, as source text. -/
def arraysSrc : String := "A:= [0;0;0;0;0]. A 2:= 3. i:= 2. A i:= 4. b:= A i = A 2"

def arraysToks : Toks :=
  [.word "A", .sym ":=", .sym "[", .num 0, .sym ";", .num 0, .sym ";", .num 0, .sym ";",
     .num 0, .sym ";", .num 0, .sym "]", .sym ".",
   .word "A", .num 2, .sym ":=", .num 3, .sym ".",
   .word "i", .sym ":=", .num 2, .sym ".",
   .word "A", .word "i", .sym ":=", .num 4, .sym ".",
   .word "b", .sym ":=", .word "A", .word "i", .sym "=", .word "A", .num 2]

/-- `A 2:= 3. i:= 2. A i:= 4. A i = A 2` "should equal ⊤", and does. -/
theorem arrays_run :
    ((parseToks arraysToks).toOption.bind fun (p, _) => run 20 p init).map (· 2) =
      some (.bool true) := by decide +kernel

/-- The self-test the binary runs: each demonstration's name, source, and the
tokens the theorems above are stated of. -/
def selfTests : List (String × String × Toks) :=
  [("sumTo", sumToSrc, sumToToks), ("backtrack", backtrackSrc, backtrackToks),
   ("arrays", arraysSrc, arraysToks)]

end Demo

end LaPToP.ProgramTheory.Interpreter.Lang
