import LaPToP.ProgramTheory.InterpreterLang
import LaPToP.ProgramTheory.InterpreterSyntax

/-!
# The concrete syntax of the interpreter's language

A tokenizer and a recursive-descent parser from text to a `Lang.Program`: named
specifications with the programs that refine them, and a main program, over the
values and expressions of `LaPToP.ProgramTheory.Interpreter.Lang`. As for the
demonstration syntax, nothing new is denoted: a parsed program is `Prog ℕ Value`
with its definitions, and means its `denote`.

## The grammar

```
file      := (name params? '⇐' program | program)*
params    := '(' name (',' name)* ')'
program   := par ('.' par)* '.'?
par       := choice ('||' choice)*
choice    := statement ('or' statement)*
statement := 'ok' | 'tick'
           | name atom* ':=' exp
           | name (',' name)* ':=' exp (',' exp)*   -- simultaneous
           | name ('(' exp (',' exp)* ')')?         -- a call
           | name '!' exp | name '?'                -- output, input
           | 'if' exp ('/' exp)? 'then' program ('else' program)? 'fi'
           | name ':=' 'rand' atom
           | 'while' exp 'do' program 'od'
           | 'do' body 'od'
           | 'for' name ':=' exp ';..' exp 'do' program 'od'
           | 'new' name ':=' exp 'in' program 'end'
           | 'ensure' exp | 'assert' exp
           | '(' program ')'
body      := item ('.' item)* '.'?
item      := 'exit' integer? ('when' exp)?
           | 'if' exp 'then' body ('else' body)? 'fi'
           | 'do' body 'od'
           | choice
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
           | '√' name
```

A file is a list of refinements `P ⇐ ...`, as the book develops a program
(Section 4.1.1), and a main program; with no main program the first
specification is run. A name on the right of a refinement is a call, and may be
the name being refined: that is recursion.

`do body od` is the exit-loop of Section 5.2.1, and is compiled to exactly the
refinement the book says it abbreviates: `do A. exit when b. C od` becomes a
fresh specification `L ⇐ A. if b then ok else C. L`, and the loop is a call of
`L`. `exit n when b` leaves `n` loops; the inner loop is then named as the book
does it, so `P ⇐ do A. do B. exit 2 when c. D od. E od` is `P ⇐ A. Q` with
`Q ⇐ B. if c then ok else D. Q`. An exit may not leave a `while`, a local
scope or a choice. `for i:= m;..n do P od` (Section 5.2.3) is the refinement
`F ⇐ if i < n then P. i:= i+1. F else ok`, with `i` local, `n` evaluated once
before the loop, and `P` forbidden to assign `i`.

A specification may have parameters, `P(x, y) ⇐ ...`, and is then called as
`P(e, f)`: the book's `⟨x: D· B⟩ e = (new x: D := e· B)` of Section 5.5.2, the
arguments all computed before any parameter is bound and the body forbidden to
assign a parameter. `x, y:= e, f` likewise computes both values before assigning
either.

`P || Q` is concurrent composition (Section 8.0). It binds tighter than `.` and
looser than `or`, so `x:= x+1. x:= x-1 || y:= x` needs parentheses around the
sequence, as the book writes it. Each process owns the variables it may assign,
through the specifications it calls, and two processes may not assign the same
one; each sees the other's variables only at their initial values.

`if a/b then P else Q fi` is the probabilistic `if` of Section 5.7: `P` with
probability `a/b`, `Q` otherwise; a `/` at the top of a condition can only be a
probability, since integer division is `div`. `x:= rand n` gives `x` each value
`0,..n` with probability `1/n`. `interp --dist` computes the distribution of the
final states.

A name written `c! e` or `c?` anywhere is a channel (Section 9.1.1): `c! e`
outputs `e`, `c?` inputs, `c` in an expression is the last message input and
`√c` says whether one is waiting. The channel's script so far is the list
variable named `c`, so an input script is given as its initial value.

Juxtaposition is indexing, as in the book: `A i` is item `i` of `A`, and
`A i j:= e` assigns an item of a two-dimensional array. Each symbol has an ASCII
spelling: `<==` `=>` `\/` `/\` `!=` `<=` `>=` `*` `true` `false`, and `⧧` is
accepted for `≠`. `¬` binds tightest, as in the book, so `¬x = y` is `(¬x) = y`;
the word `not` binds looser than a comparison, so `not x = y` is `¬(x = y)`. A
comment runs from `--` to the end of the line.
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
  c == '<' || c == '>' || c == '[' || c == ']' || c == ';' || c == ',' || c == '#' || c == '^' ||
  c == '!' || c == '?' || c == '/'

/-- The book's symbols, each as the token of its ASCII spelling. -/
private def unicodeTok : Char → Option Tok
  | '≤' => some (.sym "<=")
  | '≥' => some (.sym ">=")
  | '≠' => some (.sym "!=")
  | '⧧' => some (.sym "!=")
  | '⇒' => some (.sym "=>")
  | '⇐' => some (.sym "<==")
  | '∧' => some (.sym "/\\")
  | '∨' => some (.sym "\\/")
  | '¬' => some (.sym "¬")
  | '×' => some (.sym "*")
  | '√' => some (.sym "√")
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
      | '|', '|' :: rest => do let ts ← tokenize f rest; .ok (.sym "||" :: ts)
      | '<', '=' :: '=' :: rest => do let ts ← tokenize f rest; .ok (.sym "<==" :: ts)
      | '<', '=' :: rest => do let ts ← tokenize f rest; .ok (.sym "<=" :: ts)
      | ';', '.' :: '.' :: rest => do let ts ← tokenize f rest; .ok (.sym ";.." :: ts)
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
   "exit", "when", "for", "var", "proc", "print", "rand"]

/-- Whether a word is a keyword. -/
def isKeyword (w : String) : Bool := keywords.contains w

/-- The index a name stands for in a table, adding it if it is new. -/
def intern (w : String) (names : List String) : ℕ × List String :=
  match names.idxOf? w with
  | some k => (k, names)
  | none => (names.length, names ++ [w])

/-- The parameters of a definition's head after its `(`, up to the `⇐`. -/
def scanParams : Toks → Option (List String × Toks)
  | .word p :: .sym ")" :: .sym "<==" :: ts => some ([p], ts)
  | .word p :: .sym "," :: ts => (scanParams ts).map fun (ps, ts) => (p :: ps, ts)
  | _ => none

/-- The specifications defined by a refinement `name ⇐ ...` or
`name(p, q, ...) ⇐ ...` anywhere in the tokens, with their parameters, in order
of their first definition. -/
def scanDefs : ℕ → Toks → List (String × List String) → List (String × List String)
  | 0, _, acc => acc
  | f + 1, .word w :: .sym "<==" :: ts, acc =>
    scanDefs f ts (if acc.any (·.1 == w) then acc else acc ++ [(w, [])])
  | f + 1, .word w :: rest@(.sym "(" :: ts), acc =>
    match scanParams ts with
    | some (ps, ts) => scanDefs f ts (if acc.any (·.1 == w) then acc else acc ++ [(w, ps)])
    | none => scanDefs f rest acc
  | f + 1, _ :: ts, acc => scanDefs f ts acc
  | _, [], acc => acc

/-- The channels: the names written `c! e` or `c?` anywhere in the tokens. -/
def scanChans : Toks → List String → List String
  | .word c :: ts, acc =>
    match ts with
    | .sym "!" :: _ | .sym "?" :: _ => scanChans ts (if acc.contains c then acc else acc ++ [c])
    | _ => scanChans ts acc
  | _ :: ts, acc => scanChans ts acc
  | [], acc => acc
termination_by structural ts => ts

/-- Whether a word can name a variable given a value on the command line. -/
def validName (w : String) : Bool :=
  !w.isEmpty && !isKeyword w && (w.toList.head?.map fun c => c.isAlpha || c == '_').getD false &&
    w.toList.all fun c => c.isAlphanum || c == '_'

/-- The parser's state. -/
structure PS where
  /-- The tokens not yet read. -/
  toks : Toks
  /-- The variables: variable `k` is written `names[k]`. -/
  names : List String
  /-- The specifications: those defined in the source first, then the loops'. -/
  procs : List String
  /-- The definitions read so far. -/
  bodies : List (ℕ × P)
  /-- The parameters of each specification, as variables. -/
  params : List (List ℕ)
  /-- The channels: each name with its script variable and its read cursor. -/
  chans : List (String × ℕ × ℕ)

/-- The state with other tokens. -/
def PS.at (st : PS) (ts : Toks) : PS := { st with toks := ts }

private def expectSym (s : String) (st : PS) : Except String PS :=
  match st.toks with
  | .sym t :: rest => if t == s then .ok (st.at rest) else .error s!"expected '{s}', found '{t}'"
  | t :: _ => .error s!"expected '{s}', found '{t.render}'"
  | [] => .error s!"expected '{s}', found the end of the program"

private def expectWord (w : String) (st : PS) : Except String PS :=
  match st.toks with
  | .word v :: rest => if v == w then .ok (st.at rest) else .error s!"expected '{w}', found '{v}'"
  | t :: _ => .error s!"expected '{w}', found '{t.render}'"
  | [] => .error s!"expected '{w}', found the end of the program"

/-- A variable's name, interned. -/
def parseName (st : PS) : Except String (ℕ × PS) :=
  match st.toks with
  | .word w :: rest =>
    if isKeyword w then .error s!"expected a name, found the keyword '{w}'"
    else if st.procs.contains w then .error s!"'{w}' names a specification, not a variable"
    else if st.chans.any (·.1 == w) then .error s!"'{w}' is a channel: write to it with {w}! e"
    else let (x, names) := intern w st.names; .ok (x, { st with toks := rest, names := names })
  | t :: _ => .error s!"expected a name, found '{t.render}'"
  | [] => .error "expected a name, found the end of the program"

/-- A fresh specification for a loop to be compiled to. -/
def newProc (tag : String) (st : PS) : ℕ × PS :=
  (st.procs.length, { st with procs := st.procs ++ [tag ++ "#" ++ toString st.procs.length] })

/-- A fresh variable no source can name, for a loop's bound. -/
def newHidden (st : PS) : ℕ × PS :=
  (st.names.length, { st with names := st.names ++ ["#" ++ toString st.names.length] })

/-- Record a definition. -/
def PS.define (st : PS) (k : ℕ) (body : P) : PS := { st with bodies := st.bodies ++ [(k, body)] }

/-- Fresh hidden variables, one for each of a list. -/
def newHiddens {α : Type} : List α → PS → List ℕ × PS
  | [], st => ([], st)
  | _ :: as, st =>
    let (t, st) := newHidden st
    let (ts, st) := newHiddens as st
    (t :: ts, st)

/-- `new t₁ := e₁ in ... new tₙ := eₙ in p`: every value computed before any is
used, which is what a simultaneous assignment and a call with arguments need. -/
def declareAll : List (ℕ × Exp) → P → P
  | [], p => p
  | (t, e) :: rest, p => declare t e (declareAll rest p)

/-- A call `P(a, b, ...)` of a specification with parameters `p, q, ...`: the
book's `⟨p: D· B⟩ a = (new p: D := a· B)` (Section 5.5.2), the arguments all
evaluated before any parameter is bound. -/
def callWith (k : ℕ) (ps : List ℕ) (args : List Exp) (st : PS) : P × PS :=
  match ps, args with
  | [p], [a] => (declare p a (.call k), st)
  | _, _ =>
    let (ts, st) := newHiddens args st
    (declareAll (ts.zip args) (declareAll (ps.zip (ts.map Exp.var)) (.call k)), st)

/-- `x, y, ...:= e, f, ...`: the values all computed before any is assigned. -/
def assignAll (xs : List ℕ) (es : List Exp) (st : PS) : P × PS :=
  let (ts, st) := newHiddens es st
  let sets : List P := (xs.zip ts).map fun (x, t) => assign x (.var t)
  (declareAll (ts.zip es) (sets.foldr (fun a b => if b matches .ok then a else .seq a b) .ok), st)

/-- `n` things, for a message. -/
def plural (n : ℕ) (thing : String) : String :=
  if n == 1 then s!"1 {thing}" else s!"{n} {thing}s"

/-! ### Expressions -/

/-- Whether a token can begin an atom, so that juxtaposition continues: not a
keyword, and not the name of a specification. -/
def startsAtom (procs : List String) : Tok → Bool
  | .num _ => true
  | .word w => w == "true" || w == "false" || (!isKeyword w && !procs.contains w)
  | .sym s => s == "(" || s == "[" || s == "√"

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

private def advance (st : PS) : PS := st.at st.toks.tail

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
      if startsAtom st.procs t then do
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
    | .num k :: ts => .ok (.lit (.int k), st.at ts)
    | .word "true" :: ts => .ok (.lit (.bool true), st.at ts)
    | .word "false" :: ts => .ok (.lit (.bool false), st.at ts)
    | .sym "(" :: ts => do
      let (a, st) ← parseExp f (st.at ts)
      let st ← expectSym ")" st
      .ok (a, st)
    | .sym "[" :: .sym "]" :: ts => .ok (.nil, (st.at ts))
    | .sym "[" :: ts => do
      let (a, st) ← parseExp f (st.at ts)
      let (as, st) ← parseItems f st
      .ok (Exp.ofList (a :: as), st)
    | .word "if" :: ts => do
      let (c, st) ← parseExp f (st.at ts)
      let st ← expectWord "then" st
      let (a, st) ← parseExp f st
      let st ← expectWord "else" st
      let (b, st) ← parseExp f st
      let st ← expectWord "fi" st
      .ok (.cond c a b, st)
    | .word "rand" :: _ =>
      .error "rand may be used only as x:= rand n; for rand inside an expression, \
        assign it to a fresh variable first, as Section 5.7 does"
    | .sym "√" :: .word c :: ts =>
      match st.chans.find? (·.1 == c) with
      | some (_, M, r) => .ok (check M r, st.at ts)
      | none => .error s!"'{c}' is not a channel"
    | .word w :: ts =>
      match st.chans.find? (·.1 == w) with
      | some (_, M, r) => .ok (message M r, st.at ts)
      | none => do
        let (x, st) ← parseName st
        .ok (.var x, st)
    | t :: _ => .error s!"expected an expression, found '{t.render}'"
    | [] => .error "expected an expression, found the end of the program"
termination_by structural fuel

end

/-! ### Lists of arguments, names and values -/

/-- The arguments of a call, after its `(`, up to the `)`. -/
def parseArgs (fuel : ℕ) (st : PS) : Except String (List Exp × PS) :=
  match fuel with
  | 0 => .error "too many arguments"
  | f + 1 => do
    let (a, st) ← parseExp f st
    match st.toks with
    | .sym "," :: ts => do
      let (as, st) ← parseArgs f (st.at ts)
      .ok (a :: as, st)
    | _ => do
      let st ← expectSym ")" st
      .ok ([a], st)
termination_by structural fuel

/-- The rest of the targets of a simultaneous assignment, after the first `,`, up
to the `:=`. -/
def parseNames (fuel : ℕ) (st : PS) : Except String (List ℕ × PS) :=
  match fuel with
  | 0 => .error "too many variables"
  | f + 1 => do
    let (x, st) ← parseName st
    match st.toks with
    | .sym "," :: ts => do
      let (xs, st) ← parseNames f (st.at ts)
      .ok (x :: xs, st)
    | _ => do
      let st ← expectSym ":=" st
      .ok ([x], st)
termination_by structural fuel

/-- The values of a simultaneous assignment. -/
def parseExps (fuel : ℕ) (st : PS) : Except String (List Exp × PS) :=
  match fuel with
  | 0 => .error "too many values"
  | f + 1 => do
    let (e, st) ← parseExp f st
    match st.toks with
    | .sym "," :: ts => do
      let (es, st) ← parseExps f (st.at ts)
      .ok (e :: es, st)
    | _ => .ok ([e], st)
termination_by structural fuel

/-! ### Loops, compiled to refinements -/

/-- An item of the body of an exit-loop, before it is compiled: a statement, an
exit, an `if` whose branches may exit, or an inner loop. -/
inductive Raw where
  /-- A statement. -/
  | stmt (p : P)
  /-- `exit n when c`. -/
  | exit (n : ℕ) (c : Exp)
  /-- `if c then t else e fi` in a loop body; `jumps` says whether it contains
  an exit or a loop, so that it must be compiled with the rest of the body. -/
  | ifr (jumps : Bool) (c : Exp) (t e : List Raw)
  /-- `do body od`. -/
  | loop (body : List Raw)

/-- Whether an item exits or loops. -/
def Raw.jumps : Raw → Bool
  | .stmt _ => false
  | .ifr j _ _ _ => j
  | _ => true

/-- Compile the rest of a loop body. `K` is what follows the body — the call
that repeats the loop — or nothing at the top of a plain `if`; `E` lists what
`exit 1`, `exit 2`, ... continue with. Each loop becomes a fresh specification
refined by its compiled body, and is itself a call of it. -/
def compile (fuel : ℕ) (items : List Raw) (K : Option P) (E : List P) (st : PS) :
    Except String (P × PS) :=
  match fuel with
  | 0 => .error "loop too long or too deeply nested"
  | f + 1 =>
    match items with
    | [] => .ok (K.getD .ok, st)
    | [.stmt p] =>
      match K with
      | none => .ok (p, st)
      | some k => .ok (.seq p k, st)
    | .stmt p :: rest => do
      let (q, st) ← compile f rest K E st
      .ok (.seq p q, st)
    | .exit n c :: rest =>
      match E[n - 1]? with
      | some target =>
        if n = 0 then .error "there is no 'exit 0'" else do
        let (q, st) ← compile f rest K E st
        .ok (.cond c.test target q, st)
      | none => .error s!"'exit {n}' leaves more loops than there are"
    | .ifr jumps c t e :: rest =>
      if jumps then do
        let (pt, st) ← compile f (t ++ rest) K E st
        let (pe, st) ← compile f (e ++ rest) K E st
        .ok (.cond c.test pt pe, st)
      else do
        let (pt, st) ← compile f t none [] st
        let (pe, st) ← compile f e none [] st
        compile f (.stmt (.cond c.test pt pe) :: rest) K E st
    | .loop body :: rest => do
      let (after, st) ← compile f rest K E st
      let (k, st) := newProc "do" st
      let (b, st) ← compile f body (some (.call k)) (after :: E) st
      .ok (.call k, st.define k b)

/-! ### Programs -/

/-- The tokens that close an enclosing block, so that a trailing `.` is allowed. -/
private def endsBlock : Toks → Bool
  | [] => true
  | .word "else" :: _ => true
  | .word "fi" :: _ => true
  | .word "od" :: _ => true
  | .word "end" :: _ => true
  | .sym ")" :: _ => true
  | .word _ :: .sym "<==" :: _ => true
  | .word _ :: .sym "(" :: ts => (scanParams ts).isSome
  | _ => false

mutual

/-- `program := choice ('.' choice)* '.'?`, built to the right. -/
def parseProg (fuel : ℕ) (st : PS) : Except String (P × PS) :=
  match fuel with
  | 0 => .error "program too long or too deeply nested"
  | f + 1 => do
    let (p, st) ← parsePar f st
    match st.toks with
    | .sym "." :: ts₁ =>
      if endsBlock ts₁ then .ok (p, st.at ts₁)
      else do
        let (q, st) ← parseProg f (st.at ts₁)
        .ok (.seq p q, st)
    | _ => .ok (p, st)
termination_by structural fuel

/-- `par := choice ('||' choice)*`: concurrent composition, which binds tighter
than `.` and looser than `or`. Which variables belong to which process is
settled when the whole file has been read (`resolvePar`). -/
def parsePar (fuel : ℕ) (st : PS) : Except String (P × PS) :=
  match fuel with
  | 0 => .error "program too long or too deeply nested"
  | f + 1 => do
    let (p, st) ← parseChoice f st
    match st.toks with
    | .sym "||" :: ts₁ => do
      let (q, st) ← parsePar f (st.at ts₁)
      .ok (.par (fun _ => false) p q, st)
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
      let (q, st) ← parseChoice f (st.at ts₁)
      .ok (.or p q, st)
    | _ => .ok (p, st)
termination_by structural fuel

/-- The indices of an assignment's target, up to the `:=`. -/
def parseTarget (fuel : ℕ) (st : PS) : Except String (List Exp × PS) :=
  match fuel with
  | 0 => .error "assignment target too long"
  | f + 1 =>
    match st.toks with
    | .sym ":=" :: ts => .ok ([], st.at ts)
    | _ => do
      let (i, st) ← parseAtom f st
      let (is, st) ← parseTarget f st
      .ok (i :: is, st)
termination_by structural fuel

/-- `body := item ('.' item)* '.'?`, the body of an exit-loop or of an `if` in
one, up to the word that closes it. -/
def parseBody (fuel : ℕ) (st : PS) : Except String (List Raw × PS) :=
  match fuel with
  | 0 => .error "loop body too long or too deeply nested"
  | f + 1 => do
    let (r, st) ← parseItem f st
    match st.toks with
    | .sym "." :: ts₁ =>
      if endsBlock ts₁ then .ok ([r], st.at ts₁)
      else do
        let (rs, st) ← parseBody f (st.at ts₁)
        .ok (r :: rs, st)
    | _ => .ok ([r], st)
termination_by structural fuel

/-- An item of a loop body. -/
def parseItem (fuel : ℕ) (st : PS) : Except String (Raw × PS) :=
  match fuel with
  | 0 => .error "loop body too long or too deeply nested"
  | f + 1 =>
    match st.toks with
    | .word "exit" :: ts =>
      let (n, ts) := match ts with
        | .num k :: ts => (k.toNat, ts)
        | ts => (1, ts)
      match ts with
      | .word "when" :: ts => do
        let (c, st) ← parseExp f (st.at ts)
        .ok (.exit n c, st)
      | ts => .ok (.exit n (.lit (.bool true)), st.at ts)
    | .word "if" :: ts => do
      let st₀ := st
      let (c, st) ← parseExp f (st.at ts)
      match st.toks with
      | .sym "/" :: _ => do
        -- a probabilistic `if`, which may not exit: read it as a statement
        let (p, st) ← parseStmt f st₀
        .ok (.stmt p, st)
      | _ => do
        let st ← expectWord "then" st
        let (t, st) ← parseBody f st
        match st.toks with
        | .word "else" :: ts => do
          let (e, st) ← parseBody f (st.at ts)
          let st ← expectWord "fi" st
          .ok (.ifr ((t ++ e).any Raw.jumps) c t e, st)
        | _ => do
          let st ← expectWord "fi" st
          .ok (.ifr (t.any Raw.jumps) c t [.stmt .ok], st)
    | .word "do" :: ts => do
      let (b, st) ← parseBody f (st.at ts)
      let st ← expectWord "od" st
      .ok (.loop b, st)
    | _ => do
      let (p, st) ← parsePar f st
      .ok (.stmt p, st)
termination_by structural fuel

/-- A single statement. -/
def parseStmt (fuel : ℕ) (st : PS) : Except String (P × PS) :=
  match fuel with
  | 0 => .error "program too long or too deeply nested"
  | f + 1 =>
    match st.toks with
    | .word "ok" :: ts => .ok (.ok, st.at ts)
    | .word "tick" :: ts => .ok (.tick, st.at ts)
    | .word "ensure" :: ts => do
      let (c, st) ← parseExp f (st.at ts)
      .ok (ensure c, st)
    | .word "assert" :: ts => do
      let (c, st) ← parseExp f (st.at ts)
      .ok (assert c, st)
    | .word "if" :: ts => do
      let (c, st) ← parseExp f (st.at ts)
      let (d, st) ← match st.toks with
        | .sym "/" :: ts => do
          let (d, st) ← parseExp f (st.at ts)
          .ok (some d, st)
        | _ => .ok (none, st)
      let st ← expectWord "then" st
      let (p, st) ← parseProg f st
      let (q, st) ← match st.toks with
        | .word "else" :: ts => do
          let (q, st) ← parseProg f (st.at ts)
          let st ← expectWord "fi" st
          .ok (q, st)
        | _ => do
          let st ← expectWord "fi" st
          .ok (.ok, st)
      match d with
      | some d => .ok (probIf c d p q, st)
      | none => .ok (ifThen c p q, st)
    | .word "while" :: ts => do
      let (c, st) ← parseExp f (st.at ts)
      let st ← expectWord "do" st
      let (p, st) ← parseProg f st
      let st ← expectWord "od" st
      .ok (loop c p, st)
    | .word "do" :: ts => do
      let (b, st) ← parseBody f (st.at ts)
      let st ← expectWord "od" st
      compile f [.loop b] none [] st
    | .word "for" :: ts => do
      let (i, st) ← parseName (st.at ts)
      let st ← expectSym ":=" st
      let (m, st) ← parseExp f st
      let st ← expectSym ";.." st
      let (n, st) ← parseExp f st
      let st ← expectWord "do" st
      let (body, st) ← parseProg f st
      let st ← expectWord "od" st
      if assigns i body then
        .error s!"the body of a for-loop may not assign its index '{st.names.getD i "?"}'"
      else
        let (hi, st) := newHidden st
        let (k, st) := newProc "for" st
        let step : P := .seq body (.seq (assign i (.bin .add (.var i) (.lit (.int 1)))) (.call k))
        let st := st.define k (ifThen (.bin .lt (.var i) (.var hi)) step .ok)
        .ok (declare hi n (declare i m (.call k)), st)
    | .word c :: .sym "!" :: ts =>
      match st.chans.find? (·.1 == c) with
      | some (_, M, _) => do
        let (e, st) ← parseExp f (st.at ts)
        .ok (output M e, st)
      | none => .error s!"'{c}' is not a channel"
    | .word c :: .sym "?" :: ts =>
      match st.chans.find? (·.1 == c) with
      | some (_, M, r) => .ok (input M r, st.at ts)
      | none => .error s!"'{c}' is not a channel"
    | .word "exit" :: _ =>
      .error "'exit' is allowed only in a do-loop, and not inside a while-loop, a scope or a choice"
    | .word "new" :: ts => do
      let (x, st) ← parseName (st.at ts)
      let st ← expectSym ":=" st
      let (e, st) ← parseExp f st
      let st ← expectWord "in" st
      let (p, st) ← parseProg f st
      let st ← expectWord "end" st
      .ok (declare x e p, st)
    | .sym "(" :: ts => do
      let (p, st) ← parseProg f (st.at ts)
      let st ← expectSym ")" st
      .ok (p, st)
    | .word w :: ts =>
      match st.procs.idxOf? w with
      | some k =>
        match st.params.getD k [], ts with
        | [], .sym "(" :: _ => .error s!"'{w}' takes no arguments"
        | [], ts => .ok (.call k, st.at ts)
        | ps, .sym "(" :: ts => do
          let (args, st) ← parseArgs f (st.at ts)
          if args.length != ps.length then
            .error s!"'{w}' takes {plural ps.length "argument"}, not {args.length}"
          else .ok (callWith k ps args st)
        | ps, _ => .error s!"'{w}' takes {plural ps.length "argument"}"
      | none => do
        let (x, st) ← parseName st
        match st.toks with
        | .sym "," :: ts => do
          let (xs, st) ← parseNames f (st.at ts)
          let (es, st) ← parseExps f st
          let xs := x :: xs
          if es.length != xs.length then
            .error s!"{plural xs.length "variable"} cannot be assigned {plural es.length "value"}"
          else if !xs.Nodup then .error "a variable is assigned twice at once"
          else .ok (assignAll xs es st)
        | .sym ":=" :: .word "rand" :: ts => do
          let (e, st) ← parseAtom f (st.at ts)
          let (hn, st) := newHidden st
          let (hi, st) := newHidden st
          let (k, st) := newProc "rand" st
          .ok (declare hn e (declare hi (.lit (.int 0)) (.call k)), st.define k (randBody k x hn hi))
        | _ => do
          let (idx, st) ← parseTarget f st
          let (e, st) ← parseExp f st
          match idx with
          | [] => .ok (assign x e, st)
          | _ => .ok (assignIdx x idx e, st)
    | t :: _ => .error s!"expected a statement, found '{t.render}'"
    | [] => .error "expected a statement, found the end of the program"
termination_by structural fuel

end

/-- `file := (name '⇐' program | program)*`, with at most one main program. -/
def parseFile (fuel : ℕ) (main : Option P) (st : PS) : Except String (Option P × PS) :=
  match fuel with
  | 0 => .error "program too long"
  | f + 1 =>
    match st.toks with
    | [] => .ok (main, st)
    | .word w :: ts =>
      match st.procs.idxOf? w, (match ts with
          | .sym "<==" :: ts => some ts
          | .sym "(" :: ts => (scanParams ts).map (·.2)
          | _ => none) with
      | some k, some ts =>
        if st.bodies.any (·.1 == k) then .error s!"'{w}' is defined twice"
        else do
          let (b, st) ← parseProg f (st.at ts)
          match (st.params.getD k []).find? (assigns · b) with
          | some x => .error s!"'{w}' may not assign its parameter '{st.names.getD x "?"}'"
          | none => parseFile f main (st.define k b)
      | _, _ =>
        match main with
        | some _ => .error s!"unexpected '{w}' after the end of the program"
        | none => do
          let (p, st) ← parseProg f st
          parseFile f (some p) st
    | t :: _ =>
      match main with
      | some _ => .error s!"unexpected '{t.render}' after the end of the program"
      | none => do
        let (p, st) ← parseProg f st
        parseFile f (some p) st
termination_by structural fuel

/-! ### Who owns what in a concurrent composition -/

/-- The variables a program may assign, given those each specification may. A
local declaration hides its own variable. -/
def assigned (procW : ℕ → List ℕ) : P → List ℕ
  | .assign x _ => [x]
  | .seq p q => assigned procW p ++ assigned procW q
  | .cond _ p q => assigned procW p ++ assigned procW q
  | .or p q => assigned procW p ++ assigned procW q
  | .par _ p q => assigned procW p ++ assigned procW q
  | .whileDo _ p => assigned procW p
  | .newLocal x _ p => (assigned procW p).filter (· != x)
  | .call k => procW k
  | _ => []

/-- What each specification may assign, through the calls it makes: the least
solution, by iteration from nothing. -/
def procWrites (bodies : List (ℕ × P)) : ℕ → List (ℕ × List ℕ) → List (ℕ × List ℕ)
  | 0, w => w
  | f + 1, w =>
    let look := fun k => (w.lookup k).getD []
    let w' := bodies.map fun (k, b) => (k, (assigned look b).eraseDups)
    if w' == w then w else procWrites bodies f w'

/-- Settle each `||`: a process owns the variables it may assign, and the two
processes may not both assign one. -/
def resolvePar (procW : ℕ → List ℕ) (names : List String) : P → Except String P
  | .par _ p q => do
    let p ← resolvePar procW names p
    let q ← resolvePar procW names q
    let a := assigned procW p
    let b := assigned procW q
    match a.find? b.contains with
    | some x =>
      let w := names.getD x "?"
      if w.startsWith "#" && w.endsWith ".read" then
        .error s!"both processes of a || input from channel {(w.drop 1).dropEnd 5}"
      else .error s!"both processes of a || assign {w}"
    | none => .ok (.par (fun x => a.contains x) p q)
  | .seq p q => do .ok (.seq (← resolvePar procW names p) (← resolvePar procW names q))
  | .cond c p q => do .ok (.cond c (← resolvePar procW names p) (← resolvePar procW names q))
  | .or p q => do .ok (.or (← resolvePar procW names p) (← resolvePar procW names q))
  | .whileDo c p => do .ok (.whileDo c (← resolvePar procW names p))
  | .newLocal x e p => do .ok (.newLocal x e (← resolvePar procW names p))
  | p => .ok p

/-- Settle every `||` of a parsed file. -/
def resolveProgram (prog : Program) : Except String Program := do
  let w := procWrites prog.defs (prog.defs.length * (prog.names.length + 1) + 1) []
  let look := fun k => (w.lookup k).getD []
  let main ← resolvePar look prog.names prog.main
  let defs ← prog.defs.mapM fun (k, b) => do .ok (k, ← resolvePar look prog.names b)
  .ok ⟨main, defs, prog.names, prog.procs⟩

/-- The parameters of the definitions, interned as variables. -/
def internParams : List (String × List String) → List String → List String × List (List ℕ)
  | [], names => (names, [])
  | (_, ps) :: defs, names =>
    let (xs, names) := internAll ps names
    let (names, rest) := internParams defs names
    (names, xs :: rest)
where
  /-- Intern each of a list of names. -/
  internAll : List String → List String → List ℕ × List String
    | [], names => ([], names)
    | p :: ps, names =>
      let (x, names) := intern p names
      let (xs, names) := internAll ps names
      (x :: xs, names)

/-- The channels, each with its script variable, which has the channel's name,
and a hidden read cursor. -/
def internChans : List String → List String → List String × List (String × ℕ × ℕ)
  | [], names => (names, [])
  | c :: cs, names =>
    let (M, names) := intern c names
    let (r, names) := intern ("#" ++ c ++ ".read") names
    let (names, rest) := internChans cs names
    (names, (c, M, r) :: rest)

/-- Parse a whole token list, starting from a table of variable names already in
use. The fuel is read off its length. -/
def parseToksWith (names : List String) (ts : Toks) : Except String Program :=
  let defs := scanDefs (ts.length + 1) ts []
  let procs := defs.map (·.1)
  let (names, params) := internParams defs names
  let chanNames := scanChans ts []
  let (names, chans) := internChans chanNames names
  match procs.find? isKeyword, procs.find? names.contains, chanNames.find? procs.contains with
  | some w, _, _ => .error s!"the keyword '{w}' cannot be defined"
  | none, some w, _ => .error s!"'{w}' names a variable, a parameter or a channel, not a specification"
  | none, none, some w => .error s!"'{w}' is both a channel and a specification"
  | none, none, none =>
    match parseFile (8 * ts.length + 32) none ⟨ts, names, procs, [], params, chans⟩ with
    | .error e => .error e
    | .ok (some p, st) => resolveProgram ⟨p, st.bodies, st.names, st.procs⟩
    | .ok (none, st) =>
      match procs with
      | [] => .error "the program is empty"
      | _ :: _ => resolveProgram ⟨.call 0, st.bodies, st.names, st.procs⟩

/-- Parse a whole token list with no names in use. -/
def parseToks (ts : Toks) : Except String Program := parseToksWith [] ts

/-- Parse a program, given the variable names already in use. -/
def parseProgramWith (names : List String) (src : String) : Except String Program := do
  parseToksWith names (← tokenize (src.length + 1) src.toList)

/-- Parse a program. -/
def parseProgram (src : String) : Except String Program := parseProgramWith [] src

/-- Parse a lone expression, given the variable names in use. -/
def parseExpression (names : List String) (src : String) : Except String (Exp × List String) := do
  let ts ← tokenize (src.length + 1) src.toList
  match parseExp (8 * ts.length + 32) ⟨ts, names, [], [], [], []⟩ with
  | .ok (e, ⟨[], names, _, _, _, _⟩) => .ok (e, names)
  | .ok (_, ⟨t :: _, _, _, _, _, _⟩) => .error s!"unexpected '{t.render}' after the end of the expression"
  | .error e => .error e

/-! ### States -/

/-- A state, written out: each name in the table with its value. The loops'
hidden variables are not shown. -/
def renderState (names : List String) (s : St) : String :=
  ", ".intercalate ((names.zipIdx.filter fun (w, _) => !w.startsWith "#").map
    fun (w, k) => s!"{w} = {(s k).render}")

/-! ### Demonstrations, from their tokens

Each demonstration is stated of its token list: the kernel parses the tokens and
runs the program it gets, so these are facts about what the parser produces,
not about a program written separately in Lean. That the tokenizer takes each
source to those tokens is checked by `interp --selftest`, since reducing a string
to its characters in the kernel is prohibitively slow. The facts are checked by
`decide` evaluated in the kernel, which reduces the parser far faster than the
elaborator does. -/

namespace Demo

/-- `i:= 0. s:= 0. while i ≠ n do i:= i+1. s:= s+i od`, with `n` given on the
command line. -/
def sumToSrc : String := "i:= 0. s:= 0. while i ≠ n do i:= i+1. s:= s+i od"

/-- Its tokens. -/
def sumToToks : Toks :=
  [.word "i", .sym ":=", .num 0, .sym ".",
   .word "s", .sym ":=", .num 0, .sym ".",
   .word "while", .word "i", .sym "!=", .word "n", .word "do",
     .word "i", .sym ":=", .word "i", .sym "+", .num 1, .sym ".",
     .word "s", .sym ":=", .word "s", .sym "+", .word "i",
   .word "od"]

/-- The names given on the command line come first in the table, the others in
order of appearance, and a program with no refinements defines nothing. -/
theorem parse_sumTo :
    (parseToksWith ["n"] sumToToks).map (fun prog => (prog.names, prog.procs, prog.defs.length)) =
      .ok (["n", "i", "s"], [], 0) := by decide +kernel

/-- `1 + ... + 10 = 55`, computed by the interpreter from the parsed tokens and
checked by the kernel. -/
theorem sumTo_ten :
    ((parseToksWith ["n"] sumToToks).toOption.bind fun prog =>
      prog.run 100 (initWith [(0, .int 10)])).map (· 2) = some (.int 55) := by decide +kernel

/-- `s:= 0 or s:= 1. ensure s = 1`, the example of Section 5.4.0. -/
def backtrackSrc : String := "s:= 0 or s:= 1. ensure s = 1"

def backtrackToks : Toks :=
  [.word "s", .sym ":=", .num 0, .word "or", .word "s", .sym ":=", .num 1, .sym ".",
   .word "ensure", .word "s", .sym "=", .num 1]

theorem parse_backtrack :
    (parseToks backtrackToks).map (fun prog => (prog.names, prog.procs)) = .ok (["s"], []) := by
  decide +kernel

/-- The search finds the one poststate; the deterministic run finds none. -/
theorem backtrack_runAll :
    ((parseToks backtrackToks).toOption.map fun prog => (prog.runAll 10 init).map (· 0)) =
      some [.int 1] := by decide +kernel

theorem backtrack_run :
    ((parseToks backtrackToks).toOption.map fun prog => (prog.run 10 init).isSome) =
      some false := by decide +kernel

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
    ((parseToks arraysToks).toOption.bind fun prog => prog.run 20 init).map (· 2) =
      some (.bool true) := by decide +kernel

/-! #### Named specifications: the list summation of Section 4.1.1

The book's development, as refinements: `A ⇐ s:= 0. n:= 0. B` and
`B ⇐ if n = #L then ok else s:= s + L n. n:= n+1. B fi`, where `B` on the right
is a recursive call. -/

def listSumSrc : String := "A ⇐ s:= 0. n:= 0. B\nB ⇐ if n = #L then ok else s:= s + L n. n:= n+1. B fi"

def listSumToks : Toks :=
  [.word "A", .sym "<==", .word "s", .sym ":=", .num 0, .sym ".", .word "n", .sym ":=",
   .num 0, .sym ".", .word "B", .word "B", .sym "<==", .word "if", .word "n", .sym "=",
   .sym "#", .word "L", .word "then", .word "ok", .word "else", .word "s", .sym ":=",
   .word "s", .sym "+", .word "L", .word "n", .sym ".", .word "n", .sym ":=", .word "n",
   .sym "+", .num 1, .sym ".", .word "B", .word "fi"]

/-- The sum of `[3; 1; 4; 1; 5]` is `14`, computed by the interpreter from the
refinements and checked by the kernel. -/
theorem listSum_run :
    ((parseToksWith ["L"] listSumToks).toOption.bind fun prog =>
      prog.run 50 (initWith [(0, .list [.int 3, .int 1, .int 4, .int 1, .int 5])])).map (· 1) =
      some (.int 14) := by decide +kernel

/-! #### The exit-loop of Section 5.2.1 -/

/-- `do exit when n ≤ x. x:= x+1 od`, which counts `x` up to `n`: the book's
`x′ = max x n` (`ExitLoopExample.count_up`). -/
def exitLoopSrc : String := "do exit when n ≤ x. x:= x+1 od"

def exitLoopToks : Toks :=
  [.word "do", .word "exit", .word "when", .word "n", .sym "<=", .word "x", .sym ".",
   .word "x", .sym ":=", .word "x", .sym "+", .num 1, .word "od"]

/-- The loop is compiled to a fresh specification refined by the loop body, and
the main program is a call of it. -/
theorem parse_exitLoop :
    (parseToksWith ["n"] exitLoopToks).map (fun prog => (prog.procs, prog.defs.map (·.1))) =
      .ok (["do#0"], [0]) := rfl

theorem exitLoop_run :
    ((parseToksWith ["n"] exitLoopToks).toOption.bind fun prog =>
      prog.run 50 (initWith [(0, .int 5)])).map (· 1) = some (.int 5) := by decide +kernel

theorem exitLoop_run_above :
    ((parseToksWith ["n", "x"] exitLoopToks).toOption.bind fun prog =>
      prog.run 50 (initWith [(0, .int 5), (1, .int 9)])).map (· 1) = some (.int 9) := by
  decide +kernel

/-! #### A deep exit -/

/-- Two loops, the inner one leaving both with `exit 2`. -/
def deepExitSrc : String := "i:= 0. s:= 0. do j:= 0. do exit 2 when i × j > 6. exit when j = 3. j:= j+1. s:= s+1 od. i:= i+1 od"

def deepExitToks : Toks :=
  [.word "i", .sym ":=", .num 0, .sym ".", .word "s", .sym ":=", .num 0, .sym ".",
   .word "do", .word "j", .sym ":=", .num 0, .sym ".", .word "do", .word "exit", .num 2,
   .word "when", .word "i", .sym "*", .word "j", .sym ">", .num 6, .sym ".", .word "exit",
   .word "when", .word "j", .sym "=", .num 3, .sym ".", .word "j", .sym ":=", .word "j",
   .sym "+", .num 1, .sym ".", .word "s", .sym ":=", .word "s", .sym "+", .num 1,
   .word "od", .sym ".", .word "i", .sym ":=", .word "i", .sym "+", .num 1, .word "od"]

/-- It stops the first time `i × j > 6`, at `i = 3`, `j = 3`, having counted
`12` inner iterations. -/
theorem deepExit_run :
    ((parseToks deepExitToks).toOption.bind fun prog => prog.run 200 init).map
      (fun s => (s 0, s 1, s 2)) = some (.int 3, .int 12, .int 3) := by decide +kernel

/-! #### The for-loop of Section 5.2.3 -/

/-- `for i:= 1;..n+1 do s:= s + i od`, summing `1` to `n`. -/
def forLoopSrc : String := "s:= 0. for i:= 1;..n+1 do s:= s + i od"

def forLoopToks : Toks :=
  [.word "s", .sym ":=", .num 0, .sym ".", .word "for", .word "i", .sym ":=", .num 1,
   .sym ";..", .word "n", .sym "+", .num 1, .word "do", .word "s", .sym ":=", .word "s",
   .sym "+", .word "i", .word "od"]

theorem forLoop_run :
    ((parseToksWith ["n"] forLoopToks).toOption.bind fun prog =>
      prog.run 100 (initWith [(0, .int 10)])).map (· 1) = some (.int 55) := by decide +kernel

/-! #### A procedure with parameters, Section 5.5.2 -/

/-- Euclid's algorithm as a recursive procedure: a call `Gcd(a, b)` is the book's
`new a := ...· new b := ...· body`, the arguments computed first. -/
def gcdSrc : String := "Gcd(a, b) ⇐ if b = 0 then g:= a else Gcd(b, a mod b) fi\nGcd(x, y)"

def gcdToks : Toks :=
  [.word "Gcd", .sym "(", .word "a", .sym ",", .word "b", .sym ")", .sym "<==", .word "if",
   .word "b", .sym "=", .num 0, .word "then", .word "g", .sym ":=", .word "a",
   .word "else", .word "Gcd", .sym "(", .word "b", .sym ",", .word "a", .word "mod",
   .word "b", .sym ")", .word "fi", .word "Gcd", .sym "(", .word "x", .sym ",", .word "y",
   .sym ")"]

/-- `gcd(1071, 462) = 21`. -/
theorem gcd_run :
    ((parseToksWith ["x", "y"] gcdToks).toOption.bind fun prog =>
      prog.run 100 (initWith [(0, .int 1071), (1, .int 462)])).map (· 4) = some (.int 21) := by
  decide +kernel

/-! #### Simultaneous assignment -/

/-- `x, y:= y, x` swaps: both values are computed before either is assigned. -/
def swapSrc : String := "x, y:= y, x"

def swapToks : Toks :=
  [.word "x", .sym ",", .word "y", .sym ":=", .word "y", .sym ",", .word "x"]

theorem swap_run :
    ((parseToksWith ["x", "y"] swapToks).toOption.bind fun prog =>
      prog.run 10 (initWith [(0, .int 1), (1, .int 2)])).map (fun s => (s 0, s 1)) =
      some (.int 2, .int 1) := by decide +kernel

/-! #### Channels, Section 9.1.1 -/

/-- The first example of Section 9.1.1, `c?. d! even c`: read a number from `c`
and write whether it is even to `d`. -/
def evenSrc : String := "c?. d! c mod 2 = 0"

def evenToks : Toks :=
  [.word "c", .sym "?", .sym ".", .word "d", .sym "!", .word "c", .word "mod", .num 2,
   .sym "=", .num 0]

/-- From the script `[4]` on `c`, the script written to `d` is `[⊤]`. -/
theorem even_run :
    ((parseToksWith ["c"] evenToks).toOption.bind fun prog =>
      prog.run 20 (initWith [(0, .list [.int 4])])).map (fun s => s 2) =
      some (.list [.bool true]) := by decide +kernel

/-- With no message on `c`, the input waits: without a clock there is no
poststate, and with one the wait is until `∞`. -/
theorem even_run_empty :
    ((parseToks evenToks).toOption.map fun prog => (prog.run 20 init).isSome) = some false := by
  decide +kernel

theorem even_runT_empty :
    ((parseToks evenToks).toOption.bind fun prog =>
      (prog.runT 20 ⟨init, 0⟩).map (·.t)) = some ⊤ := by decide +kernel

/-- Input until none is waiting, `√c` being the check: the total of the script
on `c` is output on `screen`. -/
def channelSrc : String := "do exit when ¬√c. c?. total:= total + c od. screen! total"

def channelToks : Toks :=
  [.word "do", .word "exit", .word "when", .sym "¬", .sym "√", .word "c", .sym ".",
   .word "c", .sym "?", .sym ".", .word "total", .sym ":=", .word "total", .sym "+",
   .word "c", .word "od", .sym ".", .word "screen", .sym "!", .word "total"]

theorem channel_run :
    ((parseToksWith ["c"] channelToks).toOption.bind fun prog =>
      prog.run 100 (initWith [(0, .list [.int 5, .int 6, .int 7])])).map (fun s => s 2) =
      some (.list [.int 18]) := by decide +kernel

/-! #### Concurrent composition, Section 8.0 -/

/-- `x:= y || y:= x`: each process sees the other's variable at its initial
value, so the two exchange values (`Composition.swap_par`). -/
def parSwapSrc : String := "x:= y || y:= x"

def parSwapToks : Toks :=
  [.word "x", .sym ":=", .word "y", .sym "||", .word "y", .sym ":=", .word "x"]

theorem parSwap_run :
    ((parseToksWith ["x", "y"] parSwapToks).toOption.bind fun prog =>
      prog.run 10 (initWith [(0, .int 1), (1, .int 2)])).map (fun s => (s 0, s 1)) =
      some (.int 2, .int 1) := by decide +kernel

/-- `(x:= x+1. x:= x–1) || y:= x`: "if one process is a sequential composition,
the other cannot see its intermediate values" (`Composition.seq_par`), so `y`
ends with the initial `x`. -/
def seqParSrc : String := "(x:= x+1. x:= x-1) || y:= x"

def seqParToks : Toks :=
  [.sym "(", .word "x", .sym ":=", .word "x", .sym "+", .num 1, .sym ".", .word "x",
   .sym ":=", .word "x", .sym "-", .num 1, .sym ")", .sym "||", .word "y", .sym ":=",
   .word "x"]

theorem seqPar_run :
    ((parseToksWith ["x"] seqParToks).toOption.bind fun prog =>
      prog.run 10 (initWith [(0, .int 5)])).map (fun s => (s 0, s 1)) =
      some (.int 5, .int 5) := by decide +kernel

/-- With a clock, the composition finishes when both processes have: the one that
ticks twice decides the time. -/
def parTimeSrc : String := "(tick. tick. a:= 1) || (tick. b:= 2)"

def parTimeToks : Toks :=
  [.sym "(", .word "tick", .sym ".", .word "tick", .sym ".", .word "a", .sym ":=", .num 1,
   .sym ")", .sym "||", .sym "(", .word "tick", .sym ".", .word "b", .sym ":=", .num 2,
   .sym ")"]

theorem parTime_runT :
    ((parseToks parTimeToks).toOption.bind fun prog =>
      (prog.runT 10 ⟨init, 0⟩).map fun st => (st.mem 0, st.mem 1, st.t)) =
      some (.int 1, .int 2, 2) := by decide +kernel

/-! #### Probabilistic programs, Section 5.7 -/

/-- `if 1/3 then x:= 0 else x:= 1 fi`, the book's first example. -/
def probEx1Src : String := "if 1/3 then x:= 0 else x:= 1 fi"

def probEx1Toks : Toks :=
  [.word "if", .num 1, .sym "/", .num 3, .word "then", .word "x", .sym ":=", .num 0,
   .word "else", .word "x", .sym ":=", .num 1, .word "fi"]

/-- `x` is `0` with probability `1/3` and `1` with probability `2/3`, as
`Probabilistic.ex₁_zero` and `Probabilistic.ex₁_one` say. -/
theorem probEx1_dist :
    ((parseToks probEx1Toks).toOption.map fun prog =>
      (prog.runDist 10 init).map fun (s, w) => (s 0, w)) =
      some [(.int 0, 1 / 3), (.int 1, 2 / 3)] := by decide +kernel

/-- The book's "slightly more elaborate example": the first, then
`if x=0 then if 1/2 then x:= x+2 else x:= x+3 else if 1/4 then x:= x+4 else x:= x+5`. -/
def probEx2Src : String := "if 1/3 then x:= 0 else x:= 1 fi. if x = 0 then if 1/2 then x:= x+2 else x:= x+3 fi else if 1/4 then x:= x+4 else x:= x+5 fi fi"

def probEx2Toks : Toks :=
  [.word "if", .num 1, .sym "/", .num 3, .word "then", .word "x", .sym ":=", .num 0,
   .word "else", .word "x", .sym ":=", .num 1, .word "fi", .sym ".", .word "if", .word "x",
   .sym "=", .num 0, .word "then", .word "if", .num 1, .sym "/", .num 2, .word "then",
   .word "x", .sym ":=", .word "x", .sym "+", .num 2, .word "else", .word "x", .sym ":=",
   .word "x", .sym "+", .num 3, .word "fi", .word "else", .word "if", .num 1, .sym "/",
   .num 4, .word "then", .word "x", .sym ":=", .word "x", .sym "+", .num 4, .word "else",
   .word "x", .sym ":=", .word "x", .sym "+", .num 5, .word "fi", .word "fi"]

/-- Its distribution is the book's `(x′=2)/6 + (x′=3)/6 + (x′=5)/6 + (x′=6)/2`
(`Probabilistic.ex₂_eq`). -/
theorem probEx2_dist :
    ((parseToks probEx2Toks).toOption.map fun prog =>
      (prog.runDist 20 init).map fun (s, w) => (s 0, w)) =
      some [(.int 2, 1 / 6), (.int 3, 1 / 6), (.int 5, 1 / 6), (.int 6, 1 / 2)] := by
  decide +kernel

/-- "After execution of `P`, the average value of `e` is `(P. e)`": the average of
`x` is `4 + 2/3`, as `Probabilistic.avg_ex₂_x` proves. -/
theorem probEx2_average :
    ((parseToks probEx2Toks).toOption.map fun prog =>
      ((prog.runDist 20 init).map fun (s, w) => w * (s 0).toInt).sum) = some (4 + 2 / 3) := by
  decide +kernel

/-- `x:= rand 2. x:= x + rand 3`, with the book's fresh variable for the second
`rand` (Section 5.7, `RandomNumbers`). -/
def randSrc : String := "x:= rand 2. r:= rand 3. x:= x + r"

def randToks : Toks :=
  [.word "x", .sym ":=", .word "rand", .num 2, .sym ".", .word "r", .sym ":=",
   .word "rand", .num 3, .sym ".", .word "x", .sym ":=", .word "x", .sym "+", .word "r"]

/-- The probability that `x` ends as `1` is `1/3`, as in the book's
`(x′=0)/6 + (x′=1)/3 + (x′=2)/3 + (x′=3)/6`. -/
theorem rand_one :
    ((parseToks randToks).toOption.map fun prog =>
      (((prog.runDist 50 init).filter fun (s, _) => s 0 == .int 1).map (·.2)).sum) =
      some (1 / 3) := by decide +kernel

/-- The self-test the binary runs: each demonstration's name, source, and the
tokens the theorems above are stated of. -/
def selfTests : List (String × String × Toks) :=
  [("sumTo", sumToSrc, sumToToks), ("backtrack", backtrackSrc, backtrackToks),
   ("arrays", arraysSrc, arraysToks), ("listSum", listSumSrc, listSumToks),
   ("exitLoop", exitLoopSrc, exitLoopToks), ("deepExit", deepExitSrc, deepExitToks),
   ("forLoop", forLoopSrc, forLoopToks), ("gcd", gcdSrc, gcdToks), ("swap", swapSrc, swapToks),
   ("even", evenSrc, evenToks), ("channel", channelSrc, channelToks),
   ("parSwap", parSwapSrc, parSwapToks), ("seqPar", seqParSrc, seqParToks),
   ("parTime", parTimeSrc, parTimeToks), ("probEx1", probEx1Src, probEx1Toks),
   ("probEx2", probEx2Src, probEx2Toks), ("rand", randSrc, randToks)]

end Demo

end LaPToP.ProgramTheory.Interpreter.Lang
