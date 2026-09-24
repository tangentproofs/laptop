import Netty.Expr

/-!
# Reading Netty expressions from text

A tokenizer and a recursive-descent parser for the boolean and number fragment
of `Netty.Expr`, following the aPToP grammar printed in the Netty document.
Text enters the kernel in three places — the lines of a law file, direct entry
into the focus, and the scripts the headless command line replays — and all
three come through here.

The grammar, weakest operator first:

```
expr   := imp  (('≡' | '⟹' | '⟸') imp)*
imp    := or   (('⇒' | '⇐') or)*
or     := and  ('∨' and)*
and    := neg  ('∧' neg)*
neg    := '¬' neg | rel
rel    := arith (('=' | '⧧' | '<' | '>' | '≤' | '≥') arith)*
arith  := term (('+' | '-') term)*
term   := atom ('×' atom)*
atom   := identifier | number | '⊤' | '⊥' | '(' expr ')'
        | 'if' expr 'then' expr 'else' expr 'fi'
```

Two features of it are the book's and look odd at first.

* `¬` sits *between* `∧` and `=`, so `¬ a = b` is `¬(a = b)`. That is aPToP's
  precedence, not a typo.
* `≡ ⟹ ⟸` are the book's *large* `= ⇒ ⇐`: the same three operators at the
  lowest precedence. The Netty document leaves them out of its grammar because
  inside a proof the margin supplies them ("when an operator appears in the
  left margin of a proof, it has lowest precedence"). A law file has no margin,
  so it needs them: `duality: ¬(a ∧ b) ≡ ¬a ∨ ¬b` is a law, whereas the same
  line with a small `=` does not parse at all.

Every binary operator associates to the left.

Each operator has an ASCII spelling as well as the book's glyph, so a law file
can be typed on any keyboard:

| glyph | ASCII | | glyph | ASCII | | glyph | ASCII |
| ----- | ----- | - | ----- | ----- | - | ----- | ----- |
| `¬`   | `~`   | | `≤`   | `=<`  | | `≡`   | `==`  |
| `∧`   | `/\`  | | `≥`   | `>=`  | | `⟹`   | `==>` |
| `∨`   | `\/`  | | `×`   | `*`   | | `⟸`   | `<==` |
| `⇒`   | `=>`  | | `⊤`   | `T`   | | `·`   | `.`   |
| `⇐`   | `<=`  | | `⊥`   | `F`   | | `⧧`   | `!=`  |

`T` and `F` are therefore reserved and cannot be used as identifiers.

`if … then … else … fi` is the document's conditional expression. It closes
itself, so it needs no parentheses and takes whole expressions in all three
places: `if b then x else y fi ∧ z` is the conditional and-ed with `z`. The four
words are reserved in expression position for the same reason `T` and `F` are: an
identifier spelled `if`, `then`, `else` or `fi` is no longer readable.
-/

namespace Netty

/-- A lexical token of the expression language. -/
inductive Tok
  /-- An identifier. -/                     | ident (s : String)
  /-- A number literal. -/                  | num (n : Nat)
  /-- A binary operator. -/                 | op (o : BinOp)
  /-- A *large* `= ⇒ ⇐`: the same operator at the lowest precedence. -/
                                            | bigOp (o : BinOp)
  /-- `¬`. -/                               | neg
  /-- `⊤`. -/                               | top
  /-- `⊥`. -/                               | bot
  /-- `(`. -/                               | lpar
  /-- `)`. -/                               | rpar
  /-- `,`, separating law variables. -/     | comma
  /-- `·`, ending a quantifier. -/          | dot
  /-- `∀`. -/                               | univ
  deriving Repr, DecidableEq, Inhabited

namespace Tok

/-- How the token is written, for error messages. -/
def render : Tok → String
  | ident s => s
  | num n => toString n
  | op o => o.symbol
  | bigOp .eq => "≡" | bigOp .imp => "⟹" | bigOp .rimp => "⟸"
  | bigOp o => o.symbol
  | neg => "¬" | top => "⊤" | bot => "⊥"
  | lpar => "(" | rpar => ")" | comma => "," | dot => "·" | univ => "∀"

instance : ToString Tok := ⟨render⟩

end Tok

namespace Parser

/-- Strip leading and trailing whitespace. Spelled out here because the
`String` API for it moved between toolchains. -/
def trim (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- Whether `s` begins with the character `c`. -/
def beginsWith (s : String) (c : Char) : Bool :=
  match s.toList with
  | d :: _ => d == c
  | [] => false

/-- Characters that may start an identifier. -/
private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

/-- Characters that may continue an identifier. -/
private def isIdentRest (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- Every symbol, longest spelling first, so that `==>` is read before `==`
and `==` before `=>`. -/
private def symbols : List (List Char × Tok) :=
  [ ("==>".toList, .bigOp .imp), ("<==".toList, .bigOp .rimp),
    ("==".toList, .bigOp .eq),
    ("=>".toList, .op .imp), ("<=".toList, .op .rimp),
    ("=<".toList, .op .le), (">=".toList, .op .ge), ("!=".toList, .op .ne),
    ("/\\".toList, .op .and), ("\\/".toList, .op .or),
    ("≡".toList, .bigOp .eq), ("⟹".toList, .bigOp .imp), ("⟸".toList, .bigOp .rimp),
    ("⇒".toList, .op .imp), ("⇐".toList, .op .rimp),
    ("∧".toList, .op .and), ("∨".toList, .op .or),
    ("⧧".toList, .op .ne), ("≠".toList, .op .ne),
    ("≤".toList, .op .le), ("≥".toList, .op .ge),
    ("=".toList, .op .eq), ("<".toList, .op .lt), (">".toList, .op .gt),
    ("+".toList, .op .add), ("-".toList, .op .sub),
    ("–".toList, .op .sub), ("−".toList, .op .sub),
    ("×".toList, .op .mul), ("*".toList, .op .mul),
    ("¬".toList, .neg), ("~".toList, .neg),
    ("⊤".toList, .top), ("⊥".toList, .bot),
    ("(".toList, .lpar), (")".toList, .rpar), (",".toList, .comma),
    ("·".toList, .dot), (".".toList, .dot), ("∀".toList, .univ) ]

/-- Split text into tokens. The fuel is the length of the input and every step
consumes at least one character, so the function is total. -/
private def tokenizeAux : Nat → List Char → Except String (List Tok)
  | _, [] => .ok []
  | 0, _ => .error "expression too long"
  | fuel + 1, cs@(c :: cs') =>
      if c.isWhitespace then tokenizeAux fuel cs'
      else if c.isDigit then
        let digits := String.ofList (c :: cs'.takeWhile Char.isDigit)
        let rest := cs'.dropWhile Char.isDigit
        (tokenizeAux fuel rest).map (Tok.num (digits.toNat?.getD 0) :: ·)
      else if isIdentStart c then
        let name := String.ofList (c :: cs'.takeWhile isIdentRest)
        let rest := cs'.dropWhile isIdentRest
        let tok :=
          if name == "T" then Tok.top
          else if name == "F" then Tok.bot
          else if name == "forall" then Tok.univ
          else Tok.ident name
        (tokenizeAux fuel rest).map (tok :: ·)
      else
        match symbols.find? (fun s => s.1.isPrefixOf cs) with
        | some s => (tokenizeAux fuel (cs.drop s.1.length)).map (s.2 :: ·)
        | none => .error s!"unexpected character ‘{c}’"

/-- Split text into tokens. -/
def tokenize (s : String) : Except String (List Tok) :=
  let cs := s.toList
  tokenizeAux cs.length cs

/-- The operators parsed at each precedence level of the grammar above. Level
`0` holds the large operators, level `4` is prefix `¬` and level `8` is an
atom, so those three do not appear here. -/
private def opsAt : Nat → List BinOp
  | 0 => [.eq, .imp, .rimp]
  | 1 => [.imp, .rimp]
  | 2 => [.or]
  | 3 => [.and]
  | 5 => [.eq, .ne, .lt, .gt, .le, .ge]
  | 6 => [.add, .sub]
  | 7 => [.mul]
  | _ => []

/-- The result of parsing a prefix of a token list. -/
private abbrev PRes := Except String (Expr × List Tok)

/-- Consume one of the words that bracket a conditional expression. -/
private def expectWord (w : String) : List Tok → Except String (List Tok)
  | .ident v :: rest =>
      if v == w then .ok rest else .error s!"expected ‘{w}’ but found ‘{v}’"
  | t :: _ => .error s!"expected ‘{w}’ but found ‘{t}’"
  | [] => .error s!"expected ‘{w}’"

mutual

/-- Parse at precedence level `lvl`, returning the unconsumed tokens. -/
private partial def pLevel (lvl : Nat) (ts : List Tok) : PRes :=
  match lvl with
  | 4 =>
      match ts with
      | .neg :: rest => (pLevel 4 rest).map (fun p => (Expr.neg p.1, p.2))
      | _ => pLevel 5 ts
  | 8 =>
      match ts with
      -- `if … fi` brackets itself, so each of its three places takes a whole
      -- expression and none of them needs parentheses.
      | .ident "if" :: rest => do
          let (c, r) ← pLevel 0 rest
          let r ← expectWord "then" r
          let (x, r) ← pLevel 0 r
          let r ← expectWord "else" r
          let (y, r) ← pLevel 0 r
          let r ← expectWord "fi" r
          .ok (Expr.cond c x y, r)
      | .ident n :: rest => .ok (Expr.var n, rest)
      | .num n :: rest => .ok (Expr.num n, rest)
      | .top :: rest => .ok (Expr.top, rest)
      | .bot :: rest => .ok (Expr.bot, rest)
      | .lpar :: rest => do
          let (e, r) ← pLevel 0 rest
          match r with
          | .rpar :: r' => .ok (e, r')
          | t :: _ => .error s!"expected ‘)’ but found ‘{t}’"
          | [] => .error "expected ‘)’"
      | t :: _ => .error s!"expected an operand but found ‘{t}’"
      | [] => .error "expected an operand"
  | l => do
      let (e, r) ← pLevel (l + 1) ts
      pChain l (l == 0) (opsAt l) e r

/-- Continue a left-associative chain at level `lvl`; `big` says whether the
level's operators are the large ones. -/
private partial def pChain (lvl : Nat) (big : Bool) (ops : List BinOp)
    (acc : Expr) (ts : List Tok) : PRes :=
  match ts with
  | .op o :: rest =>
      if !big && ops.contains o then do
        let (e, r) ← pLevel (lvl + 1) rest
        pChain lvl big ops (Expr.bin o acc e) r
      else .ok (acc, ts)
  | .bigOp o :: rest =>
      if big && ops.contains o then do
        let (e, r) ← pLevel (lvl + 1) rest
        pChain lvl big ops (Expr.bin o acc e) r
      else .ok (acc, ts)
  | _ => .ok (acc, ts)

end

/-- Parse a whole expression from tokens, insisting that every token is
consumed. -/
def exprOfToks (ts : List Tok) : Except String Expr := do
  if ts.isEmpty then throw "empty expression"
  let (e, rest) ← pLevel 0 ts
  match rest with
  | [] => .ok e
  | t :: _ => .error s!"unexpected ‘{t}’ after the expression"

/-- Parse a whole expression. -/
def expr (s : String) : Except String Expr := do
  exprOfToks (← tokenize s)

end Parser
end Netty
