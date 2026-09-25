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
rel    := arith (('=' | '⧧' | '<' | '>' | '≤' | '≥' | ':') arith)*
arith  := term (('+' | '-') term)*
term   := atom ('×' atom)*
atom   := identifier | number | '⊤' | '⊥' | '(' expr ')'
        | 'if' expr 'then' expr 'else' expr 'fi'
        | ('∀' | '∃') identifiers ':' expr '·' expr
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

`T` and `F` are therefore reserved and cannot be used as identifiers, and so are
`forall` and `exists`, the ASCII spellings of `∀` and `∃`.

`if … then … else … fi` is the document's conditional expression. It closes
itself, so it needs no parentheses and takes whole expressions in all three
places: `if b then x else y fi ∧ z` is the conditional and-ed with `z`. The four
words are reserved in expression position for the same reason `T` and `F` are: an
identifier spelled `if`, `then`, `else` or `fi` is no longer readable.

`∀ids: d· b` and `∃ids: d· b` are the document's quantified expressions, written
`quantifier identifiers : expression · expression` in its grammar. Two things
follow from where that production sits.

* The domain is closed by the `·`, but *nothing closes the body*: a quantifier is
  the weakest thing in the grammar and its body runs to the end of the
  expression. So `∀x: nat· x ≥ 0 ∧ x ≤ 9` quantifies the conjunction, and
  `(∀x: nat· x ≥ 0) ∧ p` needs its brackets. `Expr.renderAt` writes exactly those
  brackets back.
* The parser reads a quantifier wherever an operand may begin, which is a shade
  more permissive than the document's grammar — that grammar admits one only at
  the outermost level, so `p ∧ ∀x: nat· x ≥ 0` is not a sentence of it. What is
  read is the same expression either way, and it is written back bracketed.

The document has no abbreviated quantifier that leaves the domain out, so neither
has this, and `∀`/`∃` without a `:` is an error rather than a second form. The
document also says of a scope that "the domain `d` cannot mention `v`", which is
refused here (`Parser.quantifier`) rather than read and then quietly misused.

`:` is `exp7` in the document's grammar — the level of `=` and the comparisons —
and it is membership: `x: nat` says `x` is one of the bunch `nat`. It is here
because zooming in to the body of a quantifier gains the context `v: d`. None of
the rest of the bunch notation is.
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
  /-- `∃`. -/                               | exis
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
  | lpar => "(" | rpar => ")" | comma => "," | dot => "·"
  | univ => "∀" | exis => "∃"

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
    ("·".toList, .dot), (".".toList, .dot), ("∀".toList, .univ), ("∃".toList, .exis),
    (":".toList, .op .mem) ]

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
          else if name == "exists" then Tok.exis
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
  | 5 => [.eq, .ne, .lt, .gt, .le, .ge, .mem]
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

/-- Read the identifiers a quantifier binds: names separated by `,` and closed
by the `:` that the domain follows. -/
private def boundIds : List Tok → List String → Except String (List String × List Tok)
  | .op .mem :: rest, acc =>
      if acc.isEmpty then .error "a quantifier binds at least one identifier"
      else .ok (acc.reverse, rest)
  | .ident n :: rest, acc =>
      if acc.contains n then .error s!"‘{n}’ is bound twice by the one quantifier"
      else boundIds rest (n :: acc)
  | .comma :: rest, acc => boundIds rest acc
  | .dot :: _, _ =>
      .error "a quantifier needs a domain: write ‘∀x: d· b’, not ‘∀x· b’"
  | t :: _, _ => .error s!"unexpected ‘{t}’ among the identifiers a quantifier binds"
  | [], _ => .error "expected ‘:’ and a domain after the identifiers a quantifier binds"

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
      -- `∀ids: d· b`. The `·` closes the domain; the body is parsed at the
      -- weakest level and so runs to the end of the expression, which is where
      -- the document's grammar puts a quantifier.
      | .univ :: rest => quantifier .all rest
      | .exis :: rest => quantifier .ex rest
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

/-- Parse a quantified expression, the `∀` or `∃` already consumed.

The document: "The domain `d` cannot mention `v`." A domain that mentions what the
quantifier binds is refused here, so nothing downstream has to wonder what it
would have meant. -/
private partial def quantifier (k : Quant) (ts : List Tok) : PRes := do
  let (ids, r) ← boundIds ts []
  let (d, r) ← pLevel 0 r
  let clash := d.vars.filter ids.contains
  if !clash.isEmpty then
    .error s!"the domain of ‘{k.symbol}{String.intercalate ", " ids}’ mentions \
      {String.intercalate ", " clash}, which it binds"
  match r with
  | .dot :: r' => do
      let (b, r') ← pLevel 0 r'
      .ok (Expr.quant k ids d b, r')
  | t :: _ => .error s!"expected ‘·’ after the domain but found ‘{t}’"
  | [] => .error "expected ‘·’ after the domain"

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
