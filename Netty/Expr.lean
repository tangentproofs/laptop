/-!
# Netty expressions

The formulas that appear on the lines of a Netty proof. Netty is a prover's
assistant for calculational proofs (Hehner, Will, Naiman, Kordalewski; see
`Netty_document.pdf`), so the expression language here is the boolean and
number fragment of the aPToP grammar in that document: enough to state the
Binary laws of aPToP §11.3.1 and to carry the direction machinery that a
calculation needs. Bunches, strings, lists, functions, quantifiers, programs
and channels are the later growth of the surface language and are absent.

Three things live here besides the syntax tree itself.

* **Positions.** Each operand of each operator is in a *positive*, *neutral*
  or *negative* position (the table in the document's Zoom section). Zooming in
  to an operand turns the proof direction around exactly when the position is
  negative, and flattens it to `=` when the position is neutral.
* **Types.** A line has a type — `boolean` or `number` here — because the three
  proof directions are spelled `⇒ = ⇐` for booleans and `≤ = ≥` for numbers.
  The inference is deliberately crude: an operator fixes the type of its
  result and usually of its operands, and a bare identifier inherits the type
  of the context it sits in.
* **Associativity, symmetry and units.** The document says that clicking any
  operand of `a+b+c` zooms in to it, with no need of associative laws. So the
  *main operands* of an expression whose main operator is associative are the
  flattened list, and a contiguous run of two or more of them — a *segment*,
  `b+c` inside `a+b+c` — is a place of its own that a law can be applied to
  (`segments`, `segmentExpr`, `replaceSegment`). `BinOp.comm` and
  `BinOp.identity` name the operators the document declares symmetric and the
  units it names for them; they are what `Netty.Expr.matchFuel` reads a line
  modulo, and they change nothing about how a line is drawn or zoomed in to.
-/

namespace Netty

/-- A binary operator of the boolean and number fragment. -/
inductive BinOp
  /-- `a ∧ b`. -/            | and
  /-- `a ∨ b`. -/            | or
  /-- `a ⇒ b`. -/            | imp
  /-- `a ⇐ b`. -/            | rimp
  /-- `a = b`. -/            | eq
  /-- `a ⧧ b`. -/            | ne
  /-- `a < b`. -/            | lt
  /-- `a > b`. -/            | gt
  /-- `a ≤ b`. -/            | le
  /-- `a ≥ b`. -/            | ge
  /-- `a + b`. -/            | add
  /-- `a - b`. -/            | sub
  /-- `a × b`. -/            | mul
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- The type of a line of a proof. Netty allows lines of any type; the kernel
so far knows the two the document's own examples use. -/
inductive Ty
  /-- Directions `⇒ = ⇐`. -/ | boolean
  /-- Directions `≤ = ≥`. -/ | number
  deriving Repr, DecidableEq, Inhabited

/-- Whether an operand occurrence is monotonic (`positive`), antitonic
(`negative`) or neither (`neutral`) in its operator. -/
inductive Pos
  | positive | neutral | negative
  deriving Repr, DecidableEq, Inhabited

/-- An expression: a formula on a line of a proof, or the statement of a law.

`mvar` is a *law variable*: the universally quantified identifier of a law,
which unifies with an arbitrary expression. `var` is an ordinary identifier,
which unifies only with itself. Keeping them apart means a law about `a` and a
proof about `a` can never capture one another. -/
inductive Expr
  /-- An identifier of the formula being proved. -/  | var (name : String)
  /-- A number literal. -/                           | num (n : Nat)
  /-- A universally quantified variable of a law. -/ | mvar (name : String)
  /-- `⊤`, the theorem. -/                           | top
  /-- `⊥`, the antitheorem. -/                       | bot
  /-- `¬a`. -/                                       | neg (a : Expr)
  /-- `l op r`. -/                                   | bin (op : BinOp) (l r : Expr)
  deriving Repr, DecidableEq, Inhabited

namespace BinOp

/-- How the operator is written. -/
def symbol : BinOp → String
  | and => "∧" | or => "∨" | imp => "⇒" | rimp => "⇐"
  | eq => "=" | ne => "⧧" | lt => "<" | gt => ">" | le => "≤" | ge => "≥"
  | add => "+" | sub => "-" | mul => "×"

/-- Binding power, following the aPToP grammar of the Netty document: the
larger the number, the *weaker* the operator binds. Note that `¬` (8) sits
between `∧` (9) and `=` (7), so `¬ a = b` is `¬(a = b)`. -/
def prec : BinOp → Nat
  | imp | rimp => 11
  | or => 10
  | and => 9
  | eq | ne | lt | gt | le | ge => 7
  | add | sub => 4
  | mul => 3

/-- The operators the document declares associative, so that an association
`a ∧ b ∧ c` has three main operands rather than two. -/
def assoc : BinOp → Bool
  | and | or | add | mul => true
  | _ => false

/-- The operators the document declares symmetric — the ones its `symmetry`
laws are about, `∧ ∨ = ⧧` at the boolean type and `+ ×` at the number type.
Matching reads a line modulo these, so a law about `a ∧ b` sees `y ∧ x`
(`Netty.Expr.matchFuel`). -/
def comm : BinOp → Bool
  | and | or | add | mul | eq | ne => true
  | _ => false

/-- The identity element of the operator, where the document names one: `⊤` for
`∧`, `⊥` for `∨`, `0` for `+` and `1` for `×`. Matching reads a line modulo
these too, so a law that mentions the unit can see a line that leaves it out,
and a law that does not can see a line that writes it.

The document also states `⊤ ⇒ a ≡ a` and `⊤ = a ≡ a`, but `⇒` and `=` are not
associations that a line is read apart into, so those stay ordinary laws rather
than something the matcher does silently. -/
def identity : BinOp → Option Expr
  | and => some .top
  | or => some .bot
  | add => some (.num 0)
  | mul => some (.num 1)
  | _ => none

/-- The type of the operator's result. -/
def resultTy : BinOp → Ty
  | add | sub | mul => .number
  | _ => .boolean

/-- The type the operator forces on its operands, when it forces one. `=` and
`⧧` accept any type, so they force none. -/
def operandTy : BinOp → Option Ty
  | and | or | imp | rimp => some .boolean
  | lt | gt | le | ge | add | sub | mul => some .number
  | eq | ne => none

/-- The position of operand `i` (`0` left, `1` right).

This is the table in the document's Zoom section. `×` is not in that table —
its operands are monotonic only for nonnegative factors — so the kernel calls
them neutral, which is always sound and merely loses some steps. -/
def posOf : BinOp → Nat → Pos
  | and, _ | or, _ | add, _ => .positive
  | imp, 0 | le, 0 | lt, 0 | sub, 1 => .negative
  | imp, _ | le, _ | lt, _ | sub, _ => .positive
  | rimp, 0 | ge, 0 | gt, 0 => .positive
  | rimp, _ | ge, _ | gt, _ => .negative
  | eq, _ | ne, _ | mul, _ => .neutral

/-- Whether the operator can appear in the left margin of a proof, that is,
whether it is one of the three directions of some type. `⧧` cannot: the three
boolean directions are `⇒ = ⇐`. -/
def isMargin : BinOp → Bool
  | eq | imp | rimp | lt | gt | le | ge => true
  | _ => false

/-- The converse relation, when there is one: `a op b` is `b op.flip a`. -/
def flip : BinOp → Option BinOp
  | eq => some eq | imp => some rimp | rimp => some imp
  | lt => some gt | gt => some lt | le => some ge | ge => some le
  | ne => some ne
  | and | or | add | sub | mul => none

end BinOp

namespace Expr

/-- Parenthesize when asked. -/
private def paren (b : Bool) (s : String) : String :=
  if b then "(" ++ s ++ ")" else s

/-- Binding power of an expression's main operator; `0` for an atom. -/
def prec : Expr → Nat
  | var _ | mvar _ | num _ | top | bot => 0
  | neg _ => 8
  | bin op _ _ => op.prec

/-- Render `e`, parenthesizing it when its main operator binds more weakly
than the context allows. All the binary operators associate to the left. -/
def renderAt : Nat → Expr → String
  | _, var n => n
  | _, mvar n => n
  | _, num n => toString n
  | _, top => "⊤"
  | _, bot => "⊥"
  | p, neg a => paren (8 > p) ("¬" ++ renderAt 8 a)
  | p, bin op l r =>
      paren (op.prec > p)
        (renderAt op.prec l ++ " " ++ op.symbol ++ " " ++ renderAt (op.prec - 1) r)

/-- Render an expression in the document's notation. -/
def render (e : Expr) : String := renderAt 99 e

instance : ToString Expr := ⟨render⟩

/-- The law variables occurring in `e`, in order of first occurrence. -/
def mvars (e : Expr) : List String :=
  go e [] |>.reverse
where
  go : Expr → List String → List String
    | mvar n, acc => if acc.contains n then acc else n :: acc
    | neg a, acc => go a acc
    | bin _ l r, acc => go r (go l acc)
    | _, acc => acc

/-- The ordinary identifiers occurring in `e`, in order of first occurrence. -/
def vars (e : Expr) : List String :=
  go e [] |>.reverse
where
  go : Expr → List String → List String
    | var n, acc => if acc.contains n then acc else n :: acc
    | neg a, acc => go a acc
    | bin _ l r, acc => go r (go l acc)
    | _, acc => acc

/-- Turn the named identifiers into law variables. Used when a law file
declares (or, by default, implies) that its identifiers are quantified. -/
def generalize (names : List String) : Expr → Expr
  | var n => if names.contains n then mvar n else var n
  | neg a => neg (generalize names a)
  | bin op l r => bin op (generalize names l) (generalize names r)
  | e => e

/-- The number of nodes in an expression.

It is what bounds the matcher in `Netty.Law`: that recursion spends one unit of
its fuel per level of the pattern, and an expression's height is at most its
size, so `size` is more fuel than a match can use. -/
def size : Expr → Nat
  | var _ | mvar _ | num _ | top | bot => 1
  | neg a => 1 + a.size
  | bin _ l r => 1 + l.size + r.size

/-- Flatten an association of `op`, so that `a ∧ b ∧ c` has three operands. -/
def flattenOp (op : BinOp) : Expr → List Expr
  | bin op' l r => if op' == op then flattenOp op l ++ flattenOp op r else [bin op' l r]
  | e => [e]

/-- Rebuild an association of `op` from its operands, to the left. -/
def rebuildOp (op : BinOp) : List Expr → Option Expr
  | [] => none
  | e :: es => some (es.foldl (fun acc x => bin op acc x) e)

/-- The *main operands* of `e`: the subexpressions a user can zoom in to.
An associative main operator contributes its whole flattened association. -/
def operands : Expr → List Expr
  | neg a => [a]
  | bin op l r => if op.assoc then flattenOp op (bin op l r) else [l, r]
  | _ => []

/-- The symbol of the main operator of `e`: what stands between its main
operands, or before the one operand of a negation. Empty for an atom. -/
def mainOp : Expr → String
  | neg _ => "¬"
  | bin op _ _ => op.symbol
  | _ => ""

/-- The main operands of `e`, each rendered with exactly the parentheses it
carries inside `e.render`, so that a display which draws them as separate
clickable pieces with `mainOp` between them reads as the whole line does.

The one departure is the one the flattening already makes: `a ∧ (b ∧ c)` has the
three main operands `a`, `b`, `c`, so it is drawn as `a ∧ b ∧ c`, without the
parentheses `render` writes. That is the document's own reading of an
associative operator, and it is why a click on `b` can zoom in. -/
def operandTexts (e : Expr) : List String :=
  match e with
  | neg a => [renderAt 8 a]
  | bin op _ _ =>
      match operands e with
      | [] => []
      | x :: xs => renderAt op.prec x :: xs.map (renderAt (op.prec - 1))
  | _ => []

/-- Replace the `i`-th main operand of `e`. This is how zooming out puts the
bottom line of a subproof back into the line it was zoomed in from. -/
def replaceOperand (e : Expr) (i : Nat) (new : Expr) : Option Expr :=
  match e with
  | neg _ => if i == 0 then some (neg new) else none
  | bin op l r =>
      if op.assoc then
        let es := flattenOp op (bin op l r)
        if i < es.length then rebuildOp op (es.set i new) else none
      else if i == 0 then some (bin op new r)
      else if i == 1 then some (bin op l new)
      else none
  | _ => none

/-- The contiguous multi-operand *segments* of `e`, as `(start, length)` pairs
into the flattened association of its main operator.

A segment is a run of two or more consecutive main operands: `y ∧ z` inside
`x ∧ y ∧ z`. The runs of length one are the main operands themselves and the run
of the whole length is `e`, so neither is listed here; an expression whose main
operator is not associative, and an association of only two operands, have no
segments at all. Ordered by where a run starts, then by how long it is. -/
def segments : Expr → List (Nat × Nat)
  | bin op l r =>
      if !op.assoc then [] else
        let n := (flattenOp op (bin op l r)).length
        (List.range n).flatMap fun start =>
          (List.range (n + 1)).filterMap fun len =>
            if 2 ≤ len && len < n && start + len ≤ n then some (start, len) else none
  | _ => []

/-- The subexpression a segment of `e` is: its `len` main operands from `start`,
rebuilt to the left as `rebuildOp` does. It is what a law is matched against at
a segment site, and what zooming in to that run of operands would put on the
first line of the subproof. -/
def segmentExpr (e : Expr) (start len : Nat) : Option Expr :=
  match e with
  | bin op l r =>
      if !op.assoc then none else
        let es := flattenOp op (bin op l r)
        if 2 ≤ len && start + len ≤ es.length then
          rebuildOp op ((es.drop start).take len)
        else none
  | _ => none

/-- Replace a segment of `e` — the `len` main operands from `start` — by the one
expression `new`, rebuilding the association to the left. This is how a law
applied to a contiguous segment writes its result back into the line, and it is
what zooming out of that run of operands would write. -/
def replaceSegment (e : Expr) (start len : Nat) (new : Expr) : Option Expr :=
  match e with
  | bin op l r =>
      if !op.assoc then none else
        let es := flattenOp op (bin op l r)
        if 2 ≤ len && start + len ≤ es.length then
          rebuildOp op (es.take start ++ new :: es.drop (start + len))
        else none
  | _ => none

/-- The position of a segment of `e`. An associative operator puts every one of
its operands in the same position, so a run of them is in that position too —
the very one `operandPos` gives for a single operand of the same association. -/
def segmentPos : Expr → Pos
  | bin op _ _ => op.posOf 0
  | _ => .neutral

/-- The type of a segment of `e`. A segment is itself an application of `e`'s
main operator, so its type is that operator's result type — which, for the
associative operators, is also the type the operator forces on its operands, so
a segment and a single operand of one association have the same type. -/
def segmentTy (e : Expr) (parent : Ty) : Ty :=
  match e with
  | bin op _ _ => op.resultTy
  | _ => parent

/-- The position of the `i`-th main operand. -/
def operandPos (e : Expr) (i : Nat) : Pos :=
  match e with
  | neg _ => .negative
  | bin op _ _ => if op.assoc then op.posOf 0 else op.posOf i
  | _ => .neutral

/-- The type of `e`, when its main operator settles it. A bare identifier
settles nothing and inherits the type of its surroundings. -/
def tyOf? : Expr → Option Ty
  | num _ => some .number
  | top | bot | neg _ => some .boolean
  | bin op _ _ => some op.resultTy
  | var _ | mvar _ => none

/-- The type of the `i`-th main operand of `e`, falling back to `parent` (the
type of the level we are zooming in from) when nothing settles it. -/
def operandTy (e : Expr) (i : Nat) (parent : Ty) : Ty :=
  match e with
  | neg _ => .boolean
  | bin op _ _ =>
      match op.operandTy with
      | some t => t
      | none =>
          let es := operands e
          match (es[i]?.bind tyOf?) with
          | some t => t
          | none => (es.findSome? tyOf?).getD parent
  | _ => parent

/-- Evaluate a boolean expression under an assignment of the law variables and
identifiers. `none` when the expression is not of boolean type or mentions an
unassigned name; used only by the law-soundness checker. -/
def evalBool (σ : List (String × Bool)) : Expr → Option Bool
  | top => some true
  | bot => some false
  | var n | mvar n => σ.lookup n
  | num _ => none
  | neg a => (evalBool σ a).map not
  | bin op l r => do
      let a ← evalBool σ l
      let b ← evalBool σ r
      match op with
      | .and => some (a && b)
      | .or => some (a || b)
      | .imp => some (!a || b)
      | .rimp => some (!b || a)
      | .eq => some (a == b)
      | .ne => some (a != b)
      | _ => none

/-- Evaluate a number expression under an assignment of integers to its law
variables and identifiers; `none` when it is not a number expression. This is
for *checking a law list*, not for calculating: nothing in the suggestion engine
does arithmetic. -/
def evalInt (σ : List (String × Int)) : Expr → Option Int
  | num n => some (n : Int)
  | var n | mvar n => σ.lookup n
  | bin .add l r => do return (← evalInt σ l) + (← evalInt σ r)
  | bin .sub l r => do return (← evalInt σ l) - (← evalInt σ r)
  | bin .mul l r => do return (← evalInt σ l) * (← evalInt σ r)
  | _ => none

/-- Evaluate a binary expression whose atoms may be comparisons of numbers, under
an assignment of integers. A `=` or `⧧` whose sides are numbers is read as the
comparison and otherwise as the connective, which is what the two spellings of
those operators mean in the book. -/
def evalProp (σ : List (String × Int)) : Expr → Option Bool
  | top => some true
  | bot => some false
  | neg a => (evalProp σ a).map not
  | bin o l r =>
      match o with
      | .lt => do return decide ((← evalInt σ l) < (← evalInt σ r))
      | .gt => do return decide ((← evalInt σ r) < (← evalInt σ l))
      | .le => do return decide ((← evalInt σ l) ≤ (← evalInt σ r))
      | .ge => do return decide ((← evalInt σ r) ≤ (← evalInt σ l))
      | .and => do return (← evalProp σ l) && (← evalProp σ r)
      | .or => do return (← evalProp σ l) || (← evalProp σ r)
      | .imp => do return !(← evalProp σ l) || (← evalProp σ r)
      | .rimp => do return !(← evalProp σ r) || (← evalProp σ l)
      | .eq =>
          match evalInt σ l, evalInt σ r with
          | some a, some b => some (a == b)
          | _, _ => do return (← evalProp σ l) == (← evalProp σ r)
      | .ne =>
          match evalInt σ l, evalInt σ r with
          | some a, some b => some (a != b)
          | _, _ => do return (← evalProp σ l) != (← evalProp σ r)
      | _ => none
  | _ => none

end Expr
end Netty
