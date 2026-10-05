import Netty.Law

/-!
# Arithmetic and binary algebra as rules

Two hints a calculation uses again and again are not laws of a list but
*decisions*: `arithmetic` (two number expressions are equal as polynomials, two
comparisons say the same thing, a comparison of numerals is true or false) and
`binary algebra` (two boolean expressions agree under every assignment). The
kernel checks them by computation:

* a number expression is normalized to a polynomial with integer coefficients
  (`toPoly`), and two expressions are equal when their polynomials are;
* a comparison is normalized to `0 ≤ p`, `p = 0` or `¬(p = 0)` over the
  integers (`a > b` is `0 ≤ a − b − 1`), and two comparisons say the same thing
  when their kinds agree and their polynomials are equal — or, for `=` and `⧧`,
  one is the negation of the other;
* a boolean expression of at most eight identifiers is decided by its truth
  table, as `Law.isTautology` decides a law.

A step is checked by finding where the two lines differ (`diffs`): at the
smallest places where they differ, each pair must be one of the above. So a step
may simplify several places at once, as the book's "arithmetic" steps do, and
each place is a certificate of its own.

The Lean twin of `arithmetic` is a theorem, not automation: `Netty.Calc.ring_eq`,
which follows from Lean's own verified normalizer
(`Lean.Grind.CommRing.Expr.denote_toPoly`) — the step is proved by reflection,
the two sides normalizing to the same polynomial by computation. The twin of
`binary algebra` is the truth table itself, case by case.
-/

namespace Netty

/-- Put `h` where the hole `□` is. -/
def Expr.replaceHole (c h : Expr) : Expr :=
  match c with
  | .mvar n => if n == "□" then h else .mvar n
  | .neg a => .neg (a.replaceHole h)
  | .bin o l r => .bin o (l.replaceHole h) (r.replaceHole h)
  | .cond x y z => .cond (x.replaceHole h) (y.replaceHole h) (z.replaceHole h)
  | .quant k ids d b => .quant k ids (d.replaceHole h) (b.replaceHole h)
  | e => e

namespace Arith

/-- A monomial: the identifiers multiplied, sorted. -/
abbrev Mono := List String

/-- A polynomial: monomials with nonzero coefficients, sorted, each once. -/
abbrev Poly := List (Mono × Int)

/-- Insert into a sorted list of strings. -/
def insertStr (s : String) : List String → List String
  | [] => [s]
  | t :: ts => if s ≤ t then s :: t :: ts else t :: insertStr s ts

/-- The product of two monomials. -/
def monoMul (a b : Mono) : Mono := a.foldl (fun acc s => insertStr s acc) b

/-- Whether one monomial comes before another. -/
def monoLt (a b : Mono) : Bool :=
  if a.length != b.length then a.length < b.length
  else (String.intercalate "*" a) < (String.intercalate "*" b)

/-- Add a term to a polynomial. -/
def addTerm (t : Mono × Int) : Poly → Poly
  | [] => if t.2 == 0 then [] else [t]
  | (m, c) :: rest =>
      if m == t.1 then (if c + t.2 == 0 then rest else (m, c + t.2) :: rest)
      else if monoLt t.1 m then (if t.2 == 0 then (m, c) :: rest else t :: (m, c) :: rest)
      else (m, c) :: addTerm t rest

/-- The sum of two polynomials. -/
def add (p q : Poly) : Poly := q.foldl (fun acc t => addTerm t acc) p

/-- A polynomial times an integer. -/
def scale (k : Int) (p : Poly) : Poly := p.foldl (fun acc (m, c) => addTerm (m, k * c) acc) []

/-- The product of two polynomials. -/
def mul (p q : Poly) : Poly :=
  p.foldl (fun acc (m, c) => q.foldl (fun acc' (n, d) => addTerm (monoMul m n, c * d) acc') acc) []

/-- A number expression as a polynomial, when it is one. -/
def toPoly : Expr → Option Poly
  | .num n => some (addTerm ([], n) [])
  | .var x => some [([x], 1)]
  | .bin .add a b => do return add (← toPoly a) (← toPoly b)
  | .bin .sub a b => do return add (← toPoly a) (scale (-1) (← toPoly b))
  | .bin .mul a b => do return mul (← toPoly a) (← toPoly b)
  | _ => none

/-- Whether an expression is visibly a number: a numeral or an arithmetic
operator at its top. -/
def isNumberish : Expr → Bool
  | .num _ => true
  | .bin .add _ _ | .bin .sub _ _ | .bin .mul _ _ => true
  | _ => false

/-- The normal form of a comparison of numbers: its kind (`ge`, `eq`, `ne`) and
the polynomial `p` it says is `≥ 0`, `= 0` or `≠ 0`, together with the two
sides of the comparison and how many to subtract (`1` for a strict one), which
is what the Lean proof needs to rebuild the same normal form. -/
structure Cmp where
  kind : String
  poly : Poly
  /-- The expression whose polynomial `poly` is: `big − small − k`. -/
  big : Expr
  small : Expr
  k : Int
  deriving Repr, Inhabited

/-- A comparison of numbers in normal form. -/
def cmp? : Expr → Option Cmp
  | .bin o a b => do
      let pa ← toPoly a
      let pb ← toPoly b
      let d := add pa (scale (-1) pb)
      let e := add pb (scale (-1) pa)
      match o with
      | .ge => some ⟨"ge", d, a, b, 0⟩
      | .le => some ⟨"ge", e, b, a, 0⟩
      | .gt => some ⟨"ge", add d (addTerm ([], -1) []), a, b, 1⟩
      | .lt => some ⟨"ge", add e (addTerm ([], -1) []), b, a, 1⟩
      | .eq => if isNumberish a || isNumberish b then some ⟨"eq", d, a, b, 0⟩ else none
      | .ne => if isNumberish a || isNumberish b then some ⟨"ne", d, a, b, 0⟩ else none
      | _ => none
  | _ => none

/-- Which of the decisions shows that `s` may be written `t`. -/
inductive How
  /-- Equal polynomials. -/ | ring
  /-- Comparisons with the same normal form; `neg` when one polynomial is the
  other's negation (`=` and `⧧` only). -/ | cmp (neg : Bool)
  /-- A comparison of numerals, and its value. -/ | ground (v : Bool)
  /-- The same truth table. -/ | taut
  deriving Repr, Inhabited, BEq

/-- Whether arithmetic shows `s` equal to `t`, and how. -/
def arith (s t : Expr) : Option How :=
  -- Two number expressions.
  if (isNumberish s || isNumberish t) && (toPoly s).isSome && toPoly s == toPoly t then
    some .ring
  else match cmp? s, cmp? t with
  | some a, some b =>
      if a.kind == b.kind && a.poly == b.poly then some (.cmp false)
      else if a.kind == b.kind && (a.kind == "eq" || a.kind == "ne") && a.poly == scale (-1) b.poly
      then some (.cmp true)
      else none
  | some a, none =>
      -- A comparison of numerals is ⊤ or ⊥.
      if a.poly.all (·.1.isEmpty) then
        let c := (a.poly.head?.map (·.2)).getD 0
        let v := match a.kind with
          | "ge" => decide (0 ≤ c)
          | "eq" => c == 0
          | _ => c != 0
        if (v && t == .top) || (!v && t == .bot) then some (.ground v) else none
      else none
  | _, _ => none

/-- Whether `s` and `t` have the same truth table. -/
def taut (s t : Expr) : Bool :=
  Law.isTautology { stmt := .bin .eq s t }

/-- The places where two lines differ, smallest first: each a context (the
line with the hole `□`, earlier places already rewritten), what stands there,
and what replaces it — when every one of them is shown by `ok`. Descends while
the two lines share their outermost form, and takes a whole subexpression as
one place only when it cannot descend. -/
partial def diffs (ok : Expr → Expr → Bool) (a b : Expr) : Option (List (Expr × Expr × Expr)) :=
  if a == b then some [] else
  let here := if ok a b then some [(Expr.mvar "□", a, b)] else none
  let down : Option (List (Expr × Expr × Expr)) := match a, b with
    | .bin o l r, .bin o' l' r' =>
        if o != o' then none else do
          let dl ← diffs ok l l'
          let dr ← diffs ok r r'
          return dl.map (fun (c, s, t) => (Expr.bin o c r, s, t)) ++
            dr.map (fun (c, s, t) => (Expr.bin o l' c, s, t))
    | .neg x, .neg y => do
        return (← diffs ok x y).map fun (c, s, t) => (Expr.neg c, s, t)
    | .cond c x y, .cond c' x' y' => do
        let dc ← diffs ok c c'
        let dx ← diffs ok x x'
        let dy ← diffs ok y y'
        return dc.map (fun (k, s, t) => (Expr.cond k x y, s, t)) ++
          dx.map (fun (k, s, t) => (Expr.cond c' k y, s, t)) ++
          dy.map (fun (k, s, t) => (Expr.cond c' x' k, s, t))
    | .quant q ids d bd, .quant q' ids' d' bd' =>
        if q != q' || ids != ids' then none else do
          let dd ← diffs ok d d'
          let db ← diffs ok bd bd'
          return dd.map (fun (k, s, t) => (Expr.quant q ids k bd, s, t)) ++
            db.map (fun (k, s, t) => (Expr.quant q ids d' k, s, t))
    | _, _ => none
  match down with
  | some ds => some ds
  | none => here

end Arith
end Netty
