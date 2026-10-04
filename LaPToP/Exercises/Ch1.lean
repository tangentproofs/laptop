import LaPToP.Exercises.Basic
import LaPToP.BasicTheories.Binary
import LaPToP.BasicTheories.NumberLaws
import Mathlib.Tactic
import Mathlib.Basic.Real.Sign

/-!
# Exercises — Basic Theories (aPToP §10.1)

Binary expressions are `Bool`, as in `LaPToP.BasicTheories.Binary`: `⇒` is
`imp`, `⇐` is `rimp`, `=` is `==`, `⧧` is `!=`, `if then else` is `bif`. A law
stated as a theorem of binary theory is `… = true`; every one is checked case by
case (`decide`). The book writes its large, lowest-precedence `=` and `⇒` with
space around them; the formulas below are bracketed accordingly.

Exercises that ask to design notation or to explain in words (4's
succinctness, 11(e)–(f), 13, 15(b)–(d), 17, 19's discussion, 20, 25, 29(c)–(f),
32–34, 37, 39, 40) have no single formal statement; where part of one has, that
part is here. The list is kept in `MISSING.md` §5.
-/

namespace LaPToP.Exercises.Ch1

open LaPToP.BasicTheories.Binary

/-! ### Exercise 4: value tables as axioms -/

/-- **Exercise 4**: each operator's value table is the pair of axioms with one
operand a variable, and these axioms determine the operator. -/
theorem exercise_4 :
    (∀ x : Bool, (true && x) = x ∧ (false && x) = false) ∧
    (∀ x : Bool, (true || x) = true ∧ (false || x) = x) ∧
    (∀ x : Bool, imp true x = x ∧ imp false x = true) ∧
    (∀ x : Bool, (true == x) = x ∧ (false == x) = !x) ∧
    (∀ f : Bool → Bool → Bool, (∀ x, f true x = x) → (∀ x, f false x = false) →
      ∀ a b, f a b = (a && b)) := by
  refine ⟨by decide, by decide, by decide, by decide, fun f h₁ h₂ a b => ?_⟩
  cases a
  · rw [h₂]; rfl
  · rw [h₁]; rfl

/-! ### Exercise 5: simplify -/

/-- **Exercise 5**. -/
theorem exercise_5 (x : Bool) :
    (x && !x) = false ∧ (x || !x) = true ∧ imp x (!x) = !x ∧ rimp x (!x) = x ∧
      (x == !x) = false ∧ (x != !x) = true := by
  cases x <;> decide

/-! ### Exercise 6: laws of binary theory -/

/-- **Exercise 6**, parts (a)–(w). -/
theorem exercise_6 (a b c d e p x : Bool) :
    imp (a && b) (a || b) = true ∧                                              -- (a)
    ((a && b) || (b && c) || (c && a)) = ((a || b) && (b || c) && (c || a)) ∧   -- (b)
    imp (!a) (imp a b) = true ∧                                                 -- (c)
    (a == imp b a) = (a || b) ∧                                                 -- (d)
    (a == imp a b) = (a && b) ∧                                                 -- (e)
    imp (imp a c && imp b (!c)) (!(a && b)) = true ∧                            -- (f)
    imp (a && !b) (a || b) = true ∧                                             -- (g)
    imp (imp a b && imp c d && (a || c)) (b || d) = true ∧                      -- (h)
    imp (a && !a) b = true ∧                                                    -- (i)
    (imp a b || imp b a) = true ∧                                               -- (j)
    (!(a && !(a || b))) = true ∧                                                -- (k)
    ((imp (!a) (!b) && (a != b)) || imp (a && c) (b && c)) = true ∧             -- (l)
    imp (imp a (!a)) (!a) = true ∧                                              -- (m)
    (imp a b && imp (!a) b) = b ∧                                               -- (n)
    imp (imp a b) a = a ∧                                                       -- (o)
    ((a == b) || (a == c) || (b == c)) = true ∧                                 -- (p)
    ((a && b) || (a && !b)) = a ∧                                               -- (q)
    imp a (imp b a) = true ∧                                                    -- (r)
    (imp a (a && b) = imp a b ∧ imp a b = imp (a || b) b) ∧                     -- (s)
    (imp a (a && b) || imp b (a && b)) = true ∧                                 -- (t)
    (imp a (p == x) && imp (!a) p) = (p == (x || !a)) ∧                         -- (u)
    (imp a (imp b (!a)) || imp (b && c) (a && c)) = true ∧                      -- (v)
    imp ((a == (b && c)) && (d == (!b && !c)) && (e == ((a || d) == c))) (e == b) = true := by  -- (w)
  revert a b c d e p x; decide

/-! ### Exercise 7: laws of `if then else` -/

/-- **Exercise 7**, parts (a)–(h), the branches `P`, `Q`, `R` of any type. -/
theorem exercise_7 {α : Type*} (a b c d : Bool) (P Q R : α) :
    (bif a then a else !a) = true ∧                                                  -- (a)
    (bif b then c else !c) = (bif c then b else !b) ∧                                -- (b)
    (bif b && c then P else Q) = (bif b then (bif c then P else Q) else Q) ∧          -- (c)
    (bif b || c then P else Q) = (bif b then P else bif c then P else Q) ∧            -- (d)
    (bif b then P else bif b then Q else R) = (bif b then P else R) ∧                 -- (e)
    (bif (bif b then c else d) then P else Q) =
      (bif b then (bif c then P else Q) else bif d then P else Q) ∧                   -- (f)
    (bif b then (bif c then P else R) else bif c then Q else R) =
      (bif c then (bif b then P else Q) else R) ∧                                     -- (g)
    (bif b then (bif c then P else R) else bif d then Q else R) =
      (bif (bif b then c else d) then (bif b then P else Q) else R) := by             -- (h)
  cases a <;> cases b <;> cases c <;> cases d <;> simp

/-! ### Exercise 8: `if then else` with its condition once -/

/-- **Exercise 8**: `if a then b else c = (¬c ⇒ a ⇒ b)`, the `⇒` continuing,
that is, `(¬c ⇒ a) ∧ (a ⇒ b)`: `a` written once. -/
theorem exercise_8 (a b c : Bool) : (bif a then b else c) = (imp (!c) a && imp a b) := by
  revert a b c; decide

/-! ### Exercise 9: expressions of `⊤ ⊥ = ⧧` -/

/-- A fully bracketed expression of `⊤ ⊥ = ⧧`. -/
inductive BE
  | top | bot
  | eq (x y : BE)
  | ne (x y : BE)

/-- Its value. -/
def BE.eval : BE → Bool
  | top => true
  | bot => false
  | eq x y => x.eval == y.eval
  | ne x y => x.eval != y.eval

/-- How many `⊥`s and `⧧`s it has. -/
def BE.odd : BE → ℕ
  | top => 0
  | bot => 1
  | eq x y => x.odd + y.odd
  | ne x y => x.odd + y.odd + 1

/-- Its value is whether it has an even number of `⊥`s and `⧧`s. -/
theorem BE.eval_eq : ∀ x : BE, x.eval = decide (x.odd % 2 = 0)
  | top => rfl
  | bot => rfl
  | eq x y => by
    simp only [eval, odd, BE.eval_eq x, BE.eval_eq y]
    rcases Nat.mod_two_eq_zero_or_one x.odd with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.odd with hy | hy <;> simp [hx, hy, Nat.add_mod]
  | ne x y => by
    simp only [eval, odd, BE.eval_eq x, BE.eval_eq y]
    rcases Nat.mod_two_eq_zero_or_one x.odd with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.odd with hy | hy <;> simp [hx, hy, Nat.add_mod]

/-- **Exercise 9**: (a) a rearrangement, with as many of each symbol, has the
same value; (b) so does an expression with a number of `⊥`s and `⧧`s of the same
parity, which an even number of the substitutions `⊤↔⊥`, `=↔⧧` gives (each
substitution changes that number by one). -/
theorem exercise_9 (x y : BE) (h : x.odd % 2 = y.odd % 2) : x.eval = y.eval := by
  rw [BE.eval_eq, BE.eval_eq, h]

/-! ### Exercise 10: exactly one of three -/

/-- **Exercise 10**: `(a ⧧ b ⧧ c) ∧ ¬(a ∧ b ∧ c)` says that exactly one of `a`,
`b`, `c` is true. -/
theorem exercise_10 (a b c : Bool) :
    (((a != b) != c) && !(a && b && c)) = decide ([a, b, c].count true = 1) := by
  revert a b c; decide

/-! ### Exercise 11: duals -/

/-- The dual of a one-operand operator. -/
def dual₁ (f : Bool → Bool) : Bool → Bool := fun a => !f (!a)

/-- The dual of a two-operand operator. -/
def dual₂ (f : Bool → Bool → Bool) : Bool → Bool → Bool := fun a b => !f (!a) (!b)

/-- The two-operand operator with value table `t` (`t` read from `⊤⊤` to `⊥⊥`). -/
def op₂ (t : Fin 16) : Bool → Bool → Bool := fun a b =>
  (t.val / 2 ^ ((if a then 0 else 2) + (if b then 0 else 1))) % 2 == 1

/-- Whether two value tables are of the same operator. -/
def sameOp (f g : Bool → Bool → Bool) : Bool :=
  [true, false].all fun a => [true, false].all fun b => f a b == g a b

/-- **Exercise 11**: (a) of the 4 one-operand operators, the constants are
duals, and identity and negation are their own; (b) of the 16 two-operand
operators, 4 are their own duals and the other 12 make 6 pairs; (c) the dual of
`if a then b else c` is `if a then c else b`; (d) the dual of an expression
without variables is its negation. -/
theorem exercise_11 :
    dual₁ (fun _ => true) = (fun _ => false) ∧ dual₁ id = id ∧ dual₁ (!·) = (!·) ∧
    ((List.finRange 16).filter fun t => sameOp (dual₂ (op₂ t)) (op₂ t)).length = 4 ∧
    (∀ t : Fin 16, sameOp (dual₂ (dual₂ (op₂ t))) (op₂ t)) ∧
    dual₂ (· && ·) = (· || ·) ∧ dual₂ imp = (fun a b => !a && b) ∧
    (∀ a b c : Bool, (!(bif !a then !b else !c)) = bif a then c else b) := by
  refine ⟨?_, ?_, ?_, by decide, by decide, ?_, ?_, by decide⟩
  · funext a; cases a <;> rfl
  · funext a; cases a <;> rfl
  · funext a; cases a <;> rfl
  · funext a b; cases a <;> cases b <;> rfl
  · funext a b; cases a <;> cases b <;> rfl

/-- A binary expression without variables. -/
inductive CE
  | top | bot
  | not (x : CE)
  | and (x y : CE)
  | or (x y : CE)

/-- Its value. -/
def CE.eval : CE → Bool
  | top => true
  | bot => false
  | not x => !x.eval
  | and x y => x.eval && y.eval
  | or x y => x.eval || y.eval

/-- Its dual: each operator replaced by its dual. -/
def CE.dual : CE → CE
  | top => bot
  | bot => top
  | not x => not x.dual
  | and x y => or x.dual y.dual
  | or x y => and x.dual y.dual

/-- **Exercise 11(d)**: the dual of an expression without variables is its
negation, so the dual of a theorem is an antitheorem, and vice versa. -/
theorem exercise_11_d : ∀ x : CE, x.dual.eval = !x.eval
  | .top => rfl
  | .bot => rfl
  | .not x => by simp [CE.dual, CE.eval, exercise_11_d x]
  | .and x y => by simp [CE.dual, CE.eval, exercise_11_d x, exercise_11_d y]
  | .or x y => by simp [CE.dual, CE.eval, exercise_11_d x, exercise_11_d y]

/-! ### Exercise 12: drinking and driving -/

/-- **Exercise 12**: (a) `¬(dr ∧ dv)`, (b) `dr ⇒ ¬dv`, (c) `dv ⇒ ¬dr`,
(e) `¬dr ∨ ¬dv` are all the same; (d) `¬dr ∧ ¬dv` differs from them. -/
theorem exercise_12 :
    (∀ dr dv : Bool, (!(dr && dv)) = imp dr (!dv) ∧ imp dr (!dv) = imp dv (!dr) ∧
      imp dv (!dr) = (!dr || !dv)) ∧
    ∃ dr dv : Bool, (!(dr && dv)) ≠ (!dr && !dv) := by
  exact ⟨by decide, true, false, by decide⟩

/-! ### Exercise 14: operators from a few symbols -/

/-- **Exercise 14**, with `¬ ∧` (i), `¬ ∨` (ii), `¬ ⇒` (iii), `⧧ ⇒` (iv), and
`¬ if then else` (v): each of `⊤ ⊥ ¬a a∧b a∨b a=b a⧧b a⇒b`. -/
theorem exercise_14 (a b : Bool) :
    -- (i)
    (true = !(a && !a) ∧ false = (a && !a) ∧ (a || b) = !(!a && !b) ∧
      (a == b) = (!(a && !b) && !(!a && b)) ∧ (a != b) = (!(a && b) && !(!a && !b)) ∧
      imp a b = !(a && !b)) ∧
    -- (ii)
    (true = (a || !a) ∧ false = !(a || !a) ∧ (a && b) = !(!a || !b) ∧
      (a == b) = (!(!a || !b) || !(a || b)) ∧ (a != b) = (!(a || !b) || !(!a || b)) ∧
      imp a b = (!a || b)) ∧
    -- (iii)
    (true = imp a a ∧ false = !(imp a a) ∧ (a && b) = !(imp a (!b)) ∧ (a || b) = imp (!a) b ∧
      (a == b) = !(imp (imp a b) (!(imp b a))) ∧ (a != b) = imp (imp a b) (!(imp b a))) ∧
    -- (iv), `¬x` written `x ⧧ (a ⇒ a)`
    (true = imp a a ∧ false = (a != a) ∧ (!a) = (a != imp a a) ∧
      (a && b) = (imp a (b != imp a a) != imp a a) ∧ (a || b) = imp (a != imp a a) b ∧
      (a == b) = ((a != b) != imp a a) ∧ (a != b) = (a != b)) ∧
    -- (v)
    (true = (bif a then a else !a) ∧ false = !(bif a then a else !a) ∧
      (a && b) = (bif a then b else a) ∧ (a || b) = (bif a then a else b) ∧
      (a == b) = (bif a then b else !b) ∧ (a != b) = (bif a then !b else b) ∧
      imp a b = (bif a then b else !a)) := by
  revert a b; decide

/-! ### Exercise 15: binary decision diagrams -/

/-- A BDD, over variables numbered. -/
inductive BDD
  | top | bot
  | ite (v : ℕ) (t e : BDD)

/-- Its value, given the variables'. -/
def BDD.eval (σ : ℕ → Bool) : BDD → Bool
  | top => true
  | bot => false
  | ite v t e => bif σ v then t.eval σ else e.eval σ

/-- **Exercise 15(a)**: `¬a`, `a∧b`, `a∨b`, `a⇒b`, `a=b`, `a⧧b` and
`if a then b else c` as BDDs, `a b c` variables `0 1 2`. -/
theorem exercise_15_a (σ : ℕ → Bool) :
    (BDD.ite 0 .bot .top).eval σ = !σ 0 ∧
    (BDD.ite 0 (.ite 1 .top .bot) .bot).eval σ = (σ 0 && σ 1) ∧
    (BDD.ite 0 .top (.ite 1 .top .bot)).eval σ = (σ 0 || σ 1) ∧
    (BDD.ite 0 (.ite 1 .top .bot) .top).eval σ = imp (σ 0) (σ 1) ∧
    (BDD.ite 0 (.ite 1 .top .bot) (.ite 1 .bot .top)).eval σ = (σ 0 == σ 1) ∧
    (BDD.ite 0 (.ite 1 .bot .top) (.ite 1 .top .bot)).eval σ = (σ 0 != σ 1) ∧
    (BDD.ite 0 (.ite 1 .top .bot) (.ite 2 .top .bot)).eval σ =
      (bif σ 0 then σ 1 else σ 2) := by
  simp only [BDD.eval]
  cases σ 0 <;> cases σ 1 <;> cases σ 2 <;> decide

/-! ### Exercise 16: degenerate operators -/

/-- The three-operand operator with value table `t`. -/
def op₃ (t : Fin 256) (a b c : Bool) : Bool :=
  (t.val / 2 ^ ((if a then 0 else 4) + (if b then 0 else 2) + (if c then 0 else 1))) % 2 == 1

/-- Whether it can be expressed without one of its operands. -/
def degenerate (t : Fin 256) : Bool :=
  let bs := [true, false]
  (bs.all fun b => bs.all fun c => op₃ t true b c == op₃ t false b c) ||
  (bs.all fun a => bs.all fun c => op₃ t a true c == op₃ t a false c) ||
  (bs.all fun a => bs.all fun b => op₃ t a b true == op₃ t a b false)

/-- **Exercise 16**: 38 of the 256 three-operand operators are degenerate. -/
theorem exercise_16 : ((List.finRange 256).filter degenerate).length = 38 := by decide

/-! ### Exercise 18: Jane's umbrella -/

/-- **Exercise 18**: raining `r`, umbrella `u`, wet `w`. -/
theorem exercise_18 (r u w : Bool) : imp (imp (r && !u) w && r && !w) u = true := by
  revert r u w; decide

/-! ### Exercise 19: pigs -/

/-- **Exercise 19**: if a sentence `s` says `s ⇒ p` and is true or false as it
says, then it is true, and pigs fly. -/
theorem exercise_19 (s p : Bool) (h : s = imp s p) : s = true ∧ p = true := by
  revert h; revert s p; decide

/-! ### Exercise 21: the maid and the butler -/

/-- **Exercise 21**: if the maid told the truth the butler was in the living
room, so near the kitchen, so he heard the shot; if the butler told the truth
he did not. So one of them lied. -/
theorem exercise_21 (mtt btt blr bnk bhs : Bool)
    (h₁ : imp mtt blr = true) (h₂ : imp blr bnk = true) (h₃ : imp bnk bhs = true)
    (h₄ : imp btt (!bhs) = true) : (!mtt || !btt) = true := by
  revert h₁ h₂ h₃ h₄; revert mtt btt blr bnk bhs; decide

/-! ### Exercise 22: tennis -/

/-- **Exercise 22**: playing `p`, watching `w`, reading `r`, at most one at a
time: (a) the speaker is not reading about tennis; (b) the speaker is watching
tennis. -/
theorem exercise_22 (p w r : Bool) (h₁ : imp (!p) w = true) (h₂ : imp (!w) r = true)
    (h₃ : ([p, w, r].count true ≤ 1)) : r = false ∧ w = true ∧ p = false := by
  revert h₁ h₂ h₃; revert p w r; decide

/-! ### Exercise 23: an inconsistent theory -/

/-- **Exercise 23**: if `p` is both a theorem and an antitheorem, then so is any
`q` — in particular `q = q` is both. -/
theorem exercise_23 (p q : Bool) (ht : p = true) (ha : p = false) :
    q = true ∧ q = false := by
  rw [ht] at ha; exact absurd ha (by decide)

/-! ### Exercise 24: the caskets -/

/-- **Exercise 24**: with `m` the money being in the gold casket, the gold
inscription `g = ¬m` and the silver `s = (g ⧧ s)`: the money is in the gold
casket. -/
theorem exercise_24 (m g s : Bool) (hg : g = !m) (hs : s = (g != s)) : m = true := by
  revert hg hs; revert m g s; decide

/-! ### Exercise 26: knights and knaves

`P`, `Q`, `R` are whether each is a knight; a knight's statements are true and a
knave's false, so an inhabitant who says `s` satisfies `X = s`. -/

/-- **Exercise 26(a)**: `P` says "if I am a knight, I eat my hat": `P` eats it. -/
theorem exercise_26_a (P h : Bool) (hP : P = imp P h) : P = true ∧ h = true := by
  revert hP; revert P h; decide

/-- **Exercise 26(b)**: `P` says "if `Q` is a knight, I am a knave": `P` is a
knight and `Q` a knave. -/
theorem exercise_26_b (P Q : Bool) (hP : P = imp Q (!P)) : P = true ∧ Q = false := by
  revert hP; revert P Q; decide

/-- **Exercise 26(c)**: `P` says "there is gold if and only if I am a knight":
there is gold, and `P` may be either. -/
theorem exercise_26_c :
    (∀ P g : Bool, P = (g == P) → g = true) ∧ (true = (true == true)) ∧
      (false = (true == false)) := by decide

/-- **Exercise 26(d)**: whoever `P` is, asked whether he is a knight or a knave
he says "knight" (`a`); `Q` says `P` said "knave"; `R` says `Q` lies. `Q` is a
knave and `R` a knight. -/
theorem exercise_26_d (P a Q R : Bool) (hP : P = (a == P)) (hQ : Q = !a) (hR : R = !Q) :
    Q = false ∧ R = true := by
  revert hP hQ hR; revert P a Q R; decide

/-- Exactly one of three is true. -/
def one (P Q R : Bool) : Bool := [P, Q, R].count true == 1

/-- **Exercise 26(e)**: `Q` says `P` said there is exactly one knight (`said`,
and if so `P` was right or wrong as he is); `R` says `Q` lies. `Q` is a knave and
`R` a knight. -/
theorem exercise_26_e (P Q R said : Bool) (hP : imp said (P == one P Q R) = true)
    (hQ : Q = said) (hR : R = !Q) : Q = false ∧ R = true := by
  revert hP hQ hR; revert P Q R said; decide

/-- **Exercise 26(f)**: `P` says all are knaves, `Q` says exactly one is a knight:
`P` and `R` are knaves, `Q` a knight. -/
theorem exercise_26_f (P Q R : Bool) (hP : P = (!P && !Q && !R)) (hQ : Q = one P Q R) :
    P = false ∧ Q = true ∧ R = false := by
  revert hP hQ; revert P Q R; decide

/-- **Exercise 26(g)**: `P` says `Q` and `R` are the same; `R`, asked whether
`P` and `Q` are the same, answers yes. -/
theorem exercise_26_g (P Q R ans : Bool) (hP : P = (Q == R)) (hR : R = (ans == (P == Q))) :
    ans = true := by
  revert hP hR; revert P Q R ans; decide

/-- **Exercise 26(h)**: each says the other two are knaves: there are two
knaves. -/
theorem exercise_26_h (P Q R : Bool) (hP : P = (!Q && !R)) (hQ : Q = (!P && !R))
    (hR : R = (!P && !Q)) : [P, Q, R].count false = 2 := by
  revert hP hQ hR; revert P Q R; decide

/-! ### Exercise 27: pirate gold -/

/-- A person of the islands. -/
inductive Kind | knight | knave | normal
  deriving DecidableEq

/-- **Exercise 27**: ask anyone "is your being a knight the same as there being
gold on `X`?", and dig on `X` if the answer is yes, on `Y` if no: there is gold
where you dig. A knight answers `gx`, a knave lies about `¬gx` and also says
`gx`, and a normal person, whatever he says, is on islands with gold on both. -/
theorem exercise_27 (k : Kind) (gx gy ans : Bool) (hg : (gx || gy) = true)
    (hn : k = .normal → gx = true ∧ gy = true)
    (hk : k = .knight → ans = (true == gx)) (hv : k = .knave → ans = !(false == gx)) :
    (bif ans then gx else gy) = true := by
  cases k
  · rw [hk rfl]; cases gx <;> simp_all
  · rw [hv rfl]; cases gx <;> simp_all
  · obtain ⟨h₁, h₂⟩ := hn rfl; cases ans <;> simp [h₁, h₂]

/-! ### Exercise 28: the doorway to heaven -/

/-- **Exercise 28**: ask "if I asked you whether this door leads to heaven,
would you say yes?". A truthful guard (`t`) answers truthfully what he would
say, a lying one lies about what he would say; either way the answer is whether
it leads to heaven (`h`). -/
theorem exercise_28 (t h : Bool) :
    let would := bif t then h else !h
    (bif t then would else !would) = h := by
  revert t h; decide

/-! ### Exercise 29: bracket algebra (its meaning) -/

/-- A bracket expression: empty, bracketed, adjacent, or a variable. -/
inductive Br
  | empty
  | brk (x : Br)
  | adj (x y : Br)
  | var (n : ℕ)

/-- Its meaning: empty is `⊤`, brackets negate, adjacency conjoins. -/
def Br.eval (σ : ℕ → Bool) : Br → Bool
  | empty => true
  | brk x => !x.eval σ
  | adj x y => x.eval σ && y.eval σ
  | var n => σ n

/-- **Exercise 29(a)–(b)**, as meanings: the bracket expressions written for
`¬(¬(a∧b)∧¬(¬a∧b)∧¬(a∧¬b)∧¬(¬a∧¬b))` and for `(¬a⇒¬b) ∧ (a⧧b) ∨ (a∧c ⇒ b∧c)`
(`a b c` variables `0 1 2`) mean `⊤` whatever the variables. -/
theorem exercise_29 (σ : ℕ → Bool) :
    let a := Br.var 0; let b := Br.var 1; let c := Br.var 2
    (Br.brk (.adj (.brk (.adj a b)) (.adj (.brk (.adj (.brk a) b))
      (.adj (.brk (.adj a (.brk b))) (.brk (.adj (.brk a) (.brk b))))))).eval σ = true ∧
    -- `x ⇒ y` is `(x(y))`, `x ∨ y` is `((x)(y))`, `a ⧧ b` is `((a)(b))(ab)`
    (Br.brk (.adj
      (.brk (.adj (.brk (.adj (.brk a) (.brk (.brk b)))) (.adj (.brk (.adj (.brk a) (.brk b)))
        (.brk (.adj a b)))))
      (.brk (.brk (.adj (.adj a c) (.brk (.adj b c))))))).eval σ = true := by
  simp only [Br.eval]
  cases σ 0 <;> cases σ 1 <;> cases σ 2 <;> decide

/-! ### Exercise 30: hats -/

/-- A world: the colors of Back's, Middle's and Front's hats (`true` = red). -/
abbrev World := Bool × Bool × Bool

/-- Every world with at least one red hat. -/
def worlds : List World :=
  [true, false].flatMap fun b => [true, false].flatMap fun m => [true, false].filterMap fun f =>
    if b || m || f then some (b, m, f) else none

/-- Back knows his hat in world `w`, among worlds `ws`: every world he cannot
tell from `w` (same Middle and Front) gives his hat the same color. -/
def backKnows (ws : List World) (w : World) : Bool :=
  (ws.filter fun v => v.2 == w.2).all fun v => v.1 == w.1

/-- Middle knows his hat: he sees only Front's. -/
def middleKnows (ws : List World) (w : World) : Bool :=
  (ws.filter fun v => v.2.2 == w.2.2).all fun v => v.2.1 == w.2.1

/-- **Exercise 30**: after Back and then Middle say they do not know, Front knows
— in every world left, Front's hat is red. -/
theorem exercise_30 :
    let ws₁ := worlds.filter fun w => !backKnows worlds w
    let ws₂ := ws₁.filter fun w => !middleKnows ws₁ w
    ws₂ ≠ [] ∧ ws₂.all (fun w => w.2.2 == true) = true := by decide

/-! ### Exercise 31: absolute value and sign -/

/-- **Exercise 31**: `if x ≥ 0 then x else –x` is the absolute value, and
`if x < 0 then –1 else if x = 0 then 0 else 1` the sign. -/
theorem exercise_31 (x : ℝ) :
    (if 0 ≤ x then x else -x) = |x| ∧
      (if x < 0 then -1 else if x = 0 then 0 else 1 : ℝ) = Real.sign x := by
  refine ⟨?_, ?_⟩
  · split_ifs with h
    · exact (abs_of_nonneg h).symm
    · exact (abs_of_neg (not_le.mp h)).symm
  · rcases lt_trichotomy x 0 with h | h | h
    · simp [h, Real.sign_of_neg h]
    · simp [h]
    · simp [not_lt.mpr h.le, h.ne', Real.sign_of_pos h]

/-! ### Exercises 35 and 36: division -/

open LaPToP.BasicTheories in
/-- **Exercise 35**: `–∞ < y < ∞ ∧ y ⧧ 0 ⇒ (x/y = z = x = z×y)`. -/
theorem exercise_35 {x y z : Number} (hy : Number.Finite y) (h0 : y ≠ 0) :
    x / y = z ↔ x = z * y :=
  EReal.div_eq_iff hy.1.ne' hy.2.ne h0

open LaPToP.BasicTheories in
/-- **Exercise 36**: with the axiom `–∞ < y < ∞ ⇒ x/y×y = x`, the number
axioms are inconsistent: it fails at `x = 1`, `y = 0`. -/
theorem exercise_36 : ¬ ∀ x y : Number, Number.Finite y → x / y * y = x := by
  intro h
  have := h 1 0 (Number.finite_coe 0)
  simp at this

/-! ### Exercise 38: an order from an operator -/

section Ex38

variable {T : Type*} (op : T → T → T)

/-- `a ◊ b = (a • b = a)`. -/
def diamond (a b : T) : Prop := op a b = a

/-- **Exercise 38(a)–(c)**: if `•` is idempotent, `◊` is reflexive; if
associative, transitive; if symmetric, antisymmetric. -/
theorem exercise_38_abc :
    ((∀ a, op a a = a) → ∀ a, diamond op a a) ∧
    ((∀ a b c, op (op a b) c = op a (op b c)) →
      ∀ a b c, diamond op a b → diamond op b c → diamond op a c) ∧
    ((∀ a b, op a b = op b a) → ∀ a b, diamond op a b → diamond op b a → a = b) := by
  refine ⟨fun h a => h a, fun h a b c hab hbc => ?_, fun h a b hab hba => ?_⟩
  · unfold diamond at *
    rw [← hab, h, hbc]
  · unfold diamond at *
    rw [← hab, h, hba]

end Ex38

/-- **Exercise 38(d)–(f)**: with `∧`, `◊` is `⇒`; with `∨`, it is `⇐`; and on the
naturals `≤` comes from `min`. -/
theorem exercise_38_def :
    (∀ a b : Bool, ((a && b) == a) = imp a b) ∧ (∀ a b : Bool, ((a || b) == a) = rimp a b) ∧
    (∀ a b : ℕ, diamond min a b ↔ a ≤ b) :=
  ⟨by decide, by decide, fun a b => by simp [diamond]⟩

/-- **Exercise 38(g)**: when `•` is idempotent, associative and symmetric, it is
determined by `◊`: `a • b` is the greatest `c` (by `◊`) with `c ◊ a` and
`c ◊ b`. -/
theorem exercise_38_g {T : Type*} (op : T → T → T) (hi : ∀ a, op a a = a)
    (ha : ∀ a b c, op (op a b) c = op a (op b c)) (hs : ∀ a b, op a b = op b a) (a b : T) :
    diamond op (op a b) a ∧ diamond op (op a b) b ∧
      ∀ c, diamond op c a → diamond op c b → diamond op c (op a b) := by
  unfold diamond
  refine ⟨?_, ?_, fun c hca hcb => ?_⟩
  · rw [ha, hs b a, ← ha, hi]
  · rw [ha, hi]
  · rw [← ha, hca, hcb]

end LaPToP.Exercises.Ch1
