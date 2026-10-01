import LaPToP.ProgramTheory.InterpreterTime

/-!
# The interpreter's language: names, values, and the book's operators

`Interpreter.Demo` gave the programming notations a first-order syntax over three
integer variables with fixed names. This module is the language the command line
now runs: any number of variables with any names, whose values are integers,
binaries and lists, and expressions with the operators of the book.

## The model

Programs are `Prog ℕ Value` — the core abstract syntax of `Interpreter`, so
`run`, `runAll`, `denote`, the timed interpreters and every soundness and
completeness theorem apply unchanged. A variable is a natural number; the parser
keeps a table from numbers to the names written in the source. Numbers rather
than strings are the variables because the kernel compares them instantly, which
keeps the demonstrations below proofs by reduction.

`Value` has three kinds: `int`, `bool`, and `list`. "In program theory, an array
is a list variable, and array element assignment assigns the list variable to a
new list that is like the old list but differs in one item" (Section 5.1.0), so
there is no separate array type: `A i:= e` is *defined* as the book's rewriting
`A:= i→e | A` (`assignIdx`), and `denote_assignIdx_iff` proves that it is the
book's definition `A′i = e ∧ (∀j· j⧧i ⇒ A′j = A j) ∧ x′=x ∧ y′=y ∧ ...`. A
two-dimensional element assignment `A i j:= e` is `A:= (i; j)→e | A` in the same
way, a path into nested lists.

## Honest scope

The language is untyped: each operator is total, reading its operands at the
kind it expects (`Value.toInt`, `toBool`, `toList`), so `3 + ⊤` is `3` rather
than an error. Where the book leaves a value undefined — division by `0`, an
index outside a list — this language gives a fixed one (`0`, and no change for an
assignment outside the list). The book's types, bunches, sets, strings and
records are not here, nor are real numbers.
-/

namespace LaPToP.ProgramTheory.Interpreter.Lang

/-! ### Values -/

/-- A value: an integer, a binary, or a list of values. -/
inductive Value where
  /-- An integer. -/
  | int (k : ℤ)
  /-- A binary. -/
  | bool (b : Bool)
  /-- A list. -/
  | list (vs : List Value)
  deriving Repr

mutual

/-- Equality of values is decidable, by a reduction the kernel can carry out. -/
def Value.decEq : (a b : Value) → Decidable (a = b)
  | .int a, .int b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Value.int.inj e)
  | .bool a, .bool b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Value.bool.inj e)
  | .list as, .list bs =>
    match Value.decEqList as bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (Value.list.inj e)
  | .int _, .bool _ | .int _, .list _ | .bool _, .int _ | .bool _, .list _
  | .list _, .int _ | .list _, .bool _ => isFalse Value.noConfusion

/-- Equality of lists of values is decidable. -/
def Value.decEqList : (as bs : List Value) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match Value.decEq a b, Value.decEqList as bs with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h₁, _ => isFalse fun e => h₁ (List.cons.inj e).1
    | _, isFalse h₂ => isFalse fun e => h₂ (List.cons.inj e).2
  | [], _ :: _ => isFalse fun e => nomatch e
  | _ :: _, [] => isFalse fun e => nomatch e

end

instance : DecidableEq Value := Value.decEq

/-- The value of a variable that was never assigned. -/
instance : Inhabited Value := ⟨.int 0⟩

namespace Value

/-- The value read as an integer; `0` if it is not one. -/
def toInt : Value → ℤ
  | .int k => k
  | _ => 0

/-- The value read as a binary; `⊥` if it is not one. -/
def toBool : Value → Bool
  | .bool b => b
  | _ => false

/-- The value read as a list; `[nil]` if it is not one. -/
def toList : Value → List Value
  | .list vs => vs
  | _ => []

/-- List indexing `L i`: item `i` of the list, counting from `0`, and `0` outside
the list. -/
def index (v : Value) (i : ℤ) : Value :=
  if 0 ≤ i then v.toList.getD i.toNat default else default

/-- `(i; j; ...)→e | v`: the value like `v` except at the path `i; j; ...`, which
is `e`. A path that leaves the list changes nothing. -/
def update : Value → List ℤ → Value → Value
  | _, [], e => e
  | .list vs, i :: is, e =>
    if 0 ≤ i ∧ i.toNat < vs.length then .list (vs.set i.toNat ((vs.getD i.toNat default).update is e))
    else .list vs
  | v, _ :: _, _ => v

/-- A value, written as the book writes it: `⊤` and `⊥` for the binaries and
`[a; b; c]` for a list. -/
def render : Value → String
  | .int k => toString k
  | .bool b => if b then "⊤" else "⊥"
  | .list vs => "[" ++ "; ".intercalate (vs.map render) ++ "]"

@[simp] theorem toInt_int (k : ℤ) : (int k).toInt = k := rfl
@[simp] theorem toBool_bool (b : Bool) : (bool b).toBool = b := rfl
@[simp] theorem toList_list (vs : List Value) : (list vs).toList = vs := rfl
@[simp] theorem update_nil (v e : Value) : v.update [] e = e := by cases v <;> rfl

/-- One-level update of a list at an index inside it is `List.set`. -/
theorem update_single {vs : List Value} {i : ℤ} (h : 0 ≤ i ∧ i.toNat < vs.length) (e : Value) :
    (list vs).update [i] e = list (vs.set i.toNat e) := by
  simp [update, h]

end Value

/-! ### Expressions -/

/-- The unary operators: `-x`, `¬x`, and the length `#L`. -/
inductive UnOp where
  | neg | not | len
  deriving Repr, DecidableEq

/-- The binary operators. `+` is addition of integers and catenation of lists, as
in the book. -/
inductive BinOp where
  | add | sub | mul | div | mod | pow
  | eq | ne | lt | le | gt | ge
  | and | or | imp
  deriving Repr, DecidableEq

/-- What a unary operator does. -/
def UnOp.apply : UnOp → Value → Value
  | .neg, v => .int (-v.toInt)
  | .not, v => .bool (!v.toBool)
  | .len, v => .int v.toList.length

/-- What a binary operator does. `div` and `mod` are the book's floor division and
its remainder. -/
def BinOp.apply : BinOp → Value → Value → Value
  | .add, .list a, .list b => .list (a ++ b)
  | .add, a, b => .int (a.toInt + b.toInt)
  | .sub, a, b => .int (a.toInt - b.toInt)
  | .mul, a, b => .int (a.toInt * b.toInt)
  | .div, a, b => .int (a.toInt.fdiv b.toInt)
  | .mod, a, b => .int (a.toInt.fmod b.toInt)
  | .pow, a, b => .int (if 0 ≤ b.toInt then a.toInt ^ b.toInt.toNat else 0)
  | .eq, a, b => .bool (decide (a = b))
  | .ne, a, b => .bool (!decide (a = b))
  | .lt, a, b => .bool (decide (a.toInt < b.toInt))
  | .le, a, b => .bool (decide (a.toInt ≤ b.toInt))
  | .gt, a, b => .bool (decide (b.toInt < a.toInt))
  | .ge, a, b => .bool (decide (b.toInt ≤ a.toInt))
  | .and, a, b => .bool (a.toBool && b.toBool)
  | .or, a, b => .bool (a.toBool || b.toBool)
  | .imp, a, b => .bool (!a.toBool || b.toBool)

/-- The states of the language: every variable holds a value. -/
abbrev St := Spec.State ℕ Value

/-- Expressions over the state. -/
inductive Exp where
  /-- A literal. -/
  | lit (v : Value)
  /-- A variable. -/
  | var (x : ℕ)
  /-- A unary operator. -/
  | un (op : UnOp) (a : Exp)
  /-- A binary operator. -/
  | bin (op : BinOp) (a b : Exp)
  /-- The empty list `[nil]`. -/
  | nil
  /-- An item followed by a list: `[a; b; c]` is `cons a (cons b (cons c nil))`. -/
  | cons (a rest : Exp)
  /-- Indexing `L i`. -/
  | index (a i : Exp)
  /-- `if c then a else b`. -/
  | cond (c a b : Exp)
  deriving Repr

/-- The value of an expression in a state. -/
def Exp.eval : Exp → St → Value
  | .lit v, _ => v
  | .var x, s => s x
  | .un op a, s => op.apply (a.eval s)
  | .bin op a b, s => op.apply (a.eval s) (b.eval s)
  | .nil, _ => .list []
  | .cons a r, s => .list (a.eval s :: (r.eval s).toList)
  | .index a i, s => (a.eval s).index (i.eval s).toInt
  | .cond c a b, s => if (c.eval s).toBool then a.eval s else b.eval s

/-- An expression as a condition. -/
def Exp.test (c : Exp) (s : St) : Bool := (c.eval s).toBool

/-- The literal list `[a; b; ...]`. -/
def Exp.ofList : List Exp → Exp
  | [] => .nil
  | a :: as => .cons a (ofList as)

/-! ### Programs -/

/-- Programs of the language. -/
abbrev P := Prog ℕ Value

/-- `x:= e`. -/
def assign (x : ℕ) (e : Exp) : P := .assign x e.eval

/-- `A i j ...:= e`, which is *by definition* the book's `A:= (i; j; ...)→e | A`
(Section 5.1.0: "change `A i:= e` to `A:= i→e | A` before applying any
programming theory"). -/
def assignIdx (x : ℕ) (idx : List Exp) (e : Exp) : P :=
  .assign x fun s => (s x).update (idx.map fun i => (i.eval s).toInt) (e.eval s)

/-- `if c then p else q`. -/
def ifThen (c : Exp) (p q : P) : P := .cond c.test p q

/-- `while c do p od`. -/
def loop (c : Exp) (p : P) : P := .whileDo c.test p

/-- `new x := e in p end`. -/
def declare (x : ℕ) (e : Exp) (p : P) : P := .newLocal x e.eval p

/-- `ensure c`. -/
def ensure (c : Exp) : P := .ensure c.test

/-- `assert c`. -/
def assert (c : Exp) : P := .assert c.test

/-- The initial state: every variable `0`. -/
def init : St := fun _ => default

/-- The initial state with some variables given. -/
def initWith (xs : List (ℕ × Value)) : St :=
  xs.foldl (fun s (x, v) => Function.update s x v) init

/-- Whether a program can assign to the variable `x`: the syntactic check that a
for-loop's body leaves its index alone ("it cannot be assigned within `P`",
Section 5.2.3). A local declaration of `x` hides the assignments inside it; a
call is not looked into. -/
def assigns (x : ℕ) : P → Bool
  | .assign y _ => y == x
  | .seq p q => assigns x p || assigns x q
  | .cond _ p q => assigns x p || assigns x q
  | .or p q => assigns x p || assigns x q
  | .whileDo _ p => assigns x p
  | .newLocal y _ p => y != x && assigns x p
  | .assignAt _ _ => true
  | _ => false

/-! ### Channels, Section 9.1.1

"Communication on channel `c` is described by two infinite strings `Mc` and `Tc`
called the message script and the time script, and two extended natural
variables `rc` and `wc` called the read cursor and the write cursor", with
`c! e = Mw=e ∧ Tw = t ∧ (w:= w+1)`, `c? = r:= r+1`, `c = M r–1`, `√c = T r ≤ t`.

A sequential program sees of the message script only the messages written so
far, or supplied to it: a channel here is a list variable holding that prefix of
`Mc`, whose length is the write cursor, and a hidden read cursor. Output appends
to the list; input advances the read cursor, and when no message is there it
waits — an assertion that the cursor is inside the list, so that with a clock the
wait is until `∞` (the book's input "must wait" for a message that never comes),
and without one there is no poststate. The time script is not kept. -/

/-- `c! e`: the message `e` is written at the write cursor, the length of the
script so far, which moves on. A variable never assigned is an empty script. -/
def output (M : ℕ) (e : Exp) : P := .assign M fun s => .list ((s M).toList ++ [e.eval s])

/-- `c?`: wait for a message, then move the read cursor past it. -/
def input (M r : ℕ) : P :=
  .seq (.assert fun s => decide ((s r).toInt < ((s M).toList.length : ℤ)))
    (.assign r fun s => .int ((s r).toInt + 1))

/-- `c`, the last message read: `M r–1`. -/
def message (M r : ℕ) : Exp := .index (.var M) (.bin .sub (.var r) (.lit (.int 1)))

/-- `√c`: a message is there to be read. -/
def check (M r : ℕ) : Exp := .bin .lt (.var r) (.un .len (.var M))

/-- Output is the book's `Mw = e ∧ (w:= w+1)` on the part of the script written
so far: the message at the write cursor `w = #M` is `e`, the cursor moves on, and
the messages before it are unchanged. -/
theorem denote_output {M : ℕ} {e : Exp} {s s' : St} (h : denote (output M e) s s') :
    (s' M).toList[(s M).toList.length]? = some (e.eval s) ∧
      (s' M).toList.length = (s M).toList.length + 1 ∧
      (s' M).toList.take (s M).toList.length = (s M).toList ∧ ∀ y, y ≠ M → s' y = s y := by
  have hs : s' = Function.update s M (.list ((s M).toList ++ [e.eval s])) := h
  subst hs
  refine ⟨by simp, by simp, by simp, fun y hy => Function.update_of_ne hy _ _⟩

/-! ### Whole programs -/

/-- A program as the command line runs it: named specifications, each with the
program that refines it, and a main program. -/
structure Program where
  /-- The main program. -/
  main : P
  /-- The definitions: specification `k` is refined by its program. -/
  defs : List (ℕ × P)
  /-- The names of the variables: variable `k` is written `names[k]`. -/
  names : List String
  /-- The names of the specifications, the loops' generated ones included. -/
  procs : List String

/-- The program refining specification `k`; a name with no definition has no
behaviour. -/
def Program.body (prog : Program) (k : ℕ) : P :=
  (prog.defs.lookup k).getD (.ensure fun _ => false)

/-- The definitions of a program, as the interpreter reads them. -/
@[instance_reducible] def Program.env (prog : Program) : Defs ℕ Value := ⟨prog.body⟩

/-- Run a program once. -/
def Program.run (prog : Program) (fuel : ℕ) (s : St) : Option St :=
  letI := prog.env; Interpreter.run fuel prog.main s

/-- Every poststate of a program within the fuel. -/
def Program.runAll (prog : Program) (fuel : ℕ) (s : St) : List St :=
  letI := prog.env; Interpreter.runAll fuel prog.main s

/-- Run a program once on the clock. -/
def Program.runT (prog : Program) (fuel : ℕ) (st : Timed.TState ℕ Value) :
    Option (Timed.TState ℕ Value) :=
  letI := prog.env; Timed.runT fuel prog.main st

/-- Every timed poststate of a program within the fuel. -/
def Program.runAllT (prog : Program) (fuel : ℕ) (st : Timed.TState ℕ Value) :
    List (Timed.TState ℕ Value) :=
  letI := prog.env; Timed.runAllT fuel prog.main st

/-! ### Array element assignment is the book's -/

/-- With no index, element assignment is plain assignment. -/
theorem assignIdx_nil (x : ℕ) (e : Exp) : assignIdx x [] e = assign x e := by
  simp [assignIdx, assign, Value.update_nil]

/-- Setting item `k` of a list, read item by item. -/
theorem getElem?_set_ite {vs : List Value} {k : ℕ} (h : k < vs.length) (v : Value) (j : ℕ) :
    (vs.set k v)[j]? = if j = k then some v else vs[j]? := by
  by_cases hj : j = k
  · subst hj; simp [h]
  · simp [hj, Ne.symm hj]

/-- **Array element assignment**, Section 5.1.0:
`A i:= e = A′i = e ∧ (∀j· j⧧i ⇒ A′j = A j) ∧ x′=x ∧ y′=y ∧ ...`, for a list
variable `A` and an index `i` inside it. The list after is described item by item:
at `i` it is `e`, everywhere else (including past its end) it is the list before;
every other variable is unchanged. -/
theorem denote_assignIdx_iff {A : ℕ} {i e : Exp} {s s' : St} {vs : List Value}
    (hA : s A = .list vs) (hi : 0 ≤ (i.eval s).toInt ∧ (i.eval s).toInt.toNat < vs.length) :
    denote (assignIdx A [i] e) s s' ↔
      (∃ ws, s' A = .list ws ∧
        ∀ j : ℕ, ws[j]? = if j = (i.eval s).toInt.toNat then some (e.eval s) else vs[j]?) ∧
      ∀ y, y ≠ A → s' y = s y := by
  have hupd : (s A).update [(i.eval s).toInt] (e.eval s) =
      .list (vs.set (i.eval s).toInt.toNat (e.eval s)) := by
    rw [hA]; exact Value.update_single hi _
  simp only [assignIdx, denote_assign, Spec.assign, List.map_cons, List.map_nil]
  constructor
  · rintro rfl
    refine ⟨⟨_, by rw [Function.update_self, hupd], fun j => ?_⟩, fun y hy => ?_⟩
    · exact getElem?_set_ite hi.2 _ j
    · exact Function.update_of_ne hy _ _
  · rintro ⟨⟨ws, hws, hj⟩, hy⟩
    funext y
    by_cases hyA : y = A
    · subst hyA
      rw [Function.update_self, hupd, hws]
      congr 1
      apply List.ext_getElem?
      intro j
      rw [hj, getElem?_set_ite hi.2]
    · rw [Function.update_of_ne hyA, hy y hyA]

/-- The Substitution Law is sound for element assignment once it is written as
the book says: `A i:= e. P` is `P` with `(i→e | A)` for `A`. -/
theorem denote_assignIdx_seq (A : ℕ) (idx : List Exp) (e : Exp) (Q : Spec St) :
    Spec.seq (denote (assignIdx A idx e)) Q = fun s s' =>
      Q (Function.update s A ((s A).update (idx.map fun i => (i.eval s).toInt) (e.eval s))) s' := by
  funext s s'
  simp [assignIdx, Spec.seq, Spec.assign]

/-! ### Demonstrations -/

namespace Demo

/-- A list of `n` zeros, as a literal. -/
def zeros (n : ℕ) : Value := .list (List.replicate n (.int 0))

/-- The two examples of Section 5.1.0, on a list variable `A` (variable `0`) and an
index `i` (variable `1`). First: `A 2:= 3. i:= 2. A i:= 4`, after which
`A i = A 2` "should equal ⊤". -/
def arrayExample₁ : P :=
  .seq (assignIdx 0 [.lit (.int 2)] (.lit (.int 3)))
    (.seq (assign 1 (.lit (.int 2))) (assignIdx 0 [.var 1] (.lit (.int 4))))

/-- The run: `A` ends as `[0; 0; 4; 0; 0]` and `i` as `2`, so `A i = A 2`. -/
theorem arrayExample₁_run :
    (run 10 arrayExample₁ (initWith [(0, zeros 5)])).map (fun s => (s 0, s 1)) =
      some (.list [.int 0, .int 0, .int 4, .int 0, .int 0], .int 2) := rfl

theorem arrayExample₁_test :
    (run 10 arrayExample₁ (initWith [(0, zeros 5)])).map
      (fun s => (Exp.bin .eq (.index (.var 0) (.var 1)) (.index (.var 0) (.lit (.int 2)))).test s) =
      some true := rfl

/-- Second: `A 2:= 2. A(A 2):= 3`, after which `A 2 = 2` "should equal ⊥ because
`A 2 = 3` just before the final binary expression". -/
def arrayExample₂ : P :=
  .seq (assignIdx 0 [.lit (.int 2)] (.lit (.int 2)))
    (assignIdx 0 [.index (.var 0) (.lit (.int 2))] (.lit (.int 3)))

theorem arrayExample₂_run :
    (run 10 arrayExample₂ (initWith [(0, zeros 5)])).map (fun s => (s 0).index 2) =
      some (.int 3) := rfl

/-- A two-dimensional element assignment, `A 1 2:= 7` on a 2-by-3 array. -/
theorem twoDim_run :
    (run 10 (assignIdx 0 [.lit (.int 1), .lit (.int 2)] (.lit (.int 7)))
      (initWith [(0, .list [zeros 3, zeros 3])])).map (fun s => s 0) =
      some (.list [zeros 3, .list [.int 0, .int 0, .int 7]]) := rfl

end Demo

end LaPToP.ProgramTheory.Interpreter.Lang
