import LaPToP.ProgramTheory.CompileNet
import LaPToP.ProgramTheory.NetworkLang
import LaPToP.ProgramTheory.CompileBT
import LaPToP.ProgramTheory.CompileProb

/-!
# Running the language on b4 (`interp --b4`)

The part of the language the b4 compiler takes — `ok`, `tick`, `x:= e`, `if`,
`while`, `do`/`exit` loops, `for` loops, `new x := e in P end`, simultaneous
assignment, specifications with parameters and recursion, `c! e`, `c?`, and a
`||` of processes as the whole program — read by the language's own parser,
which builds the compiler's statements (`CompileB4.Stmt`) beside each program it
reads (`parseToksShadow`), compiled, and run: a single program on one b4
machine, a network on a swarm (`B4.Swarm`). Named statements are laid out from
`0x100` and called with `cl`; local variables keep their old values on the
control stack. `≠ ≤ > ≥` are rewritten into `= <` and `¬`, `⇒` into `¬` and
`∨`, `a ^ n` (for a literal `n`) into products, and `div`/`mod` by a divisor
that may be negative into a conditional expression, all of which the compiler
handles. What the machine computes is, by `CompileB4.load_correct` and
`CompileNet.swarm_correct`, what the language computes, as long as no value
leaves 32 bits; `interp --selftest` also compares the two on the demonstrations.
-/

namespace LaPToP.ProgramTheory.Interpreter.Lang

open LaPToP.ProgramTheory.Interpreter.Demo (Tok Toks)
open LaPToP.ProgramTheory.CompileB4 LaPToP.ProgramTheory.CompileNet B4

/-- `a × a × ⋯ × a`, `n` times (`1` when `n = 0`). -/
def Exp.powB4 (a : Exp) : ℕ → Exp
  | 0 => .lit (.int 1)
  | 1 => a
  | n + 1 => .bin .mul (a.powB4 n) a

/-- `a div b` and `a mod b` by the machine's `dv` and `md`, which agree with the
book's floor division only for a positive divisor: for a negative one,
`a div b = (-a) div (-b)` and `a mod b = -((-a) mod (-b))`. -/
def Exp.divB4 (op : BinOp) (a b : Exp) : Exp :=
  let neg := fun e : Exp => Exp.un .neg e
  let byNeg := fun a b => if op = .div then .bin .div (neg a) (neg b) else neg (.bin .mod (neg a) (neg b))
  match b with
  | .lit (.int k) => if 0 < k then .bin op a b else byNeg a b
  | _ => .cond (.bin .lt b (.lit (.int 0))) (byNeg a b) (.bin op a b)

/-- An expression in the operators the compiler takes, or why not. -/
def Exp.toB4 : Exp → Except String Exp
  | .lit (.int k) => .ok (.lit (.int k))
  | .lit (.bool b) => .ok (.lit (.bool b))
  | .var x => .ok (.var x)
  | .un .neg (.lit (.int k)) => .ok (.lit (.int (-k)))
  | .un .neg a => do .ok (.un .neg (← a.toB4))
  | .un .not a => do .ok (.un .not (← a.toB4))
  | .bin op a b => do
    let a ← a.toB4
    let b ← b.toB4
    match op with
    | .add | .sub | .mul | .eq | .lt | .and | .or => .ok (.bin op a b)
    | .div | .mod => .ok (Exp.divB4 op a b)
    | .ne => .ok (.un .not (.bin .eq a b))
    | .le => .ok (.un .not (.bin .lt b a))
    | .gt => .ok (.bin .lt b a)
    | .ge => .ok (.un .not (.bin .lt a b))
    | .imp => .ok (.bin .or (.un .not a) b)
    | .pow =>
      match b with
      | .lit (.int n) =>
        if n < 0 then .ok (.lit (.int 0))
        else if n ≤ 31 then .ok (a.powB4 n.toNat)
        else .error "the b4 compiler takes a ^ n only for a literal n up to 31"
      | _ => .error "the b4 compiler takes a ^ n only for a literal n up to 31"
  | .index (.var x) i => do .ok (.index (.var x) (← i.toB4))
  | .cond c a b => do .ok (.cond (← c.toB4) (← a.toB4) (← b.toB4))
  | .un .len (.var x) => .ok (.un .len (.var x))
  -- a two-dimensional array, laid out by rows in `B4Program.prepare`
  | .index (.index (.var x) i) j => do .ok (.index (.index (.var x) (← i.toB4)) (← j.toB4))
  | .un .len (.index (.var x) i) => do .ok (.un .len (.index (.var x) (← i.toB4)))
  | _ => .error "the b4 compiler takes only integers, binaries, variables and items of arrays"

/-- The items of a list literal `[a; b; …]`. -/
def Exp.items? : Exp → Option (List Exp)
  | .nil => some []
  | .cons a r => r.items?.map (a :: ·)
  | _ => none

/-- An item of a list literal: an expression, or a row of a two-dimensional one. -/
def Exp.toB4Item (e : Exp) : Except String Exp :=
  match e.items? with
  | some rs => do .ok (Exp.ofList (← rs.mapM Exp.toB4))
  | none => e.toB4

/-- Whether a statement makes a probabilistic choice. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.hasProb : Stmt → Bool
  | .prob _ _ _ _ => true
  | .seq p q | .cond _ p q | .choice p q => p.hasProb || q.hasProb
  | .loop _ p | .scope _ _ p => p.hasProb
  | _ => false

/-- A statement's expressions in the operators the compiler takes, or why not. A
list literal assigned to a variable fills it as an array. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.toB4 : Stmt → Except String Stmt
  | .assign x e => do
    match e.items? with
    | some es => .ok (.fill x (← es.mapM Exp.toB4Item))
    | none => .ok (.assign x (← e.toB4))
  | .seq p q => do .ok (.seq (← p.toB4) (← q.toB4))
  | .cond c p q => do .ok (.cond (← c.toB4) (← p.toB4) (← q.toB4))
  | .loop c p => do .ok (.loop (← c.toB4) (← p.toB4))
  | .send ch e => do .ok (.send ch (← e.toB4))
  | .scope x e p => do .ok (.scope x (← e.toB4) (← p.toB4))
  | .store x i e => do
    match i.items? with
    | some is => .ok (.store x (Exp.ofList (← is.mapM Exp.toB4)) (← e.toB4))
    | none => .ok (.store x (← i.toB4) (← e.toB4))
  | .choice p q => do .ok (.choice (← p.toB4) (← q.toB4))
  | .ensure c => do .ok (.ensure (← c.toB4))
  | .fill x es => do .ok (.fill x (← es.mapM Exp.toB4Item))
  | .prob a b p q => do .ok (.prob (← a.toB4) (← b.toB4) (← p.toB4) (← q.toB4))
  | s => .ok s

/-- A program for b4: its processes (one, if there is no `||`), the named
statements they call, its variables, and its channels. -/
structure B4Program where
  /-- The processes. -/
  procs : List Stmt
  /-- The named statements. -/
  defs : List (ℕ × Stmt)
  /-- The variables: variable `k` is written `names[k]`. -/
  names : List String
  /-- The channels: name, variable, (unused) cursor variable. -/
  chans : List (String × ℕ × ℕ)

/-- Read a program for b4, the names given on the command line first, through the
language's own parser (`parseToksShadow`), after checking it as the interpreter
does. -/
def parseB4 (names : List String) (ts : Toks) : Except String B4Program := do
  let _ ← parseToksMode true names ts
  let sh ← parseToksShadow names ts
  let procs ← sh.procs.mapM Stmt.toB4
  let defs ← sh.defs.mapM fun (k, p) => do .ok (k, ← p.toB4)
  if !(procs ++ defs.map (·.2)).any Stmt.hasProb then
    return ⟨procs, defs, sh.names, sh.chans⟩
  -- probabilistic choices, made deterministic over a hidden seed (`CompileProb`)
  if procs.length > 1 then
    throw "a probabilistic choice is compiled only for a program without ||"
  let z := sh.names.length
  .ok ⟨procs.map (·.det z), defs.map fun (k, p) => (k, p.det z), sh.names ++ ["#seed"], sh.chans⟩

/-! ### Running -/

/-- The variables a statement may assign, given those each named statement may.
A scope hides its own variable. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.writes (look : ℕ → List ℕ) : Stmt → List ℕ
  | .assign x _ | .store x _ _ | .fill x _ => [x]
  | .recv _ x | .check _ x => [x]
  | .seq p q | .cond _ p q | .choice p q => p.writes look ++ q.writes look
  | .loop _ p => p.writes look
  | .scope x _ p => (p.writes look).filter (· != x)
  | .call k => look k
  | _ => []

/-- The channels a statement outputs on (`true`) or inputs from, given those of
each named statement. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.comms (look : ℕ → List (Bool × ℕ)) :
    Stmt → List (Bool × ℕ)
  | .send c _ => [(true, c)]
  | .recv c _ | .check c _ => [(false, c)]
  | .seq p q | .cond _ p q | .choice p q => p.comms look ++ q.comms look
  | .loop _ p | .scope _ _ p => p.comms look
  | .call k => look k
  | _ => []

/-- Close a property of named statements under the calls they make: the least
solution, by iteration from nothing. -/
def closeDefs {α : Type} [BEq α] (defs : List (ℕ × Stmt)) (f : (ℕ → List α) → Stmt → List α) :
    ℕ → List (ℕ × List α) → List (ℕ × List α)
  | 0, w => w
  | n + 1, w =>
    let look := fun k => (w.lookup k).getD []
    let w' := defs.map fun (k, b) => (k, (f look b).eraseDups)
    if w' == w then w else closeDefs defs f n w'

/-- What each named statement may assign. -/
def B4Program.writesLook (bp : B4Program) : ℕ → List ℕ :=
  let w := closeDefs bp.defs Stmt.writes (bp.defs.length * (bp.names.length + 1) + 1) []
  fun k => (w.lookup k).getD []

/-- Where each named statement communicates. -/
def B4Program.commsLook (bp : B4Program) : ℕ → List (Bool × ℕ) :=
  let w := closeDefs bp.defs Stmt.comms (bp.defs.length * (2 * bp.chans.length + 1) + 1) []
  fun k => (w.lookup k).getD []

/-- Whether an expression is a binary, by its form. -/
def Exp.isBin : Exp → Bool
  | .lit (.bool _) | .un .not _ => true
  | .bin op _ _ => op == .eq || op == .lt || op == .and || op == .or
  | .cond _ a b => a.isBin && b.isBin
  | _ => false

/-- The expressions a statement assigns to `x`. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.assignsTo (x : ℕ) : Stmt → List Exp
  | .assign y e => if x = y then [e] else []
  | .seq p q | .cond _ p q | .choice p q => p.assignsTo x ++ q.assignsTo x
  | .loop _ p | .scope _ _ p => p.assignsTo x
  | _ => []

/-- A variable every assignment of which is a binary, so it is shown as one. -/
def B4Program.isBinVar (bp : B4Program) (x : ℕ) : Bool :=
  let es := (bp.procs ++ bp.defs.map (·.2)).flatMap (·.assignsTo x)
  !es.isEmpty && es.all Exp.isBin

/-- The variables an expression indexes, or takes the length of. -/
def Exp.arrs : Exp → List ℕ
  | .un .len (.var x) => [x]
  | .index (.var x) i => x :: i.arrs
  | .index a i => a.arrs ++ i.arrs
  | .bin _ a b => a.arrs ++ b.arrs
  | .un _ a => a.arrs
  | .cond c a b => c.arrs ++ a.arrs ++ b.arrs
  | _ => []

/-- The expressions of a statement. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.exps : Stmt → List Exp
  | .assign _ e | .send _ e | .ensure e => [e]
  | .store _ i e => [i, e]
  | .fill _ es => es
  | .seq p q | .choice p q => p.exps ++ q.exps
  | .cond c p q => c :: p.exps ++ q.exps
  | .loop c p => c :: p.exps
  | .scope _ e p => e :: p.exps
  | _ => []

/-- Whether the branches of each conditional expression are short enough for the
relative hops (`h0`, at most 127 bytes) its code is made of. -/
def Exp.hopsOk (L : Layout) : Exp → Bool
  | .cond c a b => c.hopsOk L && a.hopsOk L && b.hopsOk L &&
      (ecode L a).length + 9 < 128 && (ecode L b).length + 2 < 128
  | .bin _ a b => a.hopsOk L && b.hopsOk L
  | .un _ a => a.hopsOk L
  | .index _ i => i.hopsOk L
  | _ => true

/-- The variables a statement uses as arrays. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.arrs : Stmt → List ℕ
  | .assign _ e | .send _ e => e.arrs
  | .store x i e => x :: i.arrs ++ e.arrs
  | .fill x es => x :: es.flatMap Exp.arrs
  | .seq p q => p.arrs ++ q.arrs
  | .cond c p q => c.arrs ++ p.arrs ++ q.arrs
  | .loop c p => c.arrs ++ p.arrs
  | .scope _ e p => e.arrs ++ p.arrs
  | .choice p q => p.arrs ++ q.arrs
  | .ensure c => c.arrs
  | _ => []

/-- The lists a statement assigns whole: each variable with how many items. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.fills : Stmt → List (ℕ × ℕ)
  | .fill x es => [(x, es.length)]
  | .seq p q | .cond _ p q | .choice p q => p.fills ++ q.fills
  | .loop _ p | .scope _ _ p => p.fills
  | _ => []

/-- The list literals a statement assigns, with the variables they go to. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.fillsOf : Stmt → List (ℕ × List Exp)
  | .fill x es => [(x, es)]
  | .seq p q | .cond _ p q | .choice p q => p.fillsOf ++ q.fillsOf
  | .loop _ p | .scope _ _ p => p.fillsOf
  | _ => []

/-- The assignments `x:= y` of one variable to another. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.copies : Stmt → List (ℕ × ℕ)
  | .assign x (.var y) => [(x, y)]
  | .seq p q | .cond _ p q | .choice p q => p.copies ++ q.copies
  | .loop _ p | .scope _ _ p => p.copies
  | _ => []

/-- Each `A:= B` of arrays with `cap` cells as `A:= [B 0; …; B (cap-1)]`. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.expandCopies (capOf : ℕ → Option ℕ) : Stmt → Stmt
  | .assign x (.var y) =>
    match capOf x, capOf y with
    | some c, some _ => .fill x ((List.range c).map fun j => .index (.var y) (.lit (.int j)))
    | _, _ => .assign x (.var y)
  | .seq p q => .seq (p.expandCopies capOf) (q.expandCopies capOf)
  | .cond c p q => .cond c (p.expandCopies capOf) (q.expandCopies capOf)
  | .choice p q => .choice (p.expandCopies capOf) (q.expandCopies capOf)
  | .loop c p => .loop c (p.expandCopies capOf)
  | .scope x e p => .scope x e (p.expandCopies capOf)
  | p => p

/-- The variables a statement gives a whole new value: by assignment, input, or
a scope. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.wholes : Stmt → List ℕ
  | .assign x _ | .recv _ x | .check _ x => [x]
  | .seq p q | .cond _ p q | .choice p q => p.wholes ++ q.wholes
  | .loop _ p => p.wholes
  | .scope x _ p => x :: p.wholes
  | _ => []

/-- A two-dimensional array of `r` rows of `c` items, by rows: item `A i j` is
item `i × c + j`; `#A` is `r` and `#(A i)` is `c`. -/
def Exp.flat2 (dims : ℕ → Option (ℕ × ℕ)) : Exp → Exp
  | .index (.index (.var x) i) j =>
    match dims x with
    | some (_, c) => .index (.var x) (.bin .add (.bin .mul (i.flat2 dims) (.lit (.int c))) (j.flat2 dims))
    | none => .index (.index (.var x) (i.flat2 dims)) (j.flat2 dims)
  | .un .len (.index (.var x) i) =>
    match dims x with
    | some (_, c) => .lit (.int c)
    | none => .un .len (.index (.var x) (i.flat2 dims))
  | .un .len (.var x) =>
    match dims x with
    | some (r, _) => .lit (.int r)
    | none => .un .len (.var x)
  | .un op a => .un op (a.flat2 dims)
  | .bin op a b => .bin op (a.flat2 dims) (b.flat2 dims)
  | .index a i => .index (a.flat2 dims) (i.flat2 dims)
  | .cond c a b => .cond (c.flat2 dims) (a.flat2 dims) (b.flat2 dims)
  | .cons a r => .cons (a.flat2 dims) (r.flat2 dims)
  | e => e

/-- A statement with its two-dimensional arrays laid out by rows. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.flat2 (dims : ℕ → Option (ℕ × ℕ)) : Stmt → Stmt
  | .assign x e => .assign x (e.flat2 dims)
  | .seq p q => .seq (p.flat2 dims) (q.flat2 dims)
  | .cond c p q => .cond (c.flat2 dims) (p.flat2 dims) (q.flat2 dims)
  | .loop c p => .loop (c.flat2 dims) (p.flat2 dims)
  | .send ch e => .send ch (e.flat2 dims)
  | .scope x e p => .scope x (e.flat2 dims) (p.flat2 dims)
  | .store x i e =>
    match dims x, i.items? with
    | some (_, c), some [i, j] =>
      .store x (.bin .add (.bin .mul (i.flat2 dims) (.lit (.int c))) (j.flat2 dims)) (e.flat2 dims)
    | _, _ => .store x (i.flat2 dims) (e.flat2 dims)
  | .fill x es =>
    match dims x with
    | some _ => .fill x ((es.flatMap fun r => r.items?.getD [r]).map (·.flat2 dims))
    | none => .fill x (es.map (·.flat2 dims))
  | .choice p q => .choice (p.flat2 dims) (q.flat2 dims)
  | .ensure c => .ensure (c.flat2 dims)
  | p => p

/-- Whether the compiler has code for an expression. -/
def Exp.b4Ok : Exp → Bool
  | .lit (.int _) | .lit (.bool _) | .var _ => true
  | .bin op a b =>
    [BinOp.add, .sub, .mul, .div, .mod, .eq, .lt, .and, .or].contains op && a.b4Ok && b.b4Ok
  | .un .neg a | .un .not a => a.b4Ok
  | .un .len (.var _) => true
  | .index (.var _) i => i.b4Ok
  | .cond c a b => c.b4Ok && a.b4Ok && b.b4Ok
  | _ => false

/-- The rows and items per row of each two-dimensional array: from the list of
lists it starts with, or else from a literal list of lists assigned to it. -/
def B4Program.dims (bp : B4Program) (s : St) : ℕ → Option (ℕ × ℕ) := fun x =>
  let rowsOf := fun (rs : List Value) => match rs with
    | .list r :: _ => some (rs.length, r.length)
    | _ => none
  match s x with
  | .list rs => rowsOf rs
  | _ =>
    ((bp.procs ++ bp.defs.map (·.2)).flatMap Stmt.fillsOf).findSome? fun (y, es) =>
      if y != x then none else
      match es with
      | r :: _ => match r.items? with
        | some items => some (es.length, items.length)
        | none => none
      | [] => none

/-- Get a program ready for b4's arrays, which keep their length: find the arrays
(the variables indexed, measured with `#`, assigned a list literal, or copied to
or from one) and their lengths (the list each starts with, or else the literal
assigned to it, or else the array copied to it); check every literal and copy has
that length; write each copy `A:= B` as `A:= [B 0; …]`; and start an array that
does not start as a list as that many zeros. -/
def B4Program.prepare (bp : B4Program) (s : St) (seed : ℕ := 1) :
    Except String (B4Program × St × List (ℕ × ℕ)) := do
  -- the seed of the probabilistic choices: anything from 1 to 2³¹ – 2
  let s := match bp.names.idxOf? "#seed" with
    | some z => Function.update s z (.int (seed % 2147483646 + 1))
    | none => s
  -- two-dimensional arrays, by rows
  let dims := bp.dims s
  let name := fun x => bp.names.getD x "?"
  let ds := (List.range bp.names.length).filterMap fun x => (dims x).map (x, ·)
  for (x, r, c) in ds do
    let lits : List (ℕ × List Exp) := (bp.procs ++ bp.defs.map (·.2)).flatMap Stmt.fillsOf
    let rows : List ℕ := match s x with
      | .list rs => rs.map fun (v : Value) => v.toList.length
      | _ => lits.flatMap fun (y, es) =>
          if y == x then es.map fun (r : Exp) => (r.items?.map List.length).getD 0 else []
    if rows.any (· != c) then
      throw s!"the rows of {name x} must all have {c} items"
    if (((bp.procs ++ bp.defs.map (·.2)).flatMap Stmt.fillsOf).filter (·.1 == x)).any
        (·.2.length != r) then
      throw s!"b4's arrays keep their length: {name x} has {r} rows"
  let bp : B4Program := ⟨bp.procs.map (·.flat2 dims), bp.defs.map fun (k, p) => (k, p.flat2 dims),
    bp.names, bp.chans⟩
  let s : St := fun x => match dims x, s x with
    | some _, .list rs => .list (rs.flatMap (·.toList))
    | _, v => v
  for p in bp.procs ++ bp.defs.map (·.2) do
    if !(p.exps.all Exp.b4Ok) then
      throw "the b4 compiler takes only integers, binaries, variables, items of arrays and \
        their lengths (a two-dimensional array must start as a list of lists, or be assigned one)"
  let ss := bp.procs ++ bp.defs.map (·.2)
  let fills := ss.flatMap Stmt.fills
  let copies := ss.flatMap Stmt.copies
  let name := fun x => bp.names.getD x "?"
  let arrs₀ := (ss.flatMap Stmt.arrs).eraseDups
  let grow := fun (a : List ℕ) => (a ++ copies.filterMap fun (x, y) =>
    if a.contains x then some y else if a.contains y then some x else none).eraseDups
  let arrs := (List.range (copies.length + 1)).foldl (fun a _ => grow a) arrs₀
  let cap₀ : ℕ → Option ℕ := fun x => match s x with
    | .list vs => some vs.length
    | _ => (fills.find? (·.1 == x)).map (·.2)
  let step := fun (c : ℕ → Option ℕ) (x : ℕ) => match c x with
    | some k => some k
    | none => (copies.findSome? fun (a, b) => if a == x then c b else if b == x then c a else none)
  let capOf := (List.range (copies.length + 1)).foldl (fun c _ => fun x => step c x) cap₀
  let capOf := fun x => if arrs.contains x then capOf x else none
  for x in arrs do
    match capOf x with
    | none => throw s!"{name x} is used as an array, so it must start as a list or be assigned one"
    | some k =>
      for (y, l) in fills do
        if y == x && l != k then
          throw s!"b4's arrays keep their length: {name x} has {k} items, so it cannot be assigned a list of {l}"
  for (x, y) in copies do
    if arrs.contains x && capOf x != capOf y then
      throw s!"b4's arrays keep their length: {name x} and {name y} have different lengths"
  let procs := bp.procs.map fun p => p.expandCopies capOf
  let defs := bp.defs.map fun (k, p) => (k, p.expandCopies capOf)
  let bp' : B4Program := ⟨procs, defs, bp.names, bp.chans⟩
  let s' : St := fun x => match capOf x, s x with
    | some k, .int _ => .list (List.replicate k (.int 0))
    | some k, .bool _ => .list (List.replicate k (.int 0))
    | _, v => v
  for p in bp'.procs ++ bp'.defs.map (·.2) do
    if sdepth p > STACKSZ then
      throw "a list literal or array copy is too long for b4's stack of 256 words"
  .ok (bp', s', ds.map fun (x, _, c) => (x, c))

/-- The array variables, each with as many cells as its list starts with. -/
def B4Program.arrays (bp : B4Program) (s : St) : List (ℕ × ℕ) :=
  ((bp.procs ++ bp.defs.map (·.2)).flatMap Stmt.arrs).eraseDups.map fun x => (x, (s x).toList.length)

/-- The layout: the named statements from `0x100`, each process's code after
them, the variables' cells above the longest, then the arrays'. -/
def B4Program.layout (bp : B4Program) (s : St) : Layout :=
  let L₀ := Layout.build 0 bp.names.length bp.defs (bp.arrays s)
  Layout.build (L₀.start + (bp.procs.map (slen L₀ ·)).foldl max 0 + 16) bp.names.length bp.defs
    (bp.arrays s)

/-- The network the processes make, with the command line's input on the
channels no process writes. -/
def B4Program.toSNet (bp : B4Program) (s : St) : SNet :=
  let cs := bp.procs.map (·.comms bp.commsLook)
  let outs := cs.map fun l => (l.filterMap fun (b, c) => if b then some c else none).eraseDups
  { procs := (bp.procs.zip (outs.zip cs)).map fun (p, o, l) =>
      ⟨p, o, (l.filterMap fun (b, c) => if b then none else some c).eraseDups⟩
    input := fun c => if outs.any (·.contains c) then [] else
      match bp.chans[c]? with
      | some (_, M, _) => (s M).toList.map fun v => (v, 0)
      | none => []
    defs := fun k => (bp.defs.lookup k).getD .ok }

/-- How a run on b4 ended. -/
inductive B4Status where
  /-- Every machine halted. -/
  | halted
  /-- No machine can move, and some have not halted: a deadlock. -/
  | deadlock
  /-- The fuel ran out. -/
  | running
  /-- Backtracking failed: every choice ends in a false `ensure`. -/
  | failed
  deriving DecidableEq, Repr

/-- A word as an integer. -/
def B4Program.value (w : UInt32) : ℤ := toInt32 w

/-- What a run on b4 shows: how it ended, the time, each variable that is not
hidden or a channel's, and each channel's script. -/
structure B4Outcome where
  /-- How it ended. -/
  status : B4Status
  /-- The time it ended (when the last machine did). -/
  time : ℕ
  /-- The variables. -/
  vars : List (String × ℤ)
  /-- The scripts, values with the times they were sent. -/
  scripts : List (String × List (ℤ × ℕ))
  /-- The arrays. -/
  arrays : List (String × List ℤ) := []
  /-- The items per row of each two-dimensional array (its items are by rows). -/
  cols : List (String × ℕ) := []
  deriving DecidableEq, Repr

/-- Whether a statement backtracks (`or`, `ensure`). -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.backtracks : Stmt → Bool
  | .choice _ _ | .ensure _ => true
  | .seq p q | .cond _ p q => p.backtracks || q.backtracks
  | .loop _ p | .scope _ _ p => p.backtracks
  | _ => false

/-- A value as b4 holds it, read back as an integer: a binary is `-1` or `0`. -/
def Value.b4Int : Value → ℤ
  | .int k => k
  | .bool b => if b then -1 else 0
  | .list _ => 0

/-- Run a program that backtracks: on one machine, with as many choice points
as fit above the cells (`CompileBT`). -/
def B4Program.runBT (bp : B4Program) (s : St) (fuel : ℕ) (seed : ℕ := 1) :
    Except String B4Outcome := do
  let (bp, s, cols) ← bp.prepare s seed
  let p ← match bp.procs with
    | [p] => pure p
    | _ => throw "backtracking ('or', 'ensure') is compiled only for a program without ||"
  if !bp.chans.isEmpty then throw "backtracking ('or', 'ensure') is compiled only for a program without channels"
  let L₀ := bp.layout s
  let name := fun x => bp.names.getD x "?"
  for (x, _) in L₀.arrays do
    match s x with
    | .list _ => pure ()
    | _ => throw s!"{name x} is used as an array, so it must start as a list"
    if (bp.procs ++ bp.defs.map (·.2)).any (·.wholes.contains x) then
      throw s!"the b4 compiler changes the array {name x} only item by item, not as a whole"
  for e in (bp.procs ++ bp.defs.map (·.2)).flatMap Stmt.exps do
    if !e.hopsOk L₀ then
      throw "a conditional expression is too long for b4's relative hops; use an if statement"
  let used := L₀.base + 4 * (L₀.W + 5) + 16
  if used > MAXBYTE then throw "the program and its variables do not fit in b4's 64 KB"
  let k := min 64 ((MAXBYTE - used) / (4 * (L₀.W + 1)))
  if k = 0 then throw "no room in b4's 64 KB to keep a choice point"
  let L := { L₀ with choices := k }
  let m := runN (fuel * 10000) (load L p s)
  let flag := toInt32 (getVal m.mem (L.base + 4 * (L.W + 4)))
  let st := if getRST m != 0 then B4Status.running else if flag == -1 then .failed else .halted
  let isArr := fun k => L.arrays.any (·.1 == k)
  let value := fun x => B4Program.value (getVal m.mem (L.addr x))
  let cells := fun x => match L.arrayAt x with
    | some (a₀, cap) => (List.range cap).map fun j => B4Program.value (getVal m.mem (a₀ + 4 * j))
    | none => []
  .ok ⟨st, 0,
    (bp.names.zipIdx.filter fun (n, k) => !n.startsWith "#" && !isArr k).map fun (n, k) => (n, value k),
    [], (bp.names.zipIdx.filter fun (n, k) => !n.startsWith "#" && isArr k).map
      fun (n, k) => (n, cells k),
    cols.map fun (x, c) => (bp.names.getD x "?", c)⟩

/-- Run on b4: compile and load each process, run the swarm (a lone process is a
swarm of one), and read back the result. -/
def B4Program.run (bp : B4Program) (s : St) (fuel : ℕ) (seed : ℕ := 1) :
    Except String B4Outcome := do
  if (bp.procs ++ bp.defs.map (·.2)).any (·.backtracks) then return ← bp.runBT s fuel seed
  let (bp, s, cols) ← bp.prepare s seed
  let L := bp.layout s
  let name := fun x => bp.names.getD x "?"
  for (x, _) in L.arrays do
    match s x with
    | .list _ => pure ()
    | _ => throw s!"{name x} is used as an array, so it must start as a list"
    if (bp.procs ++ bp.defs.map (·.2)).any (·.wholes.contains x) then
      throw s!"the b4 compiler changes the array {name x} only item by item, not as a whole"
  for e in (bp.procs ++ bp.defs.map (·.2)).flatMap Stmt.exps do
    if !e.hopsOk L then
      throw "a conditional expression is too long for b4's relative hops; use an if statement"
  if !(L.base + 4 * L.n + 4 * cellsOf L.arrays + 16 ≤ MAXBYTE) then
    throw "the program and its variables do not fit in b4's 64 KB"
  let net := bp.toSNet s
  for c in [0:bp.chans.length] do
    if (net.procs.filter fun pr => pr.outs.contains c).length > 1 then
      throw s!"channel {(bp.chans[c]?.map (·.1)).getD "?"} is written by two processes"
  let w := (net.load L s).runK fuel
  let st :=
    if w.ms.all (getRST · != 1) then B4Status.halted
    else if w.sweep.2 || w.settle.isSome then .running else .deadlock
  let owner := fun x => bp.procs.findIdx? (·.writes bp.writesLook |>.contains x)
  let value := fun x => match owner x with
    | some i => ((w.ms[i]?).map fun m => B4Program.value (getVal m.mem (L.addr x))).getD 0
    | none => (s x).toInt
  let cells := fun x => match L.arrayAt x, owner x with
    | some (a₀, cap), some i => ((w.ms[i]?).map fun m =>
        (List.range cap).map fun j => B4Program.value (getVal m.mem (a₀ + 4 * j))).getD []
    | _, _ => (s x).toList.map Value.b4Int
  let isArr := fun k => L.arrays.any (·.1 == k)
  .ok ⟨st, (w.ms.map fun m => (getClk m).toNat).foldl max 0,
    (bp.names.zipIdx.filter fun (n, k) => !n.startsWith "#" && !bp.chans.any (·.2.1 == k) &&
      !isArr k).map fun (n, k) => (n, value k),
    bp.chans.zipIdx.map fun ((n, _, _), c) =>
      (n, (w.chans c).map fun (v, t) => (B4Program.value v, t.toNat)),
    (bp.names.zipIdx.filter fun (n, k) => !n.startsWith "#" && isArr k).map
      fun (n, k) => (n, cells k),
    cols.map fun (x, c) => (bp.names.getD x "?", c)⟩

/-- Parse and run on b4. -/
def b4Outcome (names : List String) (ts : Toks) (s : St) (fuel : ℕ) (seed : ℕ := 1) :
    Except String B4Outcome := do
  (← parseB4 names ts).run s fuel seed

/-- Whether the arrays a run on b4 shows are the lists `look` gives. -/
def B4Outcome.arraysAre (b : B4Outcome) (look : String → Option Value) : Bool :=
  b.arrays.all fun (n, l) => (look n).any fun v => l == v.toList.flatMap fun
    | .list r => r.map Value.b4Int
    | w => [w.b4Int]

/-- Whether a run on b4 shows what the network machine computed. -/
def B4Outcome.agrees (b : B4Outcome) (o : NetOutcome) : Bool :=
  (match o.status, b.status with
    | .done, .halted => b.time == o.time.toNat && o.time != ⊤
    | .deadlock, .deadlock => true
    | _, _ => false) &&
  b.vars == (o.vars.filter fun (n, _) => !b.arrays.any (·.1 == n)).map
    (fun (n, v) => (n, v.b4Int)) &&
  b.arraysAre (fun n => o.vars.lookup n) &&
  b.scripts == o.scripts.map (fun (n, l) => (n, l.map fun (v, t) => (v.b4Int, t.toNat)))

/-- Whether a run of a single program on b4 shows what the interpreter computed. -/
def B4Outcome.agreesWith (b : B4Outcome) (names : List String) (s : St) : Bool :=
  b.status == .halted &&
    b.vars == (names.zipIdx.filter fun (n, _) => !n.startsWith "#" && !b.arrays.any (·.1 == n)).map
      (fun (n, k) => (n, (s k).b4Int)) &&
    b.arraysAre fun n => (names.idxOf? n).map s

namespace Demo

#eval b4Outcome ["n"] sumToToks (fun x => if x = 0 then .int 10 else .int 0) 10000
#eval b4Outcome [] sendRecvToks init 1000
#eval b4Outcome [] bufferToks init 1000
#eval b4Outcome [] pipelineToks init 1000
#eval b4Outcome [] deadlockToks init 1000
#eval b4Outcome ["n", "x"] exitLoopToks (fun x => if x = 0 then .int 5 else .int 0) 10000
#eval b4Outcome [] deepExitToks init 100000
#eval b4Outcome ["n"] forLoopToks (fun x => if x = 0 then .int 10 else .int 0) 100000
#eval b4Outcome ["x", "y"] gcdToks (fun x => if x = 0 then .int 12 else if x = 1 then .int 18 else .int 0) 100000
#eval b4Outcome ["x", "y"] swapToks (fun x => if x = 0 then .int 1 else if x = 1 then .int 2 else .int 0) 1000

end Demo

end LaPToP.ProgramTheory.Interpreter.Lang
