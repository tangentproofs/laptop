import LaPToP.ProgramTheory.InterpreterTime

/-!
# A faster interpreter, proved to compute the same thing

`Interpreter.run` keeps the state as a function, and each assignment wraps the
function in one more `Function.update`, so reading a variable after `k`
assignments takes `k` steps and a loop of `n` iterations takes time quadratic in
`n`. For a machine that is an implementation detail, so here is the same
interpreter on a state kept in an array — a variable is read in constant time —
and the theorem that it computes exactly what `run` computes
(`runFast_eq`, `runTFast_eq`). The command line runs this one, so what it prints
is still, by those theorems, what the proved interpreter computes.

Variables are natural numbers, as in the language of `InterpreterLang`; a
variable past the end of the array holds the default value, as a variable never
assigned does there.
-/

namespace LaPToP.ProgramTheory.Interpreter

universe v

variable {Val : Type v} [Inhabited Val] [Defs ℕ Val]

/-- The state an array stands for. -/
def toFun (a : Array Val) : Spec.State ℕ Val := fun x => (a[x]?).getD default

/-- Assign `v` to variable `x`, growing the array if `x` is past its end. -/
def store (a : Array Val) (x : ℕ) (v : Val) : Array Val :=
  if x < a.size then a.set! x v else (a ++ Array.replicate (x - a.size) default).push v

omit [Defs ℕ Val] in
/-- Storing is assignment. -/
theorem toFun_store (a : Array Val) (x : ℕ) (v : Val) :
    toFun (store a x v) = Function.update (toFun a) x v := by
  funext y
  unfold toFun store
  by_cases hy : y = x
  · subst hy
    split_ifs with hx
    · simp [hx]
    · rw [Array.getElem?_push]
      simp only [Array.size_append, Array.size_replicate]
      rw [ite_eq_left (by omega)]
      simp
  · rw [Function.update_of_ne hy]
    split_ifs with hx
    · simp [Array.set!, Ne.symm hy]
    · rw [Array.getElem?_push]
      split_ifs with h
      · simp at h; omega
      · rw [Array.getElem?_append]
        split_ifs with h'
        · rfl
        · have : a[y]? = none := Array.getElem?_eq_none (by omega)
          rw [this, Array.getElem?_replicate]
          split_ifs <;> rfl

/-- The state after two concurrent processes, in an array. -/
def mergeArr (own : ℕ → Bool) (a b : Array Val) : Array Val :=
  Array.ofFn (n := max a.size b.size) fun i =>
    if own i then (a[i.1]?).getD default else (b[i.1]?).getD default

omit [Defs ℕ Val] in
/-- Merging arrays is merging states. -/
theorem toFun_mergeArr (own : ℕ → Bool) (a b : Array Val) :
    toFun (mergeArr own a b) = Spec.merge own (toFun a) (toFun b) := by
  funext y
  unfold toFun mergeArr Spec.merge
  by_cases hy : y < max a.size b.size
  · simp [hy]
  · have ha : a[y]? = none := Array.getElem?_eq_none (by omega)
    have hb : b[y]? = none := Array.getElem?_eq_none (by omega)
    simp [hy, ha, hb]

/-- `run`, on a state kept in an array. -/
def runFast : ℕ → Prog ℕ Val → Array Val → Option (Array Val)
  | 0, _, _ => none
  | _ + 1, .ok, a => some a
  | _ + 1, .assign x e, a => some (store a x (e (toFun a)))
  | n + 1, .seq p q, a => (runFast n p a).bind (runFast n q)
  | n + 1, .cond b p q, a => if b (toFun a) then runFast n p a else runFast n q a
  | n + 1, .whileDo b p, a =>
      if b (toFun a) then (runFast n p a).bind (runFast n (.whileDo b p)) else some a
  | n + 1, .newLocal x e p, a =>
      (runFast n p (store a x (e (toFun a)))).map fun t => store t x (toFun a x)
  | _ + 1, .assignAt x e, a => some (store a (x (toFun a)) (e (toFun a)))
  | _ + 1, .ensure b, a => if b (toFun a) then some a else none
  | n + 1, .or p _, a => runFast n p a
  | _ + 1, .tick, a => some a
  | _ + 1, .assert b, a => if b (toFun a) then some a else none
  | n + 1, .call k, a => runFast n (Defs.body k) a
  | n + 1, .par own p q, a =>
      (runFast n p a).bind fun a₁ => (runFast n q a).map fun a₂ => mergeArr own a₁ a₂
  | n + 1, .prob r p q, a => if 0 < r (toFun a) then runFast n p a else runFast n q a

/-- **The fast interpreter is the interpreter**: it reaches a state exactly
when `run` does, and the same one. -/
theorem runFast_eq : ∀ (f : ℕ) (p : Prog ℕ Val) (a : Array Val),
    (runFast f p a).map toFun = run f p (toFun a) := by
  intro f
  induction f with
  | zero => intro p a; cases p <;> rfl
  | succ n ih =>
    intro p a
    cases p with
    | ok => rfl
    | assign x e => simp [runFast, run, toFun_store]
    | seq p q =>
      simp only [runFast, run]
      rw [← ih p a]
      cases runFast n p a with
      | none => rfl
      | some a₁ => simp [ih q a₁]
    | cond b p q =>
      simp only [runFast, run]
      split_ifs
      · exact ih p a
      · exact ih q a
    | whileDo b p =>
      simp only [runFast, run]
      split_ifs
      · rw [← ih p a]
        cases runFast n p a with
        | none => rfl
        | some a₁ => simp [ih _ a₁]
      · rfl
    | newLocal x e p =>
      simp only [runFast, run]
      rw [← toFun_store, ← ih p _]
      cases runFast n p _ with
      | none => rfl
      | some t => simp [toFun_store]
    | assignAt x e => simp [runFast, run, toFun_store]
    | ensure b =>
      simp only [runFast, run]
      split_ifs <;> rfl
    | or p q => exact ih p a
    | tick => rfl
    | assert b =>
      simp only [runFast, run]
      split_ifs <;> rfl
    | call k => exact ih _ a
    | par own p q =>
      simp only [runFast, run]
      rw [← ih p a, ← ih q a]
      cases runFast n p a with
      | none => rfl
      | some a₁ =>
        cases runFast n q a with
        | none => rfl
        | some a₂ => simp [toFun_mergeArr]
    | prob r p q =>
      simp only [runFast, run]
      split_ifs
      · exact ih p a
      · exact ih q a

namespace Timed

/-- `runT`, on a state kept in an array. -/
def runTFast : ℕ → Prog ℕ Val → Array Val × ℕ∞ → Option (Array Val × ℕ∞)
  | 0, _, _ => none
  | _ + 1, .ok, st => some st
  | _ + 1, .assign x e, st => some (store st.1 x (e (toFun st.1)), st.2)
  | n + 1, .seq p q, st => (runTFast n p st).bind (runTFast n q)
  | n + 1, .cond b p q, st => if b (toFun st.1) then runTFast n p st else runTFast n q st
  | n + 1, .whileDo b p, st =>
      if b (toFun st.1) then (runTFast n p st).bind (runTFast n (.whileDo b p)) else some st
  | n + 1, .newLocal x e p, st =>
      (runTFast n p (store st.1 x (e (toFun st.1)), st.2)).map
        fun u => (store u.1 x (toFun st.1 x), u.2)
  | _ + 1, .assignAt x e, st => some (store st.1 (x (toFun st.1)) (e (toFun st.1)), st.2)
  | _ + 1, .ensure b, st => if b (toFun st.1) then some st else none
  | n + 1, .or p _, st => runTFast n p st
  | _ + 1, .tick, st => some (st.1, st.2 + 1)
  | _ + 1, .assert b, st => if b (toFun st.1) then some st else some (st.1, ⊤)
  | n + 1, .call k, st => runTFast n (Defs.body k) st
  | n + 1, .par own p q, st =>
      (runTFast n p st).bind fun a => (runTFast n q st).map fun b =>
        (mergeArr own a.1 b.1, max a.2 b.2)
  | n + 1, .prob r p q, st => if 0 < r (toFun st.1) then runTFast n p st else runTFast n q st

/-- The timed state an array and a time stand for. -/
def toTState (st : Array Val × ℕ∞) : TState ℕ Val := ⟨toFun st.1, st.2⟩

/-- **The fast timed interpreter is the timed interpreter.** -/
theorem runTFast_eq : ∀ (f : ℕ) (p : Prog ℕ Val) (st : Array Val × ℕ∞),
    (runTFast f p st).map toTState = runT f p (toTState st) := by
  intro f
  induction f with
  | zero => intro p st; cases p <;> rfl
  | succ n ih =>
    intro p st
    cases p with
    | ok => rfl
    | assign x e => simp [runTFast, runT, toTState, toFun_store]
    | seq p q =>
      simp only [runTFast, runT]
      rw [← ih p st]
      cases runTFast n p st with
      | none => rfl
      | some a => simp [ih q a]
    | cond b p q =>
      by_cases hb : b (toFun st.1) = true
      · simp only [runTFast, runT, toTState, hb, ite_true]; exact ih p st
      · simp only [runTFast, runT, toTState, hb, Bool.false_eq_true, ite_false]; exact ih q st
    | whileDo b p =>
      by_cases hb : b (toFun st.1) = true
      · simp only [runTFast, runT, hb, ite_true]
        rw [show (toTState st).mem = toFun st.1 from rfl, hb, ite_eq_left rfl, ← ih p st]
        cases runTFast n p st with
        | none => rfl
        | some a => simp [ih _ a]
      · simp only [runTFast, runT, toTState, hb, Bool.false_eq_true, ite_false]; rfl
    | newLocal x e p =>
      simp only [runTFast, runT]
      have h := ih p (store st.1 x (e (toFun st.1)), st.2)
      simp only [toTState, toFun_store] at h
      simp only [toTState]
      rw [← h]
      cases runTFast n p _ with
      | none => rfl
      | some u => simp [toTState, toFun_store]
    | assignAt x e => simp [runTFast, runT, toTState, toFun_store]
    | ensure b =>
      by_cases hb : b (toFun st.1) = true
      · simp only [runTFast, runT, toTState, hb, ite_true]; rfl
      · simp only [runTFast, runT, toTState, hb, Bool.false_eq_true, ite_false]; rfl
    | or p q => exact ih p st
    | tick => rfl
    | assert b =>
      by_cases hb : b (toFun st.1) = true
      · simp only [runTFast, runT, toTState, hb, ite_true]; rfl
      · simp only [runTFast, runT, toTState, hb, Bool.false_eq_true, ite_false]; rfl
    | call k => exact ih _ st
    | par own p q =>
      simp only [runTFast, runT]
      rw [← ih p st, ← ih q st]
      cases runTFast n p st with
      | none => rfl
      | some a =>
        cases runTFast n q st with
        | none => rfl
        | some b => simp [toTState, mergeT, toFun_mergeArr]
    | prob r p q =>
      by_cases hr : 0 < r (toFun st.1)
      · simp only [runTFast, runT, toTState, hr, ite_true]; exact ih p st
      · simp only [runTFast, runT, toTState, hr, ite_false]; exact ih q st

end Timed

end LaPToP.ProgramTheory.Interpreter
