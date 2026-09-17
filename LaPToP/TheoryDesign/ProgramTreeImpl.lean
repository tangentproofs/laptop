import LaPToP.TheoryDesign.ProgramQueue
import LaPToP.DataStructures.Multidimensional

/-!
# Program-tree theory: the implementer's variables `T` and `p`

This module formalizes the second definition of program-trees in Subsection
7.1.5 (Program-Tree Theory) of Eric Hehner's *A Practical Theory of
Programming* (aPToP), p. 111, and shows that it implements the first.

"Here is another way to define program-trees. Let `T` (for tree) and `p` (for
pointer) be implementer's variables. The axioms are `tree = [tree; X; tree]`,
`T: tree`, `p: *(0, 1, 2)`, `node = T@(p; 1)`, `change = ⟨x: X· T:= (p; 1)→x | T⟩`,
`goUp = p:= p0;..↔p–1`, `goLeft = p:= p;0`, `goRight = p:= p;2`. If strings and
the `@` operator are implemented, then this theory is already an
implementation. If not, it is still a theory, and should be compared to the
previous theory for clarity."

## The model

The tree `[tree; X; tree]` is "infinite in all directions; there are no leaves
and no root", so it is not a finitely nested list (Section 2.3.0): it is
determined by the item at every position, and `T@(p; 1)` — the middle item
`1` of the subtree reached along the path `p` of `0`s (left) and `2`s (right) —
is read as `T` applied to the position. A position is a path from an origin
node, extended, to make the tree rootless, by the number `k` of ancestors
above the origin (the origin is taken to be the left child of its parent, and
so on upward); positions are kept in normal form, so each node has exactly one
name. `goUp`, `goLeft`, `goRight` are the pointer moves `p0;..↔p–1`, `p;0`, `p;2`
on the path component, and `change` is the pointwise update of `T`. Adding
the direction variable `aim` of the first theory, `go` moves in the direction
faced and turns back, and `work` is read as its description — "wander around
changing the values of nodes if you like, but do not go from this node in
this direction; end where you started, facing the way you were facing":
position and aim restored, and `T` unchanged beyond the edge faced. With
these, the six axioms of the first theory (`ProgramTreeTheory`) are proved:
the second definition implements the first (`impl`).
-/

namespace LaPToP.TheoryDesign

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

universe u

namespace ProgramTree

open scoped Classical

/-- A position in the rootless infinite binary tree: `k` steps up from the origin, then the path
`q` down (`false` = left, `0`; `true` = right, `2`), in normal form: an initial left step is
absorbed into `k` (the origin is the left child of its parent). -/
structure Pos where
  /-- Ancestors above the origin. -/
  k : ℕ
  /-- The downward path. -/
  q : List Bool
  /-- Normal form: if `k > 0`, the path does not start with a left step. -/
  norm : k = 0 ∨ q = [] ∨ q.head? = some true

namespace Pos

@[ext] theorem ext' {a b : Pos} (hk : a.k = b.k) (hq : a.q = b.q) : a = b := by
  cases a; cases b; cases hk; cases hq; rfl

/-- The origin, `p = nil`. -/
def origin : Pos := ⟨0, [], Or.inl rfl⟩

/-- `goLeft = p:= p;0`: the left child (the parent's left chain absorbs a left step at `q = nil`). -/
def left (a : Pos) : Pos :=
  if h : 0 < a.k ∧ a.q = [] then ⟨a.k - 1, [], Or.inr (Or.inl rfl)⟩
  else ⟨a.k, a.q ++ [false], by
    rcases a.norm with hk | hq | hh
    · exact Or.inl hk
    · exact Or.inl (by by_contra hk; exact h ⟨Nat.pos_of_ne_zero hk, hq⟩)
    · refine Or.inr (Or.inr ?_)
      rcases hq' : a.q with _ | ⟨b, r⟩
      · simp [hq'] at hh
      · simp [hq'] at hh; simp [hh]⟩

/-- `goRight = p:= p;2`: the right child. -/
def right (a : Pos) : Pos :=
  ⟨a.k, a.q ++ [true], by
    rcases a.norm with hk | hq | hh
    · exact Or.inl hk
    · exact Or.inr (Or.inr (by simp [hq]))
    · refine Or.inr (Or.inr ?_)
      rcases hq' : a.q with _ | ⟨b, r⟩
      · simp [hq'] at hh
      · simp [hq'] at hh; simp [hh]⟩

/-- `goUp = p:= p0;..↔p–1`: the parent (one more ancestor when the path is empty). -/
def up (a : Pos) : Pos :=
  if h : a.q = [] then ⟨a.k + 1, [], Or.inr (Or.inl rfl)⟩
  else ⟨a.k, a.q.dropLast, by
    rcases a.norm with hk | hq | hh
    · exact Or.inl hk
    · exact absurd hq h
    · rcases hq' : a.q.dropLast with _ | ⟨b, r⟩
      · exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr ?_)
        have : a.q.head? = (a.q.dropLast).head? := by
          rcases hq'' : a.q with _ | ⟨c, s⟩
          · exact absurd hq'' h
          · rw [hq''] at hq'; cases s with
            | nil => simp at hq'
            | cons d t => simp
        rw [← hq', ← this]; exact hh⟩

/-- Which child of its parent a position is: the direction from the parent back to it. -/
def childDir (a : Pos) : Dir :=
  match a.q.getLast? with
  | none => Dir.left
  | some false => Dir.left
  | some true => Dir.right

theorem up_left (a : Pos) : (left a).up = a := by
  unfold left up
  split_ifs with h1 h2 h2
  · exact ext' (by simp; omega) h1.2.symm
  · exact absurd rfl h2
  · simp at h2
  · exact ext' rfl (by simp)

theorem up_right (a : Pos) : (right a).up = a := by
  unfold right up
  split_ifs with h
  · simp at h
  · exact ext' rfl (by simp)

theorem childDir_left (a : Pos) : (left a).childDir = Dir.left := by
  unfold left childDir; split_ifs <;> simp

theorem childDir_right (a : Pos) : (right a).childDir = Dir.right := by
  unfold right childDir; simp

/-- A position is a left or a right child, never "up". -/
theorem childDir_ne_up (a : Pos) : a.childDir ≠ Dir.up := by
  unfold childDir
  split <;> simp

/-- Going up and then back down in the direction we came from returns. -/
theorem child_up (a : Pos) : (if a.childDir = Dir.left then (up a).left else (up a).right) = a := by
  rcases a with ⟨k, q, hn⟩
  rcases hq : q.getLast? with _ | ⟨b⟩
  · -- `q = []`: the origin chain
    have hq0 : q = [] := List.getLast?_eq_none_iff.1 hq
    subst hq0
    simp only [childDir, List.getLast?_nil, if_true, up, dif_pos]
    unfold left
    rw [dif_pos ⟨Nat.succ_pos k, rfl⟩]
    exact ext' (by simp) rfl
  · obtain ⟨r, rfl⟩ : ∃ r, q = r ++ [b] := List.getLast?_eq_some_iff.1 hq |>.imp fun r h => h
    have hne : r ++ [b] ≠ [] := by simp
    cases b
    · -- last step left
      have hcd : (⟨k, r ++ [false], hn⟩ : Pos).childDir = Dir.left := by simp [childDir, hq]
      rw [hcd]; simp only [if_true]
      unfold up; rw [dif_neg hne]; simp only [List.dropLast_concat]
      unfold left
      split_ifs with h
      · -- `k > 0` and `r = []`: then `q = [false]` is not normal
        exfalso
        obtain ⟨hk0, hr⟩ := h
        simp only at hk0 hr
        subst hr
        rcases hn with hk | hq' | hh
        · omega
        · exact hne hq'
        · simp at hh
      · exact ext' rfl rfl
    · have hcd : (⟨k, r ++ [true], hn⟩ : Pos).childDir = Dir.right := by simp [childDir, hq]
      rw [hcd]; simp only [reduceCtorEq, if_false]
      unfold up; rw [dif_neg hne]; simp only [List.dropLast_concat]
      unfold right
      exact ext' rfl rfl

/-- `Below a b`: `b` is in the subtree rooted at `a` (`a` itself included). -/
def Below (a b : Pos) : Prop := (b.k = a.k ∧ a.q <+: b.q) ∨ (b.k < a.k ∧ a.q = [])

theorem below_self (a : Pos) : Below a a := Or.inl ⟨rfl, List.prefix_rfl⟩

theorem below_left_subset {a b : Pos} (h : Below (left a) b) : Below a b := by
  unfold left at h
  split_ifs at h with hc
  · rcases h with ⟨hk, -⟩ | ⟨hk, -⟩
    · exact Or.inr ⟨by simp at hk; omega, hc.2⟩
    · exact Or.inr ⟨by simp at hk; omega, hc.2⟩
  · rcases h with ⟨hk, hp⟩ | ⟨hk, hq⟩
    · exact Or.inl ⟨hk, (List.prefix_append _ _).trans hp⟩
    · simp at hq

theorem below_right_subset {a b : Pos} (h : Below (right a) b) : Below a b := by
  unfold right at h
  rcases h with ⟨hk, hp⟩ | ⟨-, hq⟩
  · exact Or.inl ⟨hk, (List.prefix_append _ _).trans hp⟩
  · simp at hq

theorem not_below_left_self (a : Pos) : ¬ Below (left a) a := by
  unfold left Below
  split_ifs with hc
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩) <;> simp at hk <;> omega
  · rintro (⟨-, hp⟩ | ⟨hk, hq⟩)
    · have := hp.length_le; simp at this
    · simp at hq

theorem not_below_right_self (a : Pos) : ¬ Below (right a) a := by
  unfold right Below
  rintro (⟨-, hp⟩ | ⟨hk, hq⟩)
  · have := hp.length_le; simp at this
  · simp at hq

theorem not_below_left_right {a b : Pos} (hl : Below (left a) b) (hr : Below (right a) b) : False := by
  unfold left Below at hl
  unfold right Below at hr
  split_ifs at hl with hc
  · rcases hr with ⟨hk, hp⟩ | ⟨-, hq⟩
    · rcases hl with ⟨hk', -⟩ | ⟨hk', -⟩ <;> simp at hk hk' <;> omega
    · simp at hq
  · rcases hr with ⟨hk, hp⟩ | ⟨-, hq⟩
    · rcases hl with ⟨-, hp'⟩ | ⟨-, hq'⟩
      · -- both `a.q ++ [false]` and `a.q ++ [true]` are prefixes of `b.q`
        obtain ⟨r, hr⟩ := hp
        obtain ⟨r', hr'⟩ := hp'
        rw [← hr] at hr'
        simp [List.append_assoc] at hr'
      · simp at hq'
    · simp at hq

end Pos

/-- The nodes "beyond" position `a` in direction `d`: the component of the neighbour when the
edge in that direction is removed. -/
def beyond (a : Pos) : Dir → Pos → Prop
  | Dir.left, b => Pos.Below a.left b
  | Dir.right, b => Pos.Below a.right b
  | Dir.up, b => ¬ Pos.Below a b

/-- A position is not beyond any of its own edges. -/
theorem not_beyond_self (a : Pos) (d : Dir) : ¬ beyond a d a := by
  cases d
  · exact fun h => h (Pos.below_self a)
  · exact Pos.not_below_left_self a
  · exact Pos.not_below_right_self a

/-- The three edge components of a position are pairwise disjoint. -/
theorem beyond_disjoint {a b : Pos} {c d : Dir} (hcd : c ≠ d) (hc : beyond a c b) (hd : beyond a d b) : False := by
  cases c <;> cases d <;> simp only [beyond] at hc hd
  · exact hcd rfl
  · exact hc (Pos.below_left_subset hd)
  · exact hc (Pos.below_right_subset hd)
  · exact hd (Pos.below_left_subset hc)
  · exact hcd rfl
  · exact Pos.not_below_left_right hc hd
  · exact hd (Pos.below_right_subset hc)
  · exact Pos.not_below_left_right hd hc
  · exact hcd rfl

/-- The neighbour in a direction, and the direction that faces back to where we came from. -/
def neighbour (a : Pos) : Dir → Pos
  | Dir.left => a.left
  | Dir.right => a.right
  | Dir.up => a.up

def back (a : Pos) : Dir → Dir
  | Dir.left => Dir.up
  | Dir.right => Dir.up
  | Dir.up => a.childDir

/-- Going in direction `d` and then back in direction `back` returns to the start. -/
theorem neighbour_back (a : Pos) (d : Dir) : neighbour (neighbour a d) (back a d) = a := by
  cases d
  · have := Pos.child_up a
    rcases hc : a.childDir with _ | _ | _
    · exact absurd hc (Pos.childDir_ne_up a)
    · rw [hc] at this; simp only [if_true] at this
      simp only [neighbour, back, hc]; exact this
    · rw [hc] at this; simp only [reduceCtorEq, if_false] at this
      simp only [neighbour, back, hc]; exact this
  · exact Pos.up_left a
  · exact Pos.up_right a

/-- Facing back from the neighbour, the direction faced next time is the original one. -/
theorem back_back (a : Pos) (d : Dir) : back (neighbour a d) (back a d) = d := by
  cases d
  · rcases hc : a.childDir with _ | _ | _
    · exact absurd hc (Pos.childDir_ne_up a)
    · simp [back, hc]
    · simp [back, hc]
  · simp [neighbour, back, Pos.childDir_left]
  · simp [neighbour, back, Pos.childDir_right]

/-- The start is beyond the neighbour in the back direction: the edge separates them. -/
theorem beyond_neighbour_back (a : Pos) (d : Dir) : beyond (neighbour a d) (back a d) a := by
  cases d
  · have := Pos.child_up a
    rcases hc : a.childDir with _ | _ | _
    · exact absurd hc (Pos.childDir_ne_up a)
    · rw [hc] at this; simp only [if_true] at this
      simp only [neighbour, back, hc, beyond]; rw [this]; exact Pos.below_self a
    · rw [hc] at this; simp only [reduceCtorEq, if_false] at this
      simp only [neighbour, back, hc, beyond]; rw [this]; exact Pos.below_self a
  · exact Pos.not_below_left_self a
  · exact Pos.not_below_right_self a

/-- Beyond the neighbour, facing back, is exactly what is not beyond `a` in direction `d`. -/
theorem beyond_neighbour_back_iff (a b : Pos) (d : Dir) : beyond (neighbour a d) (back a d) b ↔ ¬ beyond a d b := by
  cases d
  · have := Pos.child_up a
    rcases hc : a.childDir with _ | _ | _
    · exact absurd hc (Pos.childDir_ne_up a)
    · rw [hc] at this; simp only [if_true] at this
      simp only [neighbour, back, hc, beyond, not_not]; rw [this]
    · rw [hc] at this; simp only [reduceCtorEq, if_false] at this
      simp only [neighbour, back, hc, beyond, not_not]; rw [this]
  · rfl
  · rfl

/-! ### The implementation -/

variable (X : Type u)

/-- The implementer's state: the tree `T` (its item at every position), the pointer `p` and the
direction `aim`. -/
structure St where
  /-- `T`, by its items: `node = T@(p; 1)` is `T p`. -/
  T : Pos → X
  /-- `p`. -/
  p : Pos
  /-- `aim`. -/
  aim : Dir

variable {X}

/-- `node = T@(p; 1)`. -/
def node (s : St X) : X := s.T s.p

/-- `change = ⟨x: X· T:= (p; 1)→x | T⟩`, i.e. `node:= x`. -/
def change (x : X) : Spec (St X) := fun s s' => s' = { s with T := Function.update s.T s.p x }

/-- `aim:= d`. -/
def assignAim (d : Dir) : Spec (St X) := fun s s' => s' = { s with aim := d }

/-- `go`: move to the neighbour in the direction faced (`goUp`, `goLeft` or `goRight`) and face back. -/
def go : Spec (St X) := fun s s' => s' = { s with p := neighbour s.p s.aim, aim := back s.p s.aim }

/-- `work`: "wander around changing the values of nodes if you like, but do not go from this node
in this direction; end where you started, facing the way you were facing": `T` may change
only on nodes not beyond the edge faced. -/
def work : Spec (St X) := fun s s' =>
  s'.p = s.p ∧ s'.aim = s.aim ∧ ∀ b, beyond s.p s.aim b → s'.T b = s.T b

theorem aim_go : Refines (fun s s' : St X => (s'.aim = Dir.up) ↔ s.aim ≠ Dir.up) go := by
  rintro s s' rfl
  show back s.p s.aim = Dir.up ↔ s.aim ≠ Dir.up
  cases h : s.aim
  · rcases hc : s.p.childDir with _ | _ | _
    · exact absurd hc (Pos.childDir_ne_up _)
    · simp [back, hc]
    · simp [back, hc]
  · simp [back]
  · simp [back]

theorem go_work_go : Refines (fun s s' : St X => node s' = node s ∧ s'.aim = s.aim) (seq go (seq work go)) := by
  rintro s s' ⟨u, rfl, v, ⟨hp, haim, hT⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · show v.T (neighbour v.p v.aim) = s.T s.p
    rw [hp, haim, neighbour_back]
    exact hT s.p (beyond_neighbour_back s.p s.aim)
  · show back v.p v.aim = s.aim
    rw [hp, haim, back_back]

theorem work_ok : Refines (work : Spec (St X)) ok := by
  rintro s s' rfl; exact ⟨rfl, rfl, fun _ _ => rfl⟩

theorem work_change (x : X) : Refines work (change x) := by
  rintro s s' rfl
  refine ⟨rfl, rfl, fun b hb => ?_⟩
  show Function.update s.T s.p x b = s.T b
  rw [Function.update_of_ne]
  rintro rfl
  exact not_beyond_self s.p s.aim hb

theorem work_turn (a b : Dir) : Refines (work : Spec (St X))
    (fun s s' => a = s.aim ∧ s.aim ≠ b ∧ seq (assignAim b) (seq go (seq work (seq go (assignAim a)))) s s') := by
  rintro s s' ⟨rfl, hab, u, rfl, v, rfl, w, ⟨hp, haim, hT⟩, z, rfl, rfl⟩
  refine ⟨?_, rfl, fun c hc => ?_⟩
  · show neighbour w.p w.aim = s.p
    rw [hp, haim, neighbour_back]
  · show w.T c = s.T c
    apply hT
    rw [beyond_neighbour_back_iff s.p c b]
    exact fun hb => beyond_disjoint (Ne.symm hab) hb hc

theorem work_work : Refines (work : Spec (St X)) (seq work work) := by
  rintro s s' ⟨u, ⟨hp₁, ha₁, hT₁⟩, hp₂, ha₂, hT₂⟩
  refine ⟨hp₂.trans hp₁, ha₂.trans ha₁, fun b hb => ?_⟩
  rw [hT₂ b (by rw [hp₁, ha₁]; exact hb), hT₁ b hb]

/-- The second definition implements the first: the tree `T` with pointer `p` (and the direction
`aim`) satisfies all the axioms of program-tree theory. -/
def impl : ProgramTreeTheory X (St X) where
  node := node
  aim := St.aim
  assignNode := change
  assignAim := assignAim
  go := go
  work := work
  aim_go := aim_go
  go_work_go := go_work_go
  work_ok := work_ok
  work_assignNode := work_change
  work_turn := work_turn
  work_work := work_work

/-- The book's opening example: `aim:= up. go` and "then look at `aim` to see where we came
from" — from the origin we came from the left. -/
theorem example_origin (T : Pos → X) :
    seq (assignAim Dir.up) go ⟨T, Pos.origin, Dir.left⟩ ⟨T, Pos.origin.up, Dir.left⟩ :=
  ⟨_, rfl, rfl⟩

end ProgramTree

end LaPToP.TheoryDesign
