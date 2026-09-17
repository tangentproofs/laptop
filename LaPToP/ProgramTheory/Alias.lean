import LaPToP.ProgramTheory.Specifications

/-!
# Alias

This module formalizes Section 5.6 (Alias) of Eric Hehner's *A Practical
Theory of Programming* (aPToP), pp. 83–84.

"Many popular programming languages present us with a model of computation
in which there is a memory consisting of a large number of individual storage
cells. Each cell contains a value. Via the programming language, cells have
names. ... `p` is a pointer variable that currently points to array element
`A 1`, and `*p` is `p` dereferenced; so `*p` and `A 1` refer to the same memory
cell. ... We see that a cell may have zero, one, two, or more names. When a
cell has two or more names that are visible at the same time, the names are
said to be “aliases”. As we have seen with arrays, with value expressions, and
with variable parameters, aliasing prevents us from applying our theory of
programming; neither the definition of assignment nor the substitution law
work. Chapter 4 introduced our computing model with the deterministic function
`address` that maps different names to different addresses, saying where each
state variable is. But aliasing maps more than one name to an address,
breaking the model. ... If we redraw our picture slightly, we see that there
are two mappings: one from names to cells, and one from cells to values. An
assignment such as `p:= (address of A 3)` or `i:= 4` can change both mappings
at once. An assignment to one name can change the value indirectly referred to
by another name. To simplify the picture and eliminate the possibility of
aliasing, we eliminate the cells and allow a richer space of values. ...
Pointer variables can be replaced by index variables dedicated to one
structure so that they can be implemented as addresses. Variable parameters
are unnecessary if functions can return structured values. The simpler picture
is perfectly adequate, and the problem of aliasing disappears."

## The model

`Memory Name Cell Val` is the book's second picture: two mappings, `addr`
from names to cells and `store` from cells to values. Assignment through a
name updates the cell it names; a pointer assignment (`retarget`) changes
`addr`. `Aliased m n₁ n₂` says two distinct names share a cell. Proved: an
assignment to one alias changes the value read through the other; hence on a
concrete two-name, one-cell memory both the Chapter 4 definition of
assignment (`x:= e = x′=e ∧ y′=y`) and the Substitution Law fail. Without
aliases (`addr` injective) the assignment law holds, and the alias-free
picture — "eliminate the cells", `Cell := Name`, `addr := id` — is exactly the
state `State Name Val` of Chapter 4 (`toMemory`), on which `assign_iff` and
`assign_seq` hold. The `A i := e` reading via `A := i → e | A` is the array
model of Section 5.1 and is not repeated here.
-/

namespace LaPToP.ProgramTheory

namespace Alias

open Spec

universe u v w

/-- The two-mapping picture: names to cells, cells to values. -/
structure Memory (Name : Type u) (Cell : Type v) (Val : Type w) where
  /-- Which cell each name refers to. -/
  addr : Name → Cell
  /-- The value in each cell. -/
  store : Cell → Val

variable {Name : Type u} {Cell : Type v} {Val : Type w}

namespace Memory

variable (m : Memory Name Cell Val)

/-- The value referred to by a name. -/
def read (n : Name) : Val := m.store (m.addr n)

/-- Assignment through a name: the cell it refers to gets the value. -/
def assign [DecidableEq Cell] (n : Name) (v : Val) : Memory Name Cell Val :=
  { m with store := Function.update m.store (m.addr n) v }

/-- `p:= (address of …)`: a pointer assignment changes the first mapping. -/
def retarget [DecidableEq Name] (p : Name) (c : Cell) : Memory Name Cell Val :=
  { m with addr := Function.update m.addr p c }

/-- "When a cell has two or more names that are visible at the same time, the names are said to
be “aliases”." -/
def Aliased (n₁ n₂ : Name) : Prop := n₁ ≠ n₂ ∧ m.addr n₁ = m.addr n₂

theorem read_assign_self [DecidableEq Cell] (n : Name) (v : Val) : (m.assign n v).read n = v := by
  simp [read, assign]

/-- Reading through a name whose cell is not the assigned one is unchanged. -/
theorem read_assign_of_addr_ne [DecidableEq Cell] {n₁ n₂ : Name} (h : m.addr n₁ ≠ m.addr n₂) (v : Val) :
    (m.assign n₁ v).read n₂ = m.read n₂ := by
  simp [read, assign, Function.update_of_ne (Ne.symm h)]

/-- "An assignment to one name can change the value indirectly referred to by another name." -/
theorem read_assign_alias [DecidableEq Cell] {n₁ n₂ : Name} (h : m.Aliased n₁ n₂) (v : Val) :
    (m.assign n₁ v).read n₂ = v := by
  simp [read, assign, h.2]

/-- After `p:= (address of a)`, `*p` and `a` are aliases. -/
theorem aliased_retarget [DecidableEq Name] {p a : Name} (h : p ≠ a) : (m.retarget p (m.addr a)).Aliased p a := by
  refine ⟨h, ?_⟩
  simp [retarget, Function.update_of_ne (Ne.symm h)]

/-- The Chapter 4 model: "the deterministic function `address` that maps different names to
different addresses" — no aliases iff `addr` is injective. -/
theorem no_alias_iff_injective : (∀ n₁ n₂, ¬ m.Aliased n₁ n₂) ↔ Function.Injective m.addr := by
  constructor
  · intro h n₁ n₂ heq
    by_contra hne
    exact h n₁ n₂ ⟨hne, heq⟩
  · rintro hinj n₁ n₂ ⟨hne, heq⟩
    exact hne (hinj heq)

/-- Without aliases, the Chapter 4 assignment law `y′ = y` holds for every other name. -/
theorem read_assign_of_injective [DecidableEq Cell] (hinj : Function.Injective m.addr) {n₁ n₂ : Name} (h : n₁ ≠ n₂) (v : Val) :
    (m.assign n₁ v).read n₂ = m.read n₂ :=
  m.read_assign_of_addr_ne (fun heq => h (hinj heq)) v

end Memory

/-! ### Aliasing breaks the theory (a two-name, one-cell memory) -/

/-- Assignment through a name as a specification, `n:= v`. -/
def assignSpec [DecidableEq Cell] (n : Name) (v : Val) : Spec (Memory Name Cell Val) :=
  fun m m' => m' = m.assign n v

/-- The binary expression `n = v` of the prestate, as a specification (nothing said about the
poststate). -/
def readEq (n : Name) (v : Val) : Spec (Memory Name Cell Val) := fun m _ => m.read n = v

/-- Two names, one cell: `true` and `false` both refer to the single cell `()`, which holds `0`. -/
def twoNames : Memory Bool Unit ℤ := ⟨fun _ => (), fun _ => 0⟩

theorem twoNames_aliased : twoNames.Aliased true false := ⟨Bool.noConfusion, rfl⟩

/-- "Neither the definition of assignment ... work": `x:= e = x′=e ∧ y′=y ∧ ...` fails, since
`true:= 1` changes the value read through `false`. -/
theorem assign_law_fails : ¬ ∀ m m' : Memory Bool Unit ℤ, assignSpec true 1 m m' → m'.read false = m.read false := by
  intro h
  have := h twoNames _ rfl
  rw [Memory.read_assign_alias _ twoNames_aliased] at this
  simp [twoNames, Memory.read] at this

/-- "... nor the substitution law": `true:= 1. (false = 1)` should, by substitution (`true` does
not occur in `false = 1`), equal `false = 1`; but it is `⊤` on the aliased memory. -/
theorem substitution_law_fails : seq (assignSpec true 1) (readEq false 1) ≠ (readEq false 1 : Spec (Memory Bool Unit ℤ)) := by
  intro h
  have h1 : seq (assignSpec true 1) (readEq false 1) twoNames twoNames :=
    ⟨_, rfl, Memory.read_assign_alias _ twoNames_aliased 1⟩
  rw [h] at h1
  simp [readEq, twoNames, Memory.read] at h1

/-! ### The alias-free picture is the Chapter 4 state -/

/-- "We eliminate the cells": every name is its own cell, and the memory is the state
`State Name Val` of Chapter 4. -/
def toMemory (s : State Name Val) : Memory Name Name Val := ⟨id, s⟩

theorem toMemory_read (s : State Name Val) (n : Name) : (toMemory s).read n = s n := rfl

/-- Assignment in the alias-free memory is the Chapter 4 assignment `σ′ = σ⊲address “x”⊳e`. -/
theorem toMemory_assign [DecidableEq Name] (s : State Name Val) (n : Name) (v : Val) :
    (toMemory s).assign n v = toMemory (Function.update s n v) := rfl

/-- There are no aliases in the alias-free picture. -/
theorem toMemory_not_aliased (s : State Name Val) (n₁ n₂ : Name) : ¬ (toMemory s).Aliased n₁ n₂ :=
  fun h => h.1 h.2

/-- The Chapter 4 assignment law holds: `x:= e = x′=e ∧ y′=y ∧ ...` (`Spec.assign_iff`). -/
theorem alias_free_assign_law [DecidableEq Name] (x : Name) (e : State Name Val → Val) (s s' : State Name Val) :
    assign x e s s' ↔ s' x = e s ∧ ∀ y, y ≠ x → s' y = s y :=
  assign_iff x e s s'

/-- ... and so does the Substitution Law (`Spec.assign_seq`). -/
theorem alias_free_substitution_law [DecidableEq Name] (x : Name) (e : State Name Val → Val) (P : Spec (State Name Val)) :
    seq (assign x e) P = fun s s' => P (Function.update s x (e s)) s' :=
  assign_seq x e P

end Alias

end LaPToP.ProgramTheory
