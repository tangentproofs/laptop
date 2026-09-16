import LaPToP.TheoryDesign.DataTransformation
import Mathlib.Data.List.Basic

/-!
# Parsing

This module formalizes Section 7.2.2 (Parsing) of Eric Hehner's *A Practical
Theory of Programming* (aPToP), Exercise 451.

"Define `E` as a bunch of strings of lists of characters satisfying
`E = [“x”], [“if”]; E; [“then”]; E; [“else”]; E; [“fi”]`. Given a string of
lists of characters, write a program to determine if the string is in the
bunch `E`. ... Let the given string be `s` (a constant). ... we introduce
natural variable `n`, increasing from `0` to at most `↔s`, indicating how much
of `s` we have parsed. ... We can express the result as the final value of
binary variable `q`. ... We assume that `s` ends with the sentinel `[“eos”]`
(end of string) ... and ... we will add the sentinel `[“eog”]` (end of
grammar) to the end of every string." After two data transformations
("the data transformer is, informally, `A = (b with all occurrences of item
[“E”] replaced by bunch E)`", then `b = s0;..n;c`) the book arrives at

    q′ = (s0;..↔s–1 : E) ⇐ c:= [“x”];[“eog”]. n:= 0. R
    R ⇐ if sn=c0 then c:= c1;..↔c. n:= n+1. R
        else if c0=[“x”] ∧ sn=[“if”]
             then c:= [“x”];[“then”];[“x”];[“else”];[“x”];[“fi”];c1;..↔c. n:= n+1. R
             else q:= c0=[“eog”] ∧ sn=[“eos”]

## The model

The items are tokens `Tok`; strings are lists of tokens. `E` is defined
inductively. The specification `R` — the result of the two transformations,
which the book computes informally — is stated directly: `R` says that `q′`
is whether the rest of the input `s n;..↔s` is one of the strings represented
by `c`, where `c` represents the strings obtained by replacing each item
`[“x”]` by a string of `E`, with `[“eog”]` standing for `[“eos”]` (`Cands`).
The book's final program is proved to refine `R` (the recursive call taken
as a specification, Section 6.1), and `q′ = (s0;..↔s–1 : E)` is proved to be
refined by `c:= [“x”];[“eog”]. n:= 0. R`, under the sentinel assumptions:
`[“eos”]` occurs in `s` only at the end, `[“eog”]` does not occur in `s`, and
(as an antecedent of `R`) `[“eog”]` occurs in `c` only at the end.

What is *not* formalized: the bunch-valued variable `A`, the intermediate
program with `b`, and the two data transformers, which the book gives
informally and whose refinements it omits ("we omit the proofs of these
refinements in order to pursue our current topic"). What is proved is that
the final program meets the original specification, which is what the
transformations are for. The printed line `c:= …;[“fi”]c` is read as
`c:= [“x”];[“then”];[“x”];[“else”];[“x”];[“fi”];c1;..↔c` (the `[“x”]` at `c0`
is what is being expanded).
-/

namespace LaPToP.TheoryDesign

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

namespace Parsing

open Spec

/-- The items: the lists of characters `[“x”]`, `[“if”]`, `[“then”]`, `[“else”]`,
`[“fi”]`, the sentinels `[“eos”]`, `[“eog”]`, and any other item. -/
inductive Tok where
  /-- `[“x”]`. -/
  | x
  /-- `[“if”]`. -/
  | ifT
  /-- `[“then”]`. -/
  | thenT
  /-- `[“else”]`. -/
  | elseT
  /-- `[“fi”]`. -/
  | fiT
  /-- The end-of-string sentinel `[“eos”]`. -/
  | eos
  /-- The end-of-grammar sentinel `[“eog”]`. -/
  | eog
  /-- Any other list of characters, numbered. -/
  | other (k : ℕ)
  deriving DecidableEq

/-- `E = [“x”], [“if”]; E; [“then”]; E; [“else”]; E; [“fi”]`, the least solution. -/
inductive E : List Tok → Prop where
  /-- `[“x”] : E`. -/
  | x : E [.x]
  /-- `[“if”]; E; [“then”]; E; [“else”]; E; [“fi”] : E`. -/
  | ite {a b c : List Tok} : E a → E b → E c → E (.ifT :: (a ++ .thenT :: (b ++ .elseT :: (c ++ [.fiT]))))

/-- A string of `E` begins with `[“x”]` or `[“if”]`. -/
theorem E.head {e : List Tok} (h : E e) : e.head? = some .x ∨ e.head? = some .ifT := by
  cases h <;> simp

/-- The only string of `E` beginning with `[“x”]` is `[“x”]`. -/
theorem E_x_cons_iff (t : List Tok) : E (.x :: t) ↔ t = [] := by
  constructor
  · intro h
    generalize hx : (Tok.x :: t) = e at h
    cases h with
    | x => simpa using hx
    | ite _ _ _ => simp at hx
  · rintro rfl
    exact E.x

/-- A string of `E` beginning with `[“if”]` is `[“if”]; a; [“then”]; b; [“else”]; c; [“fi”]`. -/
theorem E_if_cons_iff (t : List Tok) :
    E (.ifT :: t) ↔ ∃ a b c, E a ∧ E b ∧ E c ∧ t = a ++ .thenT :: (b ++ .elseT :: (c ++ [.fiT])) := by
  constructor
  · intro h
    generalize hx : (Tok.ifT :: t) = e at h
    cases h with
    | x => simp at hx
    | ite ha hb hc =>
      simp only [List.cons.injEq, true_and] at hx
      exact ⟨_, _, _, ha, hb, hc, hx⟩
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    exact E.ite ha hb hc

/-- `Cands c t`: the string `t` is one of the strings represented by `c` — `c`
"with all occurrences of item `[“x”]` replaced by bunch `E`", and with the
sentinel `[“eog”]` standing for the input's sentinel `[“eos”]`. -/
inductive Cands : List Tok → List Tok → Prop where
  /-- The empty string represents itself. -/
  | nil : Cands [] []
  /-- `[“x”]` stands for any string of `E`. -/
  | x {c e t : List Tok} : E e → Cands c t → Cands (.x :: c) (e ++ t)
  /-- `[“eog”]` stands for `[“eos”]`. -/
  | eog {c t : List Tok} : Cands c t → Cands (.eog :: c) (.eos :: t)
  /-- Any other item stands for itself. -/
  | tok {a : Tok} {c t : List Tok} (h : a ≠ .x) (h' : a ≠ .eog) : Cands c t → Cands (a :: c) (a :: t)

theorem cands_nil_iff (t : List Tok) : Cands [] t ↔ t = [] := by
  constructor
  · intro h
    generalize hc : ([] : List Tok) = c at h
    cases h <;> simp_all
  · rintro rfl
    exact Cands.nil

theorem cands_x_cons_iff (c t : List Tok) : Cands (.x :: c) t ↔ ∃ e t', E e ∧ Cands c t' ∧ t = e ++ t' := by
  constructor
  · intro h
    generalize hc : (Tok.x :: c) = c₀ at h
    cases h with
    | nil => simp at hc
    | x he hc' =>
      simp only [List.cons.injEq, true_and] at hc
      subst hc
      exact ⟨_, _, he, hc', rfl⟩
    | eog _ => simp at hc
    | tok h _ _ => simp only [List.cons.injEq] at hc; exact absurd hc.1.symm h
  · rintro ⟨e, t', he, hc, rfl⟩
    exact Cands.x he hc

theorem cands_eog_cons_iff (c t : List Tok) : Cands (.eog :: c) t ↔ ∃ t', t = .eos :: t' ∧ Cands c t' := by
  constructor
  · intro h
    generalize hc : (Tok.eog :: c) = c₀ at h
    cases h with
    | nil => simp at hc
    | x _ _ => simp at hc
    | eog hc' =>
      simp only [List.cons.injEq, true_and] at hc
      subst hc
      exact ⟨_, rfl, hc'⟩
    | tok _ h' _ => simp only [List.cons.injEq] at hc; exact absurd hc.1.symm h'
  · rintro ⟨t', rfl, hc⟩
    exact Cands.eog hc

theorem cands_tok_cons_iff {a : Tok} (ha : a ≠ .x) (ha' : a ≠ .eog) (c t : List Tok) :
    Cands (a :: c) t ↔ ∃ t', t = a :: t' ∧ Cands c t' := by
  constructor
  · intro h
    generalize hc : (a :: c) = c₀ at h
    cases h with
    | nil => simp at hc
    | x _ _ => simp only [List.cons.injEq] at hc; exact absurd hc.1 ha
    | eog _ => simp only [List.cons.injEq] at hc; exact absurd hc.1 ha'
    | tok _ _ hc' =>
      simp only [List.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨_, rfl, hc'⟩
  · rintro ⟨t', rfl, hc⟩
    exact Cands.tok ha ha' hc

/-! ### The LL(1) lemmas: what the first item of the input decides -/

/-- `[“x”]` at the head of `c` against `[“x”]` in the input: consume it. -/
theorem cands_x_x (c t : List Tok) : Cands (.x :: c) (.x :: t) ↔ Cands c t := by
  rw [cands_x_cons_iff]
  constructor
  · rintro ⟨e, t', he, hc, ht⟩
    rcases he.head with hh | hh
    · obtain ⟨e', rfl⟩ : ∃ e', e = .x :: e' := by
        cases e with
        | nil => simp at hh
        | cons a e' => simp only [List.head?_cons, Option.some.injEq] at hh; exact ⟨e', by rw [hh]⟩
      rw [E_x_cons_iff] at he
      subst he
      simp only [List.singleton_append, List.cons.injEq, true_and] at ht
      exact ht ▸ hc
    · cases e with
      | nil => simp at hh
      | cons a e' =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        simp at ht
  · intro h
    exact ⟨[.x], t, E.x, h, rfl⟩

/-- `[“x”]` at the head of `c` against `[“if”]` in the input: expand. -/
theorem cands_x_if (c t : List Tok) :
    Cands (.x :: c) (.ifT :: t) ↔ Cands (.x :: .thenT :: .x :: .elseT :: .x :: .fiT :: c) t := by
  constructor
  · intro h
    rw [cands_x_cons_iff] at h
    obtain ⟨e, t', he, hc, ht⟩ := h
    rcases he.head with hh | hh
    · cases e with
      | nil => simp at hh
      | cons a e' =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        simp at ht
    · obtain ⟨e', rfl⟩ : ∃ e', e = .ifT :: e' := by
        cases e with
        | nil => simp at hh
        | cons a e' => simp only [List.head?_cons, Option.some.injEq] at hh; exact ⟨e', by rw [hh]⟩
      rw [E_if_cons_iff] at he
      obtain ⟨a, b, d, ha, hb, hd, rfl⟩ := he
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      subst ht
      have := Cands.x ha (Cands.tok (a := .thenT) (by decide) (by decide) (Cands.x hb
        (Cands.tok (a := .elseT) (by decide) (by decide) (Cands.x hd (Cands.tok (a := .fiT) (by decide) (by decide) hc)))))
      simpa [List.append_assoc] using this
  · intro h
    rw [cands_x_cons_iff] at h
    obtain ⟨a, t₁, ha, h, rfl⟩ := h
    rw [cands_tok_cons_iff (by decide) (by decide)] at h
    obtain ⟨t₂, rfl, h⟩ := h
    rw [cands_x_cons_iff] at h
    obtain ⟨b, t₃, hb, h, rfl⟩ := h
    rw [cands_tok_cons_iff (by decide) (by decide)] at h
    obtain ⟨t₄, rfl, h⟩ := h
    rw [cands_x_cons_iff] at h
    obtain ⟨d, t₅, hd, h, rfl⟩ := h
    rw [cands_tok_cons_iff (by decide) (by decide)] at h
    obtain ⟨t₆, rfl, h⟩ := h
    have := Cands.x (E.ite ha hb hd) h
    simpa [List.append_assoc] using this

/-- `[“x”]` at the head of `c` requires `[“x”]` or `[“if”]` at the head of the input. -/
theorem cands_x_head {c t : List Tok} {b : Tok} (h : Cands (.x :: c) (b :: t)) : b = .x ∨ b = .ifT := by
  rw [cands_x_cons_iff] at h
  obtain ⟨e, t', he, -, ht⟩ := h
  cases e with
  | nil => rcases he.head with hh | hh <;> simp at hh
  | cons a e' =>
    simp only [List.cons_append, List.cons.injEq] at ht
    rcases he.head with hh | hh <;> simp only [List.head?_cons, Option.some.injEq] at hh <;> subst hh
    · exact Or.inl ht.1
    · exact Or.inr ht.1

/-- `[“eog”]` against `[“eos”]`. -/
theorem cands_eog_eos (c t : List Tok) : Cands (.eog :: c) (.eos :: t) ↔ Cands c t := by
  rw [cands_eog_cons_iff]
  constructor
  · rintro ⟨t', ht, hc⟩
    simp only [List.cons.injEq, true_and] at ht
    exact ht ▸ hc
  · exact fun h => ⟨t, rfl, h⟩

/-- A nonempty `c` represents no empty string. -/
theorem not_cands_cons_nil (a : Tok) (c : List Tok) : ¬ Cands (a :: c) [] := by
  intro h
  generalize hc : (a :: c) = c₀ at h
  generalize ht : ([] : List Tok) = t at h
  cases h with
  | nil => simp at hc
  | x he _ =>
    have := (List.append_eq_nil_iff.mp ht.symm).1
    subst this
    rcases he.head with hh | hh <;> simp at hh
  | eog _ => simp at ht
  | tok _ _ _ => simp at ht

/-! ### Sentinels -/

/-- `[“eog”]` occurs in `c` only at the end. -/
def SentC (c : List Tok) : Prop := ∀ c₁ c₂, c = c₁ ++ .eog :: c₂ → c₂ = []

theorem SentC.tail {a : Tok} {c : List Tok} (h : SentC (a :: c)) : SentC c :=
  fun c₁ c₂ hc => h (a :: c₁) c₂ (by rw [hc]; rfl)

theorem SentC.eog_cons {c : List Tok} (h : SentC (.eog :: c)) : c = [] := h [] c rfl

/-- Prepending items other than `[“eog”]` preserves the sentinel property. -/
theorem SentC.prepend {l c : List Tok} (hl : .eog ∉ l) (h : SentC c) : SentC (l ++ c) := by
  intro c₁ c₂ hc
  rcases List.append_eq_append_iff.mp hc with ⟨as, rfl, hc'⟩ | ⟨bs, rfl, hc'⟩
  · exact h as c₂ hc'
  · cases bs with
    | nil =>
      simp only [List.nil_append] at hc'
      exact h [] c₂ (by simpa using hc'.symm)
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at hc'
      refine absurd ?_ hl
      rw [hc'.1]
      exact List.mem_append_right _ (List.mem_cons_self ..)

/-- `[“eos”]` occurs in `s` only at the end, and `[“eog”]` does not occur in `s`. -/
def SentS (s : List Tok) : Prop := (∀ s₁ s₂, s = s₁ ++ .eos :: s₂ → s₂ = []) ∧ .eog ∉ s

/-- After the sentinel `[“eos”]` at index `n` nothing remains. -/
theorem SentS.drop_succ_eq_nil {s : List Tok} (hs : SentS s) {n : ℕ} (hn : s[n]? = some .eos) :
    s.drop (n + 1) = [] := by
  have hlt : n < s.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hn
    cases hn
  apply hs.1 (s.take n)
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hn
  rw [← hn, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]

theorem SentS.ne_eog {s : List Tok} (hs : SentS s) (n : ℕ) : s[n]? ≠ some .eog := by
  intro h
  exact hs.2 (List.mem_of_getElem? h)

/-! ### The program -/

/-- The state: the index `n`, the string `c`, and the result `q`. -/
structure PS where
  /-- How much of `s` has been parsed. -/
  n : ℕ
  /-- The string representing the candidates still in contention. -/
  c : List Tok
  /-- The result. -/
  q : Prop

/-- `n:= e`. -/
def assignN (e : PS → ℕ) : Spec PS := fun st st' => st' = { st with n := e st }

/-- `c:= e`. -/
def assignC (e : PS → List Tok) : Spec PS := fun st st' => st' = { st with c := e st }

/-- `q:= e`. -/
def assignQ (e : PS → Prop) : Spec PS := fun st st' => st' = { st with q := e st }

theorem assignN_seq (e : PS → ℕ) (P : Spec PS) : seq (assignN e) P = fun st st' => P { st with n := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

theorem assignC_seq (e : PS → List Tok) (P : Spec PS) :
    seq (assignC e) P = fun st st' => P { st with c := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (s : List Tok)

/-- The specification `R`: if `[“eog”]` occurs in `c` only at the end, then `q′` says
whether the rest of the input, `s n;..↔s`, is a string represented by `c`. -/
def R : Spec PS := fun st st' => SentC st.c → (st'.q ↔ Cands st.c (s.drop st.n))

/-- `[“x”];[“then”];[“x”];[“else”];[“x”];[“fi”]`. -/
def expansion : List Tok := [.x, .thenT, .x, .elseT, .x, .fiT]

/-- The book's program for `R`, with the recursive call `R` taken as a specification:
`if sn=c0 then c:= c1;..↔c. n:= n+1. R else if c0=[“x”] ∧ sn=[“if”] then
c:= [“x”];[“then”];[“x”];[“else”];[“x”];[“fi”];c1;..↔c. n:= n+1. R else q:= c0=[“eog”] ∧ sn=[“eos”]`. -/
def Rprog (Rc : Spec PS) : Spec PS :=
  cond (fun st => s[st.n]? = st.c.head?)
    (seq (assignC fun st => st.c.tail) (seq (assignN fun st => st.n + 1) Rc))
    (cond (fun st => st.c.head? = some .x ∧ s[st.n]? = some .ifT)
      (seq (assignC fun st => expansion ++ st.c.tail) (seq (assignN fun st => st.n + 1) Rc))
      (assignQ fun st => st.c.head? = some .eog ∧ s[st.n]? = some .eos))

/-- `R ⇐ (the book's program)`, for an input `s` satisfying the sentinel assumptions. -/
theorem R_refines (hs : SentS s) : Refines (R s) (Rprog s (R s)) := by
  rintro ⟨n, c, q⟩ st' h hsent
  simp only at hsent
  show st'.q ↔ Cands c (s.drop n)
  rcases h with ⟨heq, h⟩ | ⟨hne, (⟨⟨hx, hif⟩, h⟩ | ⟨hnot, rfl⟩)⟩
  · -- `sn = c0`: consume
    rw [assignC_seq, assignN_seq] at h
    simp only [R] at h heq
    cases c with
    | nil =>
      simp only [List.head?_nil] at heq
      have hlen : s.length ≤ n := by
        by_contra hlt
        rw [List.getElem?_eq_getElem (Nat.lt_of_not_le hlt)] at heq
        cases heq
      rw [h (fun _ _ h => by simp_all), List.tail_nil, List.drop_eq_nil_of_le hlen,
        List.drop_eq_nil_of_le (Nat.le_succ_of_le hlen)]
    | cons a c =>
      simp only [List.head?_cons] at heq
      have hlt : n < s.length := by
        by_contra hlt
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at heq
        cases heq
      have heq' : s[n] = a := by
        rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at heq
        exact heq
      rw [List.drop_eq_getElem_cons hlt, heq', h hsent.tail, List.tail_cons]
      by_cases hax : a = .x
      · subst hax
        exact (cands_x_x c _).symm
      by_cases haeog : a = .eog
      · subst haeog
        exact absurd heq (hs.ne_eog n)
      · rw [cands_tok_cons_iff hax haeog]
        constructor
        · exact fun hc => ⟨_, rfl, hc⟩
        · rintro ⟨t', ht, hc⟩
          simp only [List.cons.injEq, true_and] at ht
          exact ht ▸ hc
  · -- `c0 = [“x”] ∧ sn = [“if”]`: expand
    rw [assignC_seq, assignN_seq] at h
    simp only [R] at h hx hif
    cases c with
    | nil => simp at hx
    | cons a c =>
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst hx
      have hlt : n < s.length := by
        by_contra hlt
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hif
        cases hif
      have hif' : s[n] = .ifT := by
        rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hif
        exact hif
      rw [List.drop_eq_getElem_cons hlt, hif', h (hsent.tail.prepend (by decide)), List.tail_cons, cands_x_if]
      rfl
  · -- otherwise `q:= c0=[“eog”] ∧ sn=[“eos”]`
    simp only at hne
    show (c.head? = some .eog ∧ s[n]? = some .eos) ↔ Cands c (s.drop n)
    cases c with
    | nil =>
      simp only [List.head?_nil] at hne ⊢
      have hlt : n < s.length := by
        by_contra hlt
        exact hne (List.getElem?_eq_none (Nat.le_of_not_lt hlt))
      rw [List.drop_eq_getElem_cons hlt, cands_nil_iff]
      simp [hlt]
    | cons a c =>
      simp only [List.head?_cons] at hne ⊢
      by_cases hlt : n < s.length
      · rw [List.drop_eq_getElem_cons hlt]
        rw [List.getElem?_eq_getElem hlt] at hne ⊢
        have hne' : s[n] ≠ a := fun h => hne (congrArg some h)
        by_cases haeog : a = .eog
        · subst haeog
          have hc := hsent.eog_cons
          subst hc
          constructor
          · rintro ⟨-, hn⟩
            rw [Option.some.injEq] at hn
            rw [hn, cands_eog_eos, cands_nil_iff]
            exact hs.drop_succ_eq_nil (by rw [List.getElem?_eq_getElem hlt, hn])
          · intro hc
            rw [cands_eog_cons_iff] at hc
            obtain ⟨t', ht, -⟩ := hc
            simp only [List.cons.injEq] at ht
            exact ⟨rfl, by rw [ht.1]⟩
        · constructor
          · rintro ⟨h1, -⟩
            exact absurd (Option.some.inj h1) haeog
          · intro hc
            exfalso
            by_cases hax : a = .x
            · subst hax
              rcases cands_x_head hc with h1 | h1
              · exact hne' h1
              · exact hnot ⟨rfl, by rw [List.getElem?_eq_getElem hlt, h1]⟩
            · rw [cands_tok_cons_iff hax haeog] at hc
              obtain ⟨t', ht, -⟩ := hc
              simp only [List.cons.injEq] at ht
              exact hne' ht.1
      · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hlt)]
        simp only [reduceCtorEq, and_false, false_iff]
        exact not_cands_cons_nil _ _

/-- `Cands [“x”];[“eog”] s = (s0;..↔s–1 : E)` for `s = s0;..↔s–1; [“eos”]`. -/
theorem cands_init_iff (s₀ : List Tok) : Cands [.x, .eog] (s₀ ++ [.eos]) ↔ E s₀ := by
  rw [cands_x_cons_iff]
  constructor
  · rintro ⟨e, t', he, hc, ht⟩
    rw [cands_eog_cons_iff] at hc
    obtain ⟨t'', rfl, hc⟩ := hc
    rw [cands_nil_iff] at hc
    subst hc
    exact (List.append_cancel_right ht).symm ▸ he
  · intro he
    exact ⟨s₀, [.eos], he, Cands.eog Cands.nil, rfl⟩

/-- `q′ = (s0;..↔s–1 : E) ⇐ c:= [“x”];[“eog”]. n:= 0. R`, for the input `s = s0;..↔s–1; [“eos”]`
(the sentinel assumptions on `s` are needed for `R_refines`, not here). -/
theorem parse_refines (s₀ : List Tok) :
    Refines (fun _ st' : PS => st'.q ↔ E s₀)
      (seq (assignC fun _ => [.x, .eog]) (seq (assignN fun _ => 0) (R (s₀ ++ [.eos])))) := by
  intro st st' h
  rw [assignC_seq, assignN_seq] at h
  have := h (by
    intro c₁ c₂ hc
    rcases c₁ with _ | ⟨a, _ | ⟨b, c₁⟩⟩ <;> simp_all)
  simp only [List.drop_zero] at this
  rw [this, cands_init_iff]

/-- The whole solution: for an input `s0;..↔s–1; [“eos”]` satisfying the sentinel
assumptions, `q′ = (s0;..↔s–1 : E)` is refined by `c:= [“x”];[“eog”]. n:= 0. R` where
`R` is refined by the book's program (Refinement by Steps). -/
theorem parse_program_refines (s₀ : List Tok) (hs : SentS (s₀ ++ [.eos])) :
    Refines (fun _ st' : PS => st'.q ↔ E s₀)
      (seq (assignC fun _ => [.x, .eog])
        (seq (assignN fun _ => 0) (Rprog (s₀ ++ [.eos]) (R (s₀ ++ [.eos]))))) :=
  refines_trans _ _ _ (parse_refines s₀)
    (refines_seq_mono (refines_refl _) (refines_seq_mono (refines_refl _) (R_refines _ hs)))

end Parsing

end LaPToP.TheoryDesign
