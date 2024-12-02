/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.CountingSteps

namespace ContextFreeGrammar

variable {T : Type}
variable {g : ContextFreeGrammar T}

abbrev NullableNonTerminal (v : g.NT) : Prop := g.Derives [Symbol.nonterminal v] []

abbrev NullableWord (w : List (Symbol T g.NT)) : Prop := g.Derives w []

-- Properties of NullableNonTerminal, NullableWord and Derives/Produces/Rewrites to empty
lemma NullableWord.empty_of_append {w u v: List (Symbol T g.NT)}
  (hwe : NullableWord (w ++ u ++ v)) : NullableWord u := by
  unfold NullableWord at *
  rw [derives_iff_derivesIn] at hwe ⊢
  obtain ⟨n, hwe⟩ := hwe
  obtain ⟨m, _, hue⟩ := hwe.empty_of_append
  use m

lemma NullableWord.empty_of_append_left {u v: List (Symbol T g.NT)}
  (hwe : NullableWord (u ++ v)) : NullableWord u := by
  apply @NullableWord.empty_of_append _ _ []
  exact hwe

lemma NullableWord.empty_of_append_right {u v: List (Symbol T g.NT)}
  (hwe : NullableWord (u ++ v) ): NullableWord v := by
  apply @NullableWord.empty_of_append _ _ _ _ []
  simp
  exact hwe

lemma DerivesIn.mem_nullable {w : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ}
  (h: g.DerivesIn w [] n) (hin: s ∈ w) : ∃ m ≤ n, g.DerivesIn [s] [] m := by
  revert n
  induction w with
  | nil => contradiction
  | cons v t ih =>
    intro n h
    cases hin with
    | head =>
      change g.DerivesIn ([s] ++ t) [] n at h
      exact DerivesIn.empty_of_append_left h
    | tail _ hs =>
      change g.DerivesIn ([v] ++ t) [] n at h
      obtain ⟨m, hmn, hte⟩ := DerivesIn.empty_of_append_right h
      obtain ⟨m', hm'm,hse⟩ := ih hs hte
      use m'
      exact ⟨Nat.le_trans hm'm hmn, hse⟩

lemma rewrites_empty_output {v : List (Symbol T g.NT)} {r : ContextFreeRule T g.NT} (h : r.Rewrites v []) :
  r.output = [] := by
  obtain ⟨p,q,_,h2⟩ := h.exists_parts
  simp at h2
  tauto

lemma Derives.append_left_trans {v w x y: List (Symbol T g.NT)}
    (hvw : g.Derives v w) (hxy : g.Derives x y) :
    g.Derives (x ++ v) (y ++ w) := by
    apply Derives.trans
    exact Derives.append_left hvw _
    exact Derives.append_right hxy _

lemma rewrites_produces {r : ContextFreeRule T g.NT} (h : r ∈ g.rules) :
  g.Produces [Symbol.nonterminal r.input] r.output := by
  use r
  constructor
  exact h
  rw [r.rewrites_iff]
  use [], []
  simp

lemma nullable_not_terminal {t : T} {w : List (Symbol T g.NT)} : ¬ NullableWord (Symbol.terminal t :: w) := by
  by_contra h
  change g.Derives ([Symbol.terminal t] ++ w) [] at h
  apply NullableWord.empty_of_append_left at h
  obtain ⟨⟩ := h.eq_or_head
  · contradiction
  · rename_i h
    obtain ⟨w, h1, h2⟩ := h
    unfold Produces at h1
    obtain ⟨r, _, hr⟩ := h1
    cases hr
    rename_i hrs
    cases hrs

lemma Derives.empty_empty {w : List (Symbol T g.NT)} (h : g.Derives [] w) : w = [] := by
  induction h with
  | refl => rfl
  | tail hd hp ih =>
    unfold Produces at hp
    obtain ⟨r, _, hr⟩ := hp
    cases hr <;> contradiction

lemma symbols_nullable_nullableWord (w : List (Symbol T g.NT)) (h: ∀ v ∈ w, g.Derives [v] []) :
  NullableWord w := by
  induction w with
  | nil => exact Derives.refl []
  | cons hd tl ih =>
    change g.Derives ([hd] ++ tl) []
    apply Derives.trans
    · apply Derives.append_right
      apply h
      exact List.mem_cons_self hd tl
    · simp
      apply ih
      intro v hv
      apply h
      right
      exact hv

lemma DerivesIn.nullable_mem_nonterminal {w : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ}
  (hwe: g.DerivesIn w [] n) (hin: s ∈ w) : ∃ v, s = Symbol.nonterminal v := by
  have ⟨m, hmn, hse⟩ := hwe.mem_nullable hin
  cases m with
  | zero =>
    contradiction
  | succ m =>
    obtain ⟨u, hwu, _⟩ := hse.head_of_succ
    obtain ⟨r, _, hsu⟩ := hwu
    obtain ⟨p,q, hi, ho⟩ := hsu.exists_parts
    cases p <;> simp at hi
    cases q <;> simp at hi
    use r.input

lemma NullableWord.nullableNonTerminal {w : List (Symbol T g.NT)} {v : Symbol T g.NT}
  (h : NullableWord w) (hin : v ∈ w) : ∃ nt, v = Symbol.nonterminal nt ∧ NullableNonTerminal nt := by
  revert v
  induction w with
  | nil => simp
  | cons hd tl ih =>
    intro v hin
    cases hin
    · cases hd
      · exfalso
        exact nullable_not_terminal h
      · rename_i nt
        use nt
        constructor
        rfl
        exact h.empty_of_append_left
    · apply ih
      apply NullableWord.empty_of_append_right
      change NullableWord ([hd] ++ tl) at h
      exact h
      assumption


section NullableRelated

-- nullable_related xs ys holds if ys is xs with nullable variables interspersed
inductive NullableRelated : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop where
  | empty_left (ys : List (Symbol T g.NT)) (h: NullableWord ys) : NullableRelated [] ys
  | cons_term (xs ys: List (Symbol T g.NT)) (h: NullableRelated xs ys) (z : T) :
                      NullableRelated (Symbol.terminal z :: xs) (Symbol.terminal z :: ys)
  | cons_nterm_match (xs ys: List (Symbol T g.NT)) (h: NullableRelated xs ys) (z : g.NT) :
                     NullableRelated (Symbol.nonterminal z :: xs) (Symbol.nonterminal z :: ys)
  | cons_nterm_nullable (xs ys: List (Symbol T g.NT)) (h: NullableRelated xs ys) (y : g.NT)
                        (hn : NullableNonTerminal y) : NullableRelated xs (Symbol.nonterminal y :: ys)

@[refl]
lemma NullableRelated.refl (w : List (Symbol T g.NT)) : NullableRelated w w := by
  induction w with
  | nil =>
    constructor
    rfl
  | cons hd tl ih =>
    cases hd <;> constructor <;> exact ih

lemma NullableRelated.derives {xs ys : List (Symbol T g.NT)} (h: NullableRelated xs ys) :
  g.Derives ys xs := by
  induction h with
  | empty_left _ h =>
    exact h
  | cons_term xs ys _ z ih =>
    change g.Derives ([Symbol.terminal z] ++ ys) ([Symbol.terminal z] ++ xs)
    exact ih.append_left _
  | cons_nterm_match xs ys _ z ih =>
    change g.Derives ([Symbol.nonterminal z] ++ ys) ([Symbol.nonterminal z] ++ xs)
    exact ih.append_left _
  | cons_nterm_nullable xs ys _ y hn ih =>
    change g.Derives ([Symbol.nonterminal y] ++ ys) ([] ++ xs)
    apply Derives.append_left_trans
    exact ih
    exact hn

lemma NullableRelated.empty_nullable {w : List (Symbol T g.NT)} (h : NullableRelated [] w) :
  NullableWord w := by
  induction w with
  | nil => rfl
  | cons hd tl ih =>
    cases h with
    | empty_left _ h => exact h
    | cons_nterm_nullable _ _ h nt hn =>
      change g.Derives ([Symbol.nonterminal nt] ++ tl) ([] ++ [])
      apply Derives.trans
      apply Derives.append_right
      exact hn
      exact ih h

lemma NullableRelated.empty_empty {w : List (Symbol T g.NT)} (h : NullableRelated w []) : w = [] := by
  cases h with
  | empty_left => rfl

lemma NullableRelated.append_nullable {w w' v : List (Symbol T g.NT)} (h1 : NullableRelated w' w)
  (h2 : NullableWord v) : NullableRelated w' (v ++ w) := by
  revert w w'
  induction v with
  | nil =>
    intro w w' h1
    exact h1
  | cons hd tl ih =>
    intro w w' h1
    obtain ⟨nt, h3, h4⟩ := h2.nullableNonTerminal (List.mem_cons_self hd tl)
    rw [h3]
    constructor
    apply ih
    apply NullableWord.empty_of_append_right
    change NullableWord ([hd] ++ tl) at h2
    exact h2
    exact h1
    exact h4

lemma NullableRelated.append {w1' w2' w1 w2 : List (Symbol T g.NT)} (h1 : NullableRelated w1' w1)
  (h2 : NullableRelated w2' w2) : NullableRelated (w1' ++ w2') (w1 ++ w2) := by
  revert w2' w2
  induction h1 with
  | empty_left w1' h =>
    intro w2' w2 h2
    simp
    exact h2.append_nullable h
  | cons_term w2' w2 _ t ih=>
    intro w2' w2 h2
    constructor
    exact ih h2
  | cons_nterm_match w2' w2 _ nt ih=>
    intro w2' w2 h2
    constructor
    exact ih h2
  | cons_nterm_nullable w2' w2 _ nt hn ih =>
    intro w2' w2 h2
    constructor
    exact ih h2
    exact hn

-- maybe easier to do (h : u = w1 ++ w2) and then induction on h. This is quite tedious
lemma NullableRelated.append_split {w' w1 w2 : List (Symbol T g.NT)} (h : NullableRelated w' (w1 ++ w2)) :
  ∃ w1' w2', w' = w1' ++ w2' ∧ NullableRelated w1' w1 ∧ NullableRelated w2' w2 := by
  revert w2 w'
  induction w1 with
  | nil =>
    intro w' w2 h
    use [], w'
    simp
    constructor
    rfl
    exact h
  | cons hd tl ih =>
    intro w' w2 h
    cases w' with
    | nil =>
      use [], []
      simp
      have h' : NullableRelated [] (tl ++ w2) := by
        constructor
        apply NullableWord.empty_of_append_right
        change NullableRelated [] ([hd] ++ (tl ++ w2)) at h
        exact h.empty_nullable
      specialize @ih [] w2 h'
      obtain ⟨w1', w2', heq, _, h2⟩ := ih
      simp at heq
      constructor
      · constructor
        cases h
        · apply NullableWord.empty_of_append_left
          assumption
        · change NullableWord ([Symbol.nonterminal _] ++ tl)
          apply Derives.trans
          apply Derives.append_right
          assumption
          simp
          exact h'.empty_nullable.empty_of_append_left
      · rw [←heq.2]
        exact h2
    | cons hd' tl' =>
      cases h with
      | cons_term _ _ h t =>
        obtain ⟨w1', w2', heq, h1, h2⟩ := ih h
        use (Symbol.terminal t :: w1'), w2'
        simp
        constructor
        · exact heq
        · constructor
          · constructor
            exact h1
          · exact h2
      | cons_nterm_match _ _ h nt =>
        obtain ⟨w1', w2', heq, h1, h2⟩ := ih h
        use (Symbol.nonterminal nt :: w1'), w2'
        simp
        constructor
        · exact heq
        · constructor
          · constructor
            exact h1
          · exact h2
      | cons_nterm_nullable _ _ h nt hn =>
        obtain ⟨w1', w2', heq, h1, h2⟩ := ih h
        use w1', w2'
        constructor
        · exact heq
        · constructor
          · constructor
            exact h1
            exact hn
          · exact h2

lemma NullableRelated.append_split_three {w' w1 w2 w3 : List (Symbol T g.NT)}
  (h : NullableRelated w' (w1 ++ w2 ++ w3)) :
  ∃ w1' w2' w3', w' = w1' ++ w2' ++ w3' ∧ NullableRelated w1' w1
    ∧ NullableRelated w2' w2 ∧ NullableRelated w3' w3 := by
  obtain ⟨wx', w3', heq, hx, h3⟩ := h.append_split
  obtain ⟨w1', w2', heq2, h1, h2⟩ := hx.append_split
  use w1',w2',w3'
  constructor ; rw [heq, heq2]
  exact ⟨h1, h2, h3⟩

end NullableRelated

-- *********************************************************************************************** --
-- ************************************** Nullable Symbols *************************************** --
-- *********************************************************************************************** --
section ComputeNullables
variable [DecidableEq g.NT]

-- All lefthand side non-terminals
noncomputable def generators : Finset g.NT := (g.rules.toList.map (fun r => r.input)).toFinset

lemma input_in_generators {r : ContextFreeRule T g.NT} (h : r ∈ g.rules) :
  r.input ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at h
  revert h
  induction g.rules.toList with
  | nil => simp
  | cons hd tl ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw [c1]
    · right
      exact ih c2

lemma nonterminal_in_generators {v : g.NT} {r : ContextFreeRule T g.NT} (h : r ∈ g.rules) (h' : r.input = v):
  v ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at h
  revert h
  induction g.rules.toList with
  | nil => simp
  | cons hd tl ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw [← h', c1]
    · right
      exact ih c2

-- Fixpoint iteration to compute all nullable variables
-- For the termination proof, we ensure that we only ever add nonterminals from the set of generators
def symbol_is_nullable (nullable : Finset g.NT) (s : Symbol T g.NT) : Bool :=
  match s with
  | Symbol.terminal _ => False
  | Symbol.nonterminal nt => nt ∈ nullable

def rule_is_nullable (nullable : Finset g.NT) (r : ContextFreeRule T g.NT) : Bool :=
  ∀ s ∈ r.output, symbol_is_nullable nullable s

def add_if_nullable (r : ContextFreeRule T g.NT) (nullable : Finset g.NT) : Finset g.NT :=
  if rule_is_nullable nullable r then insert r.input nullable else nullable

lemma add_if_nullable_subset_generators {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (p : nullable ⊆ g.generators) (hin : r ∈ g.rules) :
  add_if_nullable r nullable ⊆ g.generators := by
  unfold add_if_nullable
  split
  · exact Finset.insert_subset (input_in_generators hin) p
  · exact p

lemma add_if_nullable_subset (r : ContextFreeRule T g.NT) (nullable : Finset g.NT) :
  nullable ⊆ (add_if_nullable r nullable) := by
  unfold add_if_nullable
  split <;> simp

--  Single round of fixpoint iteration
--  Add all rules' lefthand variable if all output symbols are in the set of nullable symbols
noncomputable def add_nullables (nullable : Finset g.NT) : Finset g.NT :=
  g.rules.toList.attach.foldr (fun ⟨r, _⟩ => add_if_nullable r) nullable

lemma add_nullables_subset_generators (nullable : Finset g.NT) (p : nullable ⊆ g.generators) :
  add_nullables nullable ⊆ g.generators := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil => simp; exact p
  | cons hd tl ih =>
    exact add_if_nullable_subset_generators ih (Finset.mem_toList.1 hd.2)

lemma add_nullables_grows (nullable : Finset g.NT) :
  nullable ⊆ (add_nullables nullable) := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil => simp
  | cons hd tl ih =>
    apply subset_trans ih
    apply add_if_nullable_subset hd.1

-- Proof of our termination measure shrinking
lemma generators_limits_nullable (nullable : Finset g.NT) (p : nullable ⊆ g.generators)
  (hneq : nullable ≠ add_nullables nullable) :
  (g.generators).card - (add_nullables nullable).card < (g.generators).card - nullable.card := by
  have h := HasSubset.Subset.ssubset_of_ne (add_nullables_grows nullable) hneq
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_lt_of_le
    · apply Finset.card_lt_card h
    · exact Finset.card_le_card (add_nullables_subset_generators nullable p)
  · apply Finset.card_lt_card h

noncomputable def add_nullables_iter (nullable : Finset g.NT) (p : nullable ⊆ g.generators) : Finset g.NT :=
  let nullable' := add_nullables nullable
  if nullable = nullable' then
    nullable
  else
    add_nullables_iter nullable' (add_nullables_subset_generators nullable p)
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable p h

-- Compute all nullable variables of a grammar
noncomputable def compute_nullables : Finset g.NT :=
  add_nullables_iter ∅ generators.empty_subset

-- ********************************************************************** --
-- Only If direction of the main correctness theorem of compute_nullables --
-- ********************************************************************** --

lemma rule_is_nullable_correct (nullable : Finset g.NT) (r : ContextFreeRule T g.NT)
  (hrin : r ∈ g.rules) (hin : ∀ v ∈ nullable, NullableNonTerminal v) (hr : rule_is_nullable nullable r) :
  NullableNonTerminal r.input := by
  unfold rule_is_nullable at hr
  unfold NullableNonTerminal
  have h1 : g.Produces [Symbol.nonterminal r.input] r.output := by
    use r
    constructor
    exact hrin
    rw [ContextFreeRule.rewrites_iff]
    use [], []
    simp
  apply Produces.trans_derives h1
  apply symbols_nullable_nullableWord
  intro v hvin
  simp at hr
  specialize hr v hvin
  unfold symbol_is_nullable at hr
  cases v <;> simp at hr
  exact hin _ hr

lemma add_nullables_nullable (nullable : Finset g.NT) (hin : ∀ v ∈ nullable, NullableNonTerminal v) :
  ∀ v ∈ add_nullables nullable, NullableNonTerminal v := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil =>
    simp
    apply hin
  | cons hd tl ih =>
    simp
    unfold add_if_nullable
    split <;> rename_i h
    · simp
      constructor
      · apply rule_is_nullable_correct _ _ (Finset.mem_toList.1 hd.2) ih
        simp
        exact h
      · simp at ih
        exact ih
    · simp at ih
      exact ih

-- Main correctness result of the only if direction
lemma add_nullables_iter_only_nullable (nullable : Finset g.NT) (p : nullable ⊆ g.generators)
  (hin : ∀ v ∈ nullable, NullableNonTerminal v) :
  ∀ v ∈ (add_nullables_iter nullable p), NullableNonTerminal v:= by
  unfold add_nullables_iter
  intro v
  simp
  split
  · tauto
  · apply add_nullables_iter_only_nullable (add_nullables nullable)
          (add_nullables_subset_generators nullable p)
    exact add_nullables_nullable nullable hin
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable p h

-- ***************************************************************** --
-- If direction of the main correctness theorem of compute_nullables --
-- ***************************************************************** --

lemma subset_add_if_nullable_subset {r: ContextFreeRule T g.NT} {nullable nullable' : Finset g.NT}
  (p : nullable ⊆ nullable') : add_if_nullable r nullable ⊆ add_if_nullable r nullable' := by
  intro v hvin
  unfold add_if_nullable rule_is_nullable at hvin ⊢
  by_cases  h : decide (∀ s ∈ r.output, symbol_is_nullable nullable s) = true <;> simp [h] at hvin; simp at h
  · split <;> rename_i h'; simp at h'
    · cases hvin with
      | inl h =>
        rw [h]
        exact Finset.mem_insert_self r.input nullable'
      | inr h =>
        exact Finset.mem_insert_of_mem (p h)
    · cases hvin with
      | inl h'' =>
        unfold symbol_is_nullable at h' h
        simp at h' h
        obtain ⟨s, hsin, hs⟩ := h'
        specialize h s
        cases s <;> simp at hs h
        · contradiction
        · rename_i u
          apply h at hsin
          apply p at hsin
          contradiction
      | inr h =>
        exact p h
  · split
    · exact Finset.mem_insert_of_mem (p hvin)
    · exact (p hvin)

private lemma add_if_nullable_subset_rec {l : List (ContextFreeRule T g.NT)} {nullable : Finset g.NT} :
  nullable ⊆ List.foldr add_if_nullable nullable l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp
    apply Finset.Subset.trans ih
    apply add_if_nullable_subset

lemma nullable_in_add_nullables {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (h : rule_is_nullable nullable r) (hr : r ∈ g.rules) : r.input ∈ add_nullables nullable := by
  unfold add_nullables
  have h := List.mem_attach g.rules.toList ⟨r, (Finset.mem_toList.2 hr)⟩
  revert r nullable
  induction g.rules.toList.attach with
  | nil =>
    intro r nullable _ hrin
    simp
  | cons r t ih =>
    intro r' nullable h hr' hr''
    cases hr'' <;> simp at ih ⊢
    · apply Finset.mem_of_subset
      apply subset_add_if_nullable_subset
      apply add_if_nullable_subset_rec
      unfold add_if_nullable
      simp [h]
    · rename_i hr''
      apply Finset.mem_of_subset
      apply add_if_nullable_subset
      apply ih h
      exact hr''
      exact hr'

lemma add_nullable_add_nullable_iter (nullable: Finset g.NT) (p : nullable ⊆ generators) :
  add_nullables_iter nullable p = add_nullables (add_nullables_iter nullable p) := by
  unfold add_nullables_iter
  simp
  split <;> rename_i h
  · exact h
  · apply add_nullable_add_nullable_iter
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable p h

lemma nullable_in_compute_nullables (nullable : Finset g.NT) (p : nullable ⊆ generators) (v : g.NT)
  (n : ℕ) (h: g.DerivesIn [Symbol.nonterminal v] [] n) : v ∈ add_nullables_iter nullable p := by
  cases n with
  | zero =>
    cases h
  | succ n =>
    obtain ⟨u, hwu, hue⟩ := h.head_of_succ
    obtain ⟨r, hrin, hwu⟩ := hwu
    have h : rule_is_nullable (add_nullables_iter nullable p) r := by
      have h1 : u = r.output := by
        obtain ⟨p,q,h1,h2⟩ := hwu.exists_parts
        cases p <;> simp at h1
        cases q <;> simp at h1
        simp at h2
        exact h2
      unfold rule_is_nullable
      simp
      intro s hsin
      rw [←h1] at hsin
      obtain ⟨v', hv'⟩ := hue.nullable_mem_nonterminal hsin
      unfold symbol_is_nullable
      rw [hv']
      simp
      have ⟨m,_, hse⟩ := hue.mem_nullable hsin
      apply nullable_in_compute_nullables
      rw [←hv']
      exact hse
    have h1 : v = r.input := by
      obtain ⟨p,q,h2,_⟩ := hwu.exists_parts
      cases p <;> simp at h2
      cases q <;> simp at h2
      exact h2
    rw [add_nullable_add_nullable_iter]
    rw [h1]
    exact nullable_in_add_nullables h hrin

-- Main correctness theorem of computing all nullable symbols --
lemma compute_nullables_iff (v : g.NT) :
  v ∈ compute_nullables ↔ NullableNonTerminal v := by
  constructor
  · intro h
    apply add_nullables_iter_only_nullable Finset.empty
    tauto
    exact h
  · intro h
    unfold NullableNonTerminal at h
    obtain ⟨m, h⟩ := (derives_iff_derivesIn _ _ _).1 h
    apply nullable_in_compute_nullables
    exact h

end ComputeNullables

-- *********************************************************************************************** --
-- ************************************* Epsilon Elimination ************************************* --
-- *********************************************************************************************** --

section EliminateEmpty

variable [DecidableEq g.NT]

def remove_nullable (nullable : Finset g.NT) (output : List (Symbol T g.NT)) : List (List (Symbol T g.NT)) :=
  match output with
  | [] => [[]]
  | x :: xs => match x with
               | Symbol.nonterminal n => (if n ∈ nullable then remove_nullable nullable xs else [])
                                         ++ List.map (fun y => x :: y) (remove_nullable nullable xs)
               | Symbol.terminal _ => List.map (fun y => x :: y) (remove_nullable nullable xs)

def remove_nullable_rule (nullable : Finset g.NT) (r: ContextFreeRule T g.NT) : (List (ContextFreeRule T g.NT)) :=
  let fltrmap : List (Symbol T g.NT) → Option (ContextFreeRule T g.NT)
    | [] => Option.none
    | h :: t => ContextFreeRule.mk r.input (h :: t)
  (remove_nullable nullable r.output).filterMap fltrmap

noncomputable def remove_nullables (nullable : Finset g.NT) [DecidableEq T] : Finset (ContextFreeRule T g.NT) :=
  (g.rules.toList.map (remove_nullable_rule nullable)).flatten.toFinset

noncomputable def eliminate_empty (g : ContextFreeGrammar T) [DecidableEq g.NT] [DecidableEq T] :=
  ContextFreeGrammar.mk g.NT g.initial (remove_nullables compute_nullables)

-- ******************************************************************** --
-- Only If direction of the main correctness theorem of eliminate_empty --
-- ******************************************************************** --

-- First we prove that the grammar cannot derive empty (Given the input non-empty)

lemma in_remove_nullable_rule {r r': ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (h: r' ∈ remove_nullable_rule nullable r) : r'.output ≠ [] := by
  unfold remove_nullable_rule at h
  rw [List.mem_filterMap] at h
  obtain ⟨a, h1, h2⟩ := h
  cases a <;> simp at h2
  · rw [←h2]
    simp

lemma in_remove_not_epsilon {r : ContextFreeRule T g.NT} {nullable : Finset g.NT} [DecidableEq T]
  (h : r ∈ remove_nullables nullable) : r.output ≠ [] := by
  unfold remove_nullables at h
  rw [List.mem_toFinset, List.mem_flatten] at h
  obtain ⟨l, hlin, hrin⟩ := h
  rw [List.mem_map] at hlin
  obtain ⟨r',hr'in, hr'l⟩ := hlin
  rw [←hr'l] at hrin
  exact in_remove_nullable_rule hrin

lemma produces_not_epsilon {v w : List (Symbol T g.NT)} [DecidableEq T]
  (h : (g.eliminate_empty).Produces v w) : w ≠ [] := by
  unfold Produces at h
  change ∃ r ∈ (remove_nullables compute_nullables), r.Rewrites v w at h
  obtain ⟨r, hin, hr⟩ := h
  intro hw
  rw [hw] at hr
  apply in_remove_not_epsilon hin
  exact rewrites_empty_output hr

lemma derives_not_epsilon {v w : List (Symbol T g.NT)} [DecidableEq T]
  (h : (g.eliminate_empty).Derives v w) (he : v ≠ []) :
  w ≠ [] := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact he
  | head hd _ ih =>
    apply ih
    exact produces_not_epsilon hd

-- Main proof of the only if direction: If the eliminate_empty grammar derives a string,
-- it is derivable in the original grammar

lemma remove_nullable_related {o o': List (Symbol T g.NT)} (nullable : Finset g.NT)
  (p : ∀ x ∈ nullable, NullableNonTerminal x) (hin : o ∈ (remove_nullable nullable o')) :
  NullableRelated o o' := by
  revert o
  induction o' with
  | nil =>
    intro o hin
    unfold remove_nullable at hin
    simp at hin
    rw [hin]
  | cons hd tl ih =>
    intro o hin
    unfold remove_nullable at hin
    cases hd with
    | nonterminal nt =>
      simp at hin
      cases hin <;> rename_i h
      · by_cases h' : nt ∈ nullable <;> simp [h'] at h
        constructor
        exact ih h
        exact p _ h'
      · obtain ⟨o1, hoin, ho⟩ := h
        rw [←ho]
        constructor
        exact ih hoin
    | terminal t =>
      simp at hin
      obtain ⟨o1, hoin, ho⟩ := hin
      rw [←ho]
      constructor
      exact ih hoin

lemma remove_nullable_rule_related {r': ContextFreeRule T g.NT} [DecidableEq T]
  {r : ContextFreeRule T (@eliminate_empty T g).NT} {h : r ∈ remove_nullable_rule compute_nullables r'} :
  r.input = r'.input ∧ @NullableRelated _ g r.output r'.output := by
  unfold remove_nullable_rule at h
  rw [List.mem_filterMap] at h
  obtain ⟨o, ho1, ho2⟩ := h
  cases o <;> simp at ho2
  rw [←ho2]
  constructor
  rfl
  apply remove_nullable_related
  intro
  apply (compute_nullables_iff _).1
  exact ho1

lemma eliminate_empty_rules [DecidableEq T] (r : ContextFreeRule T (@eliminate_empty T g).NT) {h : r ∈ (@eliminate_empty T g).rules} :
  ∃ r' ∈ g.rules, r.input = r'.input ∧ @NullableRelated _ g r.output r'.output := by
  unfold eliminate_empty remove_nullables at h
  simp at h
  obtain ⟨r', hrin', hr'⟩ := h
  use r'
  constructor
  exact hrin'
  apply remove_nullable_rule_related
  exact hr'

lemma eliminate_empty_step_derives [DecidableEq T] {v w : List (Symbol T g.NT)} (h : (@eliminate_empty T g).Produces v w) :
  g.Derives v w := by
  obtain ⟨r, hrin, hr⟩ := h
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  apply Derives.append_right
  apply Derives.append_left
  obtain ⟨r', hin, heq, hn⟩ := @eliminate_empty_rules _ _ _ _ r hrin
  rw [heq]
  apply Produces.trans_derives
  exact rewrites_produces hin
  apply hn.derives

lemma eliminate_empty_implies [DecidableEq T] {v w : List (Symbol T g.NT)}
  (h : (@eliminate_empty T g).Derives v w) : g.Derives v w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    apply Derives.trans
    exact eliminate_empty_step_derives hp
    exact ih

-- *************************************************************** --
-- If direction of the main correctness theorem of eliminate_empty --
-- *************************************************************** --

lemma in_remove_nullable (nullable : Finset g.NT) (output : List (Symbol T g.NT)) :
  output ∈ remove_nullable nullable output := by
  induction output with
  | nil =>
    unfold remove_nullable
    simp
  | cons o output ih =>
    unfold remove_nullable
    cases o <;> simp
    · exact ih
    · rename_i nt
      by_cases h : nt ∈ nullable <;> simp [h]
      · right
        exact ih
      · exact ih

lemma in_remove_nullables [DecidableEq T] (nullable : Finset g.NT) (r : ContextFreeRule T g.NT) (h : r ∈ g.rules)
  (ho : r.output ≠ []):
  r ∈ remove_nullables nullable := by
  unfold remove_nullables
  rw [List.mem_toFinset, List.mem_flatten]
  use (remove_nullable_rule nullable r)
  constructor
  · simp
    use r
  · unfold remove_nullable_rule
    rw [List.mem_filterMap]
    use r.output
    constructor
    · apply in_remove_nullable
    · obtain ⟨rin, rout⟩ := r
      cases rout
      contradiction
      simp

lemma nullableRelated_in_remove_nullable {nullable : Finset g.NT} {o o': List (Symbol T g.NT)}
  (h : NullableRelated o' o) (p : ∀ s, s ∈ nullable ↔ NullableNonTerminal s) :
  o' ∈ remove_nullable nullable o := by
  revert o'
  induction o with
  | nil =>
    intro o' h
    rw [h.empty_empty]
    unfold remove_nullable
    exact List.mem_singleton.2 rfl
  | cons o os ih =>
    unfold remove_nullable
    intro o' h
    cases o with
    | terminal t =>
      simp
      cases h with
      | empty_left =>
        rename_i h
        exfalso
        exact nullable_not_terminal h
      | cons_term os' _ h =>
        use os'
        constructor
        · exact ih h
        · rfl
    | nonterminal nt =>
      simp
      cases h with
      | empty_left _ h =>
        left
        rw [←List.singleton_append] at h
        rw [p]
        exact ⟨h.empty_of_append_left, ih (NullableRelated.empty_left os h.empty_of_append_right)⟩
      | cons_nterm_match os' _ h =>
        right
        use os'
        constructor
        · exact ih h
        · rfl
      | cons_nterm_nullable os' _ h _ hn =>
        left
        rw [p]
        exact ⟨hn, ih h⟩

lemma nullableRelated_rule_in_rules [DecidableEq T] {r : ContextFreeRule T g.NT} {o' : List (Symbol T g.NT)}
  (hrin : r ∈ g.rules) (h : NullableRelated o' r.output) (hneq : o' ≠ []) :
  { input := r.input, output := o' } ∈ (@eliminate_empty T g).rules := by
  unfold eliminate_empty
  simp
  unfold remove_nullables
  rw [List.mem_toFinset, List.mem_flatten]
  use (remove_nullable_rule compute_nullables r)
  unfold remove_nullable_rule
  constructor
  · rw [List.mem_map]
    use r
    constructor
    · exact Finset.mem_toList.2 hrin
    · rfl
  · rw [List.mem_filterMap]
    use o'
    constructor
    · exact nullableRelated_in_remove_nullable h compute_nullables_iff
    · cases o'
      contradiction
      rfl

lemma empty_related_produces_derives [DecidableEq T] {v w w': List (Symbol T g.NT)} (hp : g.Produces v w)
  (hn : NullableRelated w' w) : ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w' := by
  unfold Produces at hp
  obtain ⟨r, hrin, hr⟩ := hp
  rw [r.rewrites_iff] at hr
  obtain ⟨p,q, hv, hw⟩ := hr
  rw [hw] at hn
  obtain ⟨w1', w2', w3', heq, hw1, hw2, hw3⟩ := hn.append_split_three
  cases w2' with
  | nil =>
    use w'
    constructor
    · rw [hv, heq]
      apply (hw1.append _).append hw3
      apply NullableRelated.empty_left
      apply Produces.trans_derives
      apply rewrites_produces hrin
      exact hw2.empty_nullable
    · rfl
  | cons hd tl =>
    use (w1' ++ [Symbol.nonterminal r.input] ++ w3')
    constructor
    · rw [hv]
      apply (hw1.append _).append hw3
      rfl
    · rw [heq]
      apply Produces.single
      have hneq : (hd :: tl) ≠ [] := by simp
      have h := nullableRelated_rule_in_rules hrin hw2 hneq
      let r' : ContextFreeRule T g.NT := { input := r.input, output := hd :: tl }
      use r'
      constructor
      exact h
      change r'.Rewrites (w1' ++ [Symbol.nonterminal r'.input] ++ w3') (w1' ++ r'.output ++ w3')
      apply ContextFreeRule.rewrites_of_exists_parts

lemma implies_eliminate_empty_related [DecidableEq T] {v w : List (Symbol T g.NT)} (hneq : w ≠ []) {n : ℕ}
  (h : g.DerivesIn v w n) :
  ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w := by
  cases n with
  | zero =>
    cases h
    use v
  | succ n =>
    obtain ⟨u, huv, hvw⟩ := h.head_of_succ
    obtain ⟨u', hru', huw'⟩ := @implies_eliminate_empty_related _ _ _ hneq _ hvw
    obtain ⟨v', hvrv', hpv'u'⟩ := empty_related_produces_derives huv hru'
    use v'
    constructor
    exact hvrv'
    exact Derives.trans hpv'u' huw'

lemma implies_eliminate_empty [DecidableEq T] {w : List (Symbol T g.NT)} {v : g.NT} {hneq : w ≠ []} {n : ℕ}
  (h : g.DerivesIn [Symbol.nonterminal v] w n) :
  (@eliminate_empty T g).Derives [Symbol.nonterminal v] w := by
  obtain ⟨w', hw', hw'w⟩ := implies_eliminate_empty_related hneq h
  cases hw'
  · rename_i h
    obtain ⟨h1, h1⟩ := Derives.eq_or_head hw'w
    · contradiction
    · apply Derives.empty_empty at hw'w
      contradiction
  · rename_i h
    cases h
    exact hw'w
  · rename_i h
    apply NullableRelated.empty_empty at h
    rw [h] at hw'w
    apply Derives.empty_empty at hw'w
    contradiction

theorem eliminate_empty_correct [DecidableEq T] :
  g.language \ {[]} = (@eliminate_empty T g).language := by
  unfold language Generates
  apply Set.eq_of_subset_of_subset
  · intro w h
    rw [Set.mem_diff] at h
    obtain ⟨h1, h2⟩ := h
    simp at h1
    rw [g.derives_iff_derivesIn] at h1
    obtain ⟨n, h1⟩ := h1
    apply implies_eliminate_empty
    · intro h'
      simp at h'
      rw [h'] at h2
      contradiction
    · unfold eliminate_empty
      simp
      exact h1
  · intro w h
    simp at h
    rw [Set.mem_diff]
    constructor
    · exact eliminate_empty_implies h
    · rw [Set.not_mem_singleton_iff]
      intro h'
      apply derives_not_epsilon h
      simp
      rw [h', List.map_nil]

end EliminateEmpty

end ContextFreeGrammar
