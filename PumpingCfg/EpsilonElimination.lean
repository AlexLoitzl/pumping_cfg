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

-- *********************************************************************************************** --
-- ************************************** Nullable Symbols *************************************** --
-- *********************************************************************************************** --
variable [DecidableEq g.NT]

-- All lefthand side non-terminals
def generators : Finset g.NT := (g.rules.map (fun r => r.input)).toFinset

lemma in_generators {r : ContextFreeRule T g.NT} (h : r ∈ g.rules) :
  r.input ∈ g.generators := by
  unfold generators
  revert h
  induction g.rules with
  | nil => simp
  | cons hd tl ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw [c1]
    · right
      exact ih c2

-- Fixpoint iteration to compute all nullable variables
-- I can't quite get functional induction to work here :(
-- NOTE If we instead shrink the set of generators the termination argument should
-- be easier. I am not so sure about the correctness proofs

def symbol_is_nullable (nullable : Finset g.NT) (s : Symbol T g.NT) : Bool :=
    match s with
    | Symbol.terminal _ => False
    | Symbol.nonterminal nt => nt ∈ nullable

def rule_is_nullable (nullable : Finset g.NT) (r : ContextFreeRule T g.NT) : Bool :=
  ∀ s ∈ r.output, symbol_is_nullable nullable s

def add_if_nullable (r : ContextFreeRule T g.NT) (nullable : Finset g.NT) : Finset g.NT :=
  if rule_is_nullable nullable r then insert r.input nullable else nullable

--  Single round of fixpoint iteration
--  Add all rules' lefthand variable if all output symbols are in the set of nullable symbols
def add_nullables (nullable : Finset g.NT) : Finset g.NT :=
  g.rules.attach.foldr (fun ⟨r, _⟩ => add_if_nullable r) nullable

-- Lemmas for termination proof
lemma add_if_nullable_subset_generators {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (p : nullable ⊆ g.generators) (hin : r ∈ g.rules) :
  add_if_nullable r nullable ⊆ g.generators := by
  unfold add_if_nullable
  split
  · exact Finset.insert_subset (in_generators hin) p
  · exact p

lemma add_nullables_subset_generators (nullable : Finset g.NT) (p : nullable ⊆ g.generators) :
  add_nullables nullable ⊆ g.generators := by
  unfold add_nullables
  induction g.rules.attach with
  | nil => simp; exact p
  | cons hd tl ih => exact add_if_nullable_subset_generators ih hd.2

lemma add_if_nullable_subset (r : ContextFreeRule T g.NT) (nullable : Finset g.NT) :
  nullable ⊆ (add_if_nullable r nullable) := by
  unfold add_if_nullable
  split <;> simp

lemma nullable_subset_add_nullables (nullable : Finset  g.NT) :
  nullable ⊆ (add_nullables nullable) := by
  unfold add_nullables
  induction g.rules.attach with
  | nil => simp
  | cons hd tl ih =>
    apply subset_trans ih
    apply add_if_nullable_subset hd.1

-- Main Property that guarantees the termination of our fixpoint iteration
lemma generators_limits_nullable (nullable : Finset g.NT) (p : nullable ⊆ g.generators)
  (hneq : nullable ≠ add_nullables nullable) :
  (g.generators).card - (add_nullables nullable).card < (g.generators).card - nullable.card := by
  have h := HasSubset.Subset.ssubset_of_ne (nullable_subset_add_nullables nullable) hneq
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_lt_of_le
    · apply Finset.card_lt_card h
    · exact Finset.card_le_card (add_nullables_subset_generators nullable p)
  · apply Finset.card_lt_card h

def add_nullables_iter (nullable : Finset g.NT) (p : nullable ⊆ g.generators) : Finset g.NT :=
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
def compute_nullables : Finset g.NT :=
  add_nullables_iter ∅ generators.empty_subset

def NullableNonTerminal (v : g.NT) : Prop := g.Derives [Symbol.nonterminal v] []

-- ********************************************************************** --
-- Only If direction of the main correctness theorem of compute_nullables --
-- ********************************************************************** --

-- That's annoying
omit [DecidableEq g.NT] in
lemma all_nullable_nullable (w : List (Symbol T g.NT)) (h: ∀ v ∈ w, g.Derives [v] []) :
  g.Derives w [] := by
  induction w with
  | nil => exact Derives.refl []
  | cons hd tl ih =>
    change g.Derives ([hd] ++ tl) []
    apply Derives.trans
    · apply Derives.append_right
      apply h
      simp
    · simp
      apply ih
      intro v hv
      apply h
      right
      exact hv

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
  apply all_nullable_nullable
  intro v hvin
  simp at hr
  specialize hr v hvin
  unfold symbol_is_nullable at hr
  cases v <;> simp at hr
  apply hin _ hr

lemma add_nullables_nullable (nullable : Finset g.NT) (hin : ∀ v ∈ nullable, NullableNonTerminal v) :
  ∀ v ∈ add_nullables nullable, NullableNonTerminal v := by
  unfold add_nullables
  induction g.rules.attach with
  | nil =>
    simp
    apply hin
  | cons hd tl ih =>
    simp
    unfold add_if_nullable
    split
    · simp
      constructor
      · apply rule_is_nullable_correct _ _ hd.2 ih
        rename_i h
        simp
        exact h
      · exact ih
    · exact ih

-- Main correctness result of the only if direction
lemma add_nullables_iter_only_nullable (nullable : Finset g.NT) (p : nullable ⊆ g.generators)
  (hin : ∀ v ∈ nullable, NullableNonTerminal v) :
  ∀ v ∈ (add_nullables_iter nullable p), NullableNonTerminal v:= by
  unfold add_nullables_iter
  intro v
  simp
  split
  · tauto
  · have ih := add_nullables_iter_only_nullable (add_nullables nullable) (add_nullables_subset_generators nullable p)
    apply ih
    exact add_nullables_nullable nullable hin
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable p h

-- ************************
-- If direction starts here
-- ************************

omit [DecidableEq g.NT] in
lemma Derives.empty_of_append {w u v: List (Symbol T g.NT)}
  (hwe : g.Derives (w ++ u ++ v) []) : g.Derives u [] := by
  rw [derives_iff_derivesIn] at hwe ⊢
  obtain ⟨n, hwe⟩ := hwe
  obtain ⟨m, _, hue⟩ := hwe.empty_of_append
  use m

omit [DecidableEq g.NT] in
lemma Derives.empty_of_append_left {u v: List (Symbol T g.NT)}
  (hwe : g.Derives (u ++ v) []) : g.Derives u [] := by
  apply @Derives.empty_of_append _ _ []
  exact hwe

omit [DecidableEq g.NT] in
lemma Derives.empty_of_append_right {u v: List (Symbol T g.NT)}
  (hwe : g.Derives (u ++ v) []) : g.Derives v [] := by
  apply @Derives.empty_of_append _ _ _ _ []
  simp
  exact hwe

lemma l0 {r: ContextFreeRule T g.NT} {nullable nullable' : Finset g.NT} (p : nullable ⊆ nullable') :
  add_if_nullable r nullable ⊆ add_if_nullable r nullable' := by
  intro v hvin
  unfold add_if_nullable rule_is_nullable at hvin ⊢
  by_cases  h : decide (∀ s ∈ r.output, symbol_is_nullable nullable s) = true <;> simp[h] at hvin; simp at h
  · split <;> rename_i h'; simp at h'
    · cases hvin with
      | inl h =>
        rw[h]
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

lemma lminus1 {l : List {x // x ∈ g.rules}} {nullable : Finset g.NT} :
  nullable ⊆ List.foldr (fun x : {x // x ∈ g.rules} ↦ add_if_nullable ↑x) nullable l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp
    apply Finset.Subset.trans ih
    apply add_if_nullable_subset

lemma l1 {r : ContextFreeRule T g.NT} {nullable : Finset g.NT} (h : rule_is_nullable nullable r)
  (hr : r ∈ g.rules) : r.input ∈ add_nullables nullable := by
  unfold add_nullables
  have h := List.mem_attach g.rules ⟨r, hr⟩
  revert r nullable
  induction g.rules.attach with
  | nil =>
    intro r nullable _ hrin
    simp
  | cons r t ih =>
    intro r' nullable h hr' hr''
    cases hr'' <;> simp at ih ⊢
    · apply Finset.mem_of_subset
      apply l0
      apply lminus1
      unfold add_if_nullable
      simp[h]
    · rename_i hr''
      apply Finset.mem_of_subset
      apply add_if_nullable_subset
      apply ih h
      exact hr''

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

omit [DecidableEq g.NT] in
lemma l2 {w : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ} (h: g.DerivesSteps w [] n) (hin: s ∈ w) :
  ∃ m ≤ n, g.DerivesSteps [s] [] m := by
  revert n
  induction w with
  | nil => contradiction
  | cons v t ih =>
    intro n h
    cases hin with
    | head =>
      change g.DerivesSteps ([s] ++ t) [] n at h
      exact DerivesSteps.empty_of_append_left h
    | tail _ hs =>
      change g.DerivesSteps ([v] ++ t) [] n at h
      obtain ⟨m, hmn, hte⟩ := DerivesSteps.empty_of_append_right h
      obtain ⟨m', hm'm,hse⟩ := ih hs hte
      use m'
      exact ⟨Nat.le_trans hm'm hmn, hse⟩

omit [DecidableEq g.NT] in
lemma l3 {w : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ} (hwe: g.DerivesSteps w [] n) (hin: s ∈ w) :
  ∃ v, s = Symbol.nonterminal v := by
  have ⟨m, hmn, hse⟩ := l2 hwe hin
  cases m with
  | zero =>
    contradiction
  | succ m =>
    obtain ⟨u, hwu, _⟩ := hse.head_of_succ
    obtain ⟨r, _, hsu⟩ := hwu
    obtain ⟨p,q, hi, ho⟩ := (r.rewrites_iff _ _).1  hsu
    cases p <;> simp at hi
    cases q <;> simp at hi
    use r.input

lemma nullable_in_compute_nullables' (nullable : Finset g.NT) (p : nullable ⊆ generators) (v : g.NT)
  (w : List (Symbol T g.NT)) (hw : w = [Symbol.nonterminal v]) (n : ℕ) (h: g.DerivesSteps w [] n) :
  v ∈ add_nullables_iter nullable p := by
  cases n with
  | zero =>
    rw[hw] at h
    cases h
  | succ n =>
    obtain ⟨u, hwu, hue⟩ := h.head_of_succ
    obtain ⟨r, hrin, hwu⟩ := hwu
    rw[hw] at *
    have h : rule_is_nullable (add_nullables_iter nullable p) r := by
      have h1 : u = r.output := by
        obtain ⟨p,q,h1,h2⟩ := (r.rewrites_iff _ _).1 hwu
        cases p <;> simp at h1
        cases q <;> simp at h1
        simp at h2
        exact h2
      unfold rule_is_nullable
      simp
      intro s hsin
      rw[←h1] at hsin
      obtain ⟨v', hv'⟩ := l3 hue hsin
      unfold symbol_is_nullable
      rw[hv']
      simp
      have ⟨m,_, hse⟩ := l2 hue hsin
      apply nullable_in_compute_nullables'
      rw[←hv']
      exact hse
    have h1 : v = r.input := by
      obtain ⟨p,q,h2,_⟩ := (r.rewrites_iff _ _).1 hwu
      cases p <;> simp at h2
      cases q <;> simp at h2
      exact h2
    rw[add_nullable_add_nullable_iter]
    rw[h1]
    exact l1 h hrin

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
    obtain ⟨m, h⟩ := (derives_iff_derivesSteps _ _ _).1 h
    apply nullable_in_compute_nullables'
    rfl
    exact h

-- *********************************************************************************************** --
-- ************************************* Epsilon Elimination ************************************* --
-- *********************************************************************************************** --

def nonterminalProp (s : Symbol T g.NT) (P : g.NT → Prop) :=
  match s with
  | Symbol.terminal _ => False
  | Symbol.nonterminal n => P n

def remove_nullable (nullable : Finset g.NT) (s: (Symbol T g.NT)) (acc : List (List (Symbol T g.NT))) :=
  match s with
  | Symbol.nonterminal n => (if n ∈ nullable then acc else []) ++ acc.map (fun x => s :: x)
  | Symbol.terminal _ => acc.map (fun x => s :: x)

def remove_nullable_rule (nullable : Finset g.NT) (r: ContextFreeRule T g.NT) : (List (ContextFreeRule T g.NT)) :=
  let fltrmap : List (Symbol T g.NT) → Option (ContextFreeRule T g.NT)
    | [] => Option.none
    | h :: t => ContextFreeRule.mk r.input (h :: t)
  (r.output.foldr (remove_nullable nullable) [[]]).filterMap fltrmap

def remove_nullables (nullable : Finset g.NT) : List (ContextFreeRule T g.NT) :=
  (g.rules.map (remove_nullable_rule nullable)).join

def eliminate_empty : ContextFreeGrammar T :=
  ContextFreeGrammar.mk g.NT g.initial (remove_nullables compute_nullables)

lemma in_remove_nullable_rule {r r': ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (h: r' ∈ remove_nullable_rule nullable r) : r'.output ≠ [] := by
  unfold remove_nullable_rule at h
  rw [List.mem_filterMap] at h
  obtain ⟨a, h1, h2⟩ := h
  cases a <;> simp at h2
  · rw [←h2]
    simp

lemma in_remove_not_epsilon {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (h : r ∈ remove_nullables nullable) : r.output ≠ [] := by
  unfold remove_nullables at h
  rw [List.mem_join] at h
  obtain ⟨l, hlin, hrin⟩ := h
  rw [List.mem_map] at hlin
  obtain ⟨r',hr'in, hr'l⟩ := hlin
  rw [←hr'l] at hrin
  apply in_remove_nullable_rule hrin

omit [DecidableEq g.NT] in
lemma rewrites_epsilon {v : List (Symbol T g.NT)} {r : ContextFreeRule T g.NT} (h : r.Rewrites v []) :
  r.output = [] := by
  obtain ⟨p,q,_,h2⟩ := h.exists_parts
  simp at h2
  tauto

lemma produces_not_epsilon {v w : List (Symbol T g.NT)} (h : (g.eliminate_empty).Produces v w) :
  w ≠ [] := by
  unfold Produces at h
  change ∃ r ∈ (remove_nullables compute_nullables), r.Rewrites v w at h
  obtain ⟨r, hin, hr⟩ := h
  intro hw
  rw [hw] at hr
  apply in_remove_not_epsilon hin
  exact rewrites_epsilon hr

lemma derives_not_epsilon {v w : List (Symbol T g.NT)} (h : (g.eliminate_empty).Derives v w) (he : v ≠ [])
  : w ≠ [] := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact he
  | head hd _ ih =>
    apply ih
    exact produces_not_epsilon hd

theorem eliminate_empty_correct :
  g.language = (@eliminate_empty T g).language \ {[]} := by sorry

end ContextFreeGrammar
