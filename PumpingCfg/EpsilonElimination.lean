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

abbrev NullableWord (w : List (Symbol T g.NT)) : Prop := g.Derives w []

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
      exact List.mem_cons_self hd tl
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
  exact hin _ hr

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
    split <;> rename_i h
    · simp
      constructor
      · apply rule_is_nullable_correct _ _ hd.2 ih
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
  · apply add_nullables_iter_only_nullable (add_nullables nullable)
          (add_nullables_subset_generators nullable p)
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

private lemma add_if_nullable_subset_rec {l : List {x // x ∈ g.rules}} {nullable : Finset g.NT} :
  nullable ⊆ List.foldr (fun x : {x // x ∈ g.rules} ↦ add_if_nullable ↑x) nullable l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp
    apply Finset.Subset.trans ih
    apply add_if_nullable_subset

lemma nullable_in_add_nullables {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (h : rule_is_nullable nullable r) (hr : r ∈ g.rules) : r.input ∈ add_nullables nullable := by
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
      apply subset_add_if_nullable_subset
      apply add_if_nullable_subset_rec
      unfold add_if_nullable
      simp [h]
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
lemma nullable_string_all_symbols_nullable {w : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ}
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

omit [DecidableEq g.NT] in
lemma nullable_only_nonterminals {w : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ}
  (hwe: g.DerivesIn w [] n) (hin: s ∈ w) : ∃ v, s = Symbol.nonterminal v := by
  have ⟨m, hmn, hse⟩ := nullable_string_all_symbols_nullable hwe hin
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
        obtain ⟨p,q,h1,h2⟩ := (r.rewrites_iff _ _).1 hwu
        cases p <;> simp at h1
        cases q <;> simp at h1
        simp at h2
        exact h2
      unfold rule_is_nullable
      simp
      intro s hsin
      rw [←h1] at hsin
      obtain ⟨v', hv'⟩ := nullable_only_nonterminals hue hsin
      unfold symbol_is_nullable
      rw [hv']
      simp
      have ⟨m,_, hse⟩ := nullable_string_all_symbols_nullable hue hsin
      apply nullable_in_compute_nullables
      rw [←hv']
      exact hse
    have h1 : v = r.input := by
      obtain ⟨p,q,h2,_⟩ := (r.rewrites_iff _ _).1 hwu
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

-- *********************************************************************************************** --
-- ************************************* Epsilon Elimination ************************************* --
-- *********************************************************************************************** --

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

def remove_nullables (nullable : Finset g.NT) : List (ContextFreeRule T g.NT) :=
  (g.rules.map (remove_nullable_rule nullable)).join

def eliminate_empty : ContextFreeGrammar T :=
  ContextFreeGrammar.mk g.NT g.initial (remove_nullables compute_nullables)

-- Only If Direction of correctness proof
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
  exact in_remove_nullable_rule hrin

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

lemma derives_not_epsilon {v w : List (Symbol T g.NT)} (h : (g.eliminate_empty).Derives v w) (he : v ≠ []) :
  w ≠ [] := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact he
  | head hd _ ih =>
    apply ih
    exact produces_not_epsilon hd

-- ********************************* Interesing prop of deriving ********************************* --
omit [DecidableEq g.NT] in
lemma Derives.append_left_trans {v w x y: List (Symbol T g.NT)}
    (hvw : g.Derives v w) (hxy : g.Derives x y) :
    g.Derives (x ++ v) (y ++ w) := by
    apply Derives.trans
    exact Derives.append_left hvw _
    exact Derives.append_right hxy _

omit [DecidableEq g.NT] in
lemma rewrites_produces {r : ContextFreeRule T g.NT} (h : r ∈ g.rules) :
  g.Produces [Symbol.nonterminal r.input] r.output := by
  use r
  constructor
  exact h
  rw [r.rewrites_iff]
  use [], []
  simp

-- *********************************************************************************************** --

-- nullable_related xs ys holds if ys is xs with nullable variables interspersed
inductive NullableRelated : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  | empty_left (ys : List (Symbol T g.NT)) (h: NullableWord ys) : NullableRelated [] ys
  | cons_term (xs ys: List (Symbol T g.NT)) (h: NullableRelated xs ys) (z : T) :
                      NullableRelated (Symbol.terminal z :: xs) (Symbol.terminal z :: ys)
  | cons_nterm_match (xs ys: List (Symbol T g.NT)) (h: NullableRelated xs ys) (z : g.NT) :
                     NullableRelated (Symbol.nonterminal z :: xs) (Symbol.nonterminal z :: ys)
  | cons_nterm_nullable (xs ys: List (Symbol T g.NT)) (h: NullableRelated xs ys) (y : g.NT)
                        (hn : NullableNonTerminal y) : NullableRelated xs (Symbol.nonterminal y :: ys)

omit [DecidableEq g.NT] in
@[refl]
lemma NullableRelated.refl (w : List (Symbol T g.NT)) : NullableRelated w w := by
  induction w with
  | nil =>
    constructor
    rfl
  | cons hd tl ih =>
    cases hd <;> constructor <;> exact ih

omit [DecidableEq g.NT] in
lemma nullable_related_derivable {xs ys : List (Symbol T g.NT)} (h: NullableRelated xs ys) :
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
      · by_cases h' : nt ∈ nullable <;> simp[h'] at h
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

lemma remove_nullable_rule_related {r': ContextFreeRule T g.NT}
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

lemma eliminate_empty_rules (r : ContextFreeRule T (@eliminate_empty T g).NT) {h : r ∈ (@eliminate_empty T g).rules} :
  ∃ r' ∈ g.rules, r.input = r'.input ∧ @NullableRelated _ g r.output r'.output := by
  unfold eliminate_empty remove_nullables at h
  simp at h
  obtain ⟨r', hrin', hr'⟩ := h
  use r'
  constructor
  exact hrin'
  apply remove_nullable_rule_related
  exact hr'

lemma eliminate_empty_step_derives {v w : List (Symbol T g.NT)} (h : (@eliminate_empty T g).Produces v w) :
  g.Derives v w := by
  obtain ⟨r, hrin, hr⟩ := h
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  apply Derives.append_right
  apply Derives.append_left
  obtain ⟨r', hin, heq, hn⟩ := @eliminate_empty_rules _ _ _ r hrin
  rw [heq]
  apply Produces.trans_derives
  exact rewrites_produces hin
  apply nullable_related_derivable
  exact hn

lemma eliminate_empty_implies {v w : List (Symbol T g.NT)}
  (h : (@eliminate_empty T g).Derives v w) : g.Derives v w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    apply Derives.trans
    exact eliminate_empty_step_derives hp
    exact ih

-- If Direction starts here
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
      by_cases h : nt ∈ nullable <;> simp[h]
      · right
        exact ih
      · exact ih

lemma in_remove_nullables (nullable : Finset g.NT) (r : ContextFreeRule T g.NT) (h : r ∈ g.rules)
  (ho : r.output ≠ []):
  r ∈ remove_nullables nullable := by
  unfold remove_nullables
  rw [List.mem_join]
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

omit [DecidableEq g.NT] in
lemma k1 {w : List (Symbol T g.NT)} (h : NullableWord w) : NullableRelated [] w := by sorry

-- lemma k2 {w w1 w2 : List (Symbol T g.NT)} {nt : g.NT} (hn : NullableNonTerminal nt)
--   (h : NullableRelated w (w1 ++ w2)) : NullableRelated w (w1 ++ [Symbol.nonterminal nt] ++ w2) := by sorry

lemma k3 {nullable : Finset g.NT} {o o': List (Symbol T g.NT)} (h : NullableRelated o' o)
  (p : ∀ s ∈ nullable, NullableNonTerminal s) : o' ∈ remove_nullable nullable o := by sorry

lemma k4 {w : List (Symbol T g.NT)} (h : NullableRelated [] w) : NullableWord w := by sorry

-- lemma k5 {w : List (Symbol T g.NT)} (h : NullableWord w) : NullableWord w.tail := by sorry

-- lemma l0 {w : List (Symbol T g.NT)} {v : Symbol T g.NT} (h : NullableWord w) (hin : v ∈ w) :
--   ∃ nt, v = Symbol.nonterminal nt ∧ NullableNonTerminal nt := by sorry

-- lemma l1 {w' w1 w2 : List (Symbol T g.NT)} (h : NullableRelated w' (w1 ++ w2)) :
--   ∃ w1' w2', w' = w1' ++ w2' ∧ NullableRelated w1' w1 ∧ NullableRelated w2' w2 := by sorry

lemma l2 {r : ContextFreeRule T g.NT} {o' : List (Symbol T g.NT)} (hrin : r ∈ g.rules)
  (h : NullableRelated o' r.output) (hneq : o' ≠ []) : { input := r.input, output := o' } ∈ (@eliminate_empty T g).rules := by
  unfold eliminate_empty
  simp
  unfold remove_nullables
  rw [List.mem_join]
  use (remove_nullable_rule compute_nullables r)
  constructor
  rw [List.mem_map]
  use r
  unfold remove_nullable_rule
  rw [List.mem_filterMap]
  use o'
  constructor
  · apply k3
    exact h
    intro s hs
    apply (compute_nullables_iff _).1
    exact hs
  · cases h : o' <;> simp
    contradiction

-- FIXME I need to find the right spots for saying that the output of the nullable related rule is non empty.
-- Potentially saying that the original rules is also not empty...

-- lemma l3 {r : ContextFreeRule T g.NT} {v w w' : List (Symbol T g.NT)} (hr : r.Rewrites v w)
--   (hn1 : NullableRelated w' w) :
--   ∃ (r' : ContextFreeRule T g.NT), ∃ v', NullableRelated r'.output r.output
--            ∧ r.input = r'.input
--            ∧ NullableRelated v' v
--            ∧ r'.Rewrites v' w' := by
--   revert w'
--   induction hr with
--   | head v =>
--     intro w' hn1
--     obtain ⟨w1', w2', heq, hn1, hn2⟩:= l1 hn1
--     use { input := r.input, output := w1' }, (Symbol.nonterminal r.input :: w2')
--     simp
--     constructor <;> try trivial
--     constructor
--     · constructor
--       exact hn2
--     · rw [heq]
--       constructor
--   | @cons v1 vs1 vs2 _ ih =>
--     intro w' hn1
--     cases hn1 with
--     | empty_left ys h =>
--       have h' := k1 (k5 h)
--       simp at h'
--       obtain ⟨r', v', h1, h2, h3, h4⟩ := @ih [] h'
--       use r', v'
--       repeat (constructor <;> try assumption)
--       obtain ⟨nt, heq, hn⟩ := l0 h (List.mem_cons_self v1 vs2)
--       rw [heq]
--       constructor
--       exact h3
--       exact hn
--     | cons_term w' _ h t =>
--       obtain ⟨r', v', h1, h2, h3, h4⟩ := @ih w' h
--       use r', Symbol.terminal t :: v'
--       repeat (constructor <;> try assumption)
--     | cons_nterm_match w' _ h nt =>
--       obtain ⟨r', v', h1, h2, h3, h4⟩ := @ih w' h
--       use r', Symbol.nonterminal nt :: v'
--       repeat (constructor <;> try assumption)
--     | cons_nterm_nullable w' _ h nt =>
--       obtain ⟨r', v', h1, h2, h3, h4⟩ := @ih w' h
--       use r', v'
--       repeat (constructor <;> try assumption)


-- lemma l3' {r : ContextFreeRule T g.NT} {v w w' : List (Symbol T g.NT)} (hr : r.Rewrites v w)
--   (hn1 : NullableRelated w' w) (h : r.output ≠ []) :
--   ∃ (r' : ContextFreeRule T g.NT), ∃ v', NullableRelated r'.output r.output
--            ∧ r.input = r'.input
--            ∧ NullableRelated v' v
--            ∧ r'.Rewrites v' w'
--            ∧ r'.output ≠ [] := by
--   revert w'
--   induction hr with
--   | head v =>
--     intro w' hn1
--     obtain ⟨w1', w2', heq, hn1, hn2⟩:= l1 hn1
--     cases w1' with
--     | nil =>
--       cases h : r.output with
--       | nil => contradiction
--       | cons hd tl =>
--         use { input := r.input, output := hd :: tl }, w2'
--         simp
--         sorry

--       use { input := r.input, output := w2' }, w2'
--       simp
--       sorry
--     | cons hd tl =>
--       use { input := r.input, output := hd :: tl }, (Symbol.nonterminal r.input :: w2')
--       simp
--       constructor <;> try trivial
--       constructor
--       · constructor
--         exact hn2
--       · rw [heq]
--         constructor
--   | @cons v1 vs1 vs2 _ ih =>
--     intro w' hn1
--     cases hn1 with
--     | empty_left ys h =>
--       have h' := k1 (k5 h)
--       simp at h'
--       obtain ⟨r', v', h1, h2, h3, h4⟩ := @ih [] h'
--       use r', v'
--       repeat (constructor <;> try assumption)
--       obtain ⟨nt, heq, hn⟩ := l0 h (List.mem_cons_self v1 vs2)
--       rw [heq]
--       constructor
--       exact h3
--       exact hn
--     | cons_term w' _ h t =>
--       obtain ⟨r', v', h1, h2, h3, h4⟩ := @ih w' h
--       use r', Symbol.terminal t :: v'
--       repeat (constructor <;> try assumption)
--     | cons_nterm_match w' _ h nt =>
--       obtain ⟨r', v', h1, h2, h3, h4⟩ := @ih w' h
--       use r', Symbol.nonterminal nt :: v'
--       repeat (constructor <;> try assumption)
--     | cons_nterm_nullable w' _ h nt =>
--       obtain ⟨r', v', h1, h2, h3, h4⟩ := @ih w' h
--       use r', v'
--       repeat (constructor <;> try assumption)


lemma l4 {w : List (Symbol T g.NT)} (h : g.Derives [] w) : w = [] := by sorry

omit [DecidableEq g.NT] in
lemma l5 {w : List (Symbol T g.NT)} (h : NullableRelated w []) : w = [] := by
  cases h with
  | empty_left => rfl


lemma j4 {w1' w2' w3' w1 w2 w3 : List (Symbol T g.NT)} (h1 : NullableRelated w1' w1)
  (h2 : NullableRelated w2' w2) (h3 : NullableRelated w3' w3) :
  NullableRelated (w1' ++ w2' ++ w3') (w1 ++ w2 ++ w3) := by sorry

lemma j5 {w' w1 w2 w3 : List (Symbol T g.NT)} (h : NullableRelated w' (w1 ++ w2 ++ w3)) :
  ∃ w1' w2' w3', w' = w1' ++ w2' ++ w3' ∧ NullableRelated w1' w1
                 ∧ NullableRelated w2' w2 ∧ NullableRelated w3' w3 := by sorry

lemma empty_related_produces_derives'' {v w w': List (Symbol T g.NT)} (hp : g.Produces v w)
  (hn : NullableRelated w' w) : ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w' := by
  unfold Produces at hp
  obtain ⟨r, hrin, hr⟩ := hp
  rw[r.rewrites_iff] at hr
  obtain ⟨p,q, hv, hw⟩ := hr
  rw [hw] at hn
  obtain ⟨w1', w2', w3', heq, hw1, hw2, hw3⟩ := j5 hn
  cases w2' with
  | nil =>
    use w'
    constructor
    · rw [hv, heq]
      apply j4 hw1 _ hw3
      apply k1
      apply Produces.trans_derives
      apply rewrites_produces hrin
      exact k4 hw2
    · rfl
  | cons hd tl =>
    use (w1' ++ [Symbol.nonterminal r.input] ++ w3')
    constructor
    · rw[hv]
      apply j4 hw1 _ hw3
      rfl
    · rw [heq]
      apply Produces.single
      have hneq : (hd :: tl) ≠ [] := by simp
      have h := l2 hrin hw2 hneq
      let r' : ContextFreeRule T g.NT := { input := r.input, output := hd :: tl }
      use r'
      constructor
      exact h
      change r'.Rewrites (w1' ++ [Symbol.nonterminal r'.input] ++ w3') (w1' ++ r'.output ++ w3')
      apply ContextFreeRule.rewrites_of_exists_parts

-- lemma empty_related_produces_derives' {v w w': List (Symbol T g.NT)} (hp : g.Produces v w)
--   (hn : NullableRelated w' w) : ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w' := by
--   unfold Produces at hp
--   obtain ⟨r, hrin, hr⟩ := hp
--   cases h' : r.output with
--   | nil =>
--     use w'
--     constructor
--     · rw [r.rewrites_iff] at hr
--       obtain ⟨p, q, hv, hw⟩ := hr
--       rw [hv]
--       apply k2
--       apply Produces.single
--       nth_rewrite 2 [← h']
--       exact rewrites_produces hrin
--       rw [h'] at hw
--       simp at hw
--       rw [←hw]
--       exact hn
--     · rfl
--   | cons hd tl =>
--     have h : r.output ≠ [] := by rw [h']; simp
--     obtain ⟨r', v', hn', hneq, hn'', hr', hneq'⟩ := l3' hr hn h
--     use v'
--     constructor
--     exact hn''
--     apply Produces.single
--     use r'
--     constructor
--     have h := l2 hrin hn' hneq'
--     obtain ⟨⟩ := r'
--     simp at *
--     rw [hneq] at h
--     apply h
--     exact hr'

-- lemma empty_related_produces_derives {v w w': List (Symbol T g.NT)} (hp : g.Produces v w)
--   (hn : NullableRelated w' w) : ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w' := by
--   unfold Produces at hp
--   obtain ⟨r, hrin, hr⟩ := hp
--   cases h' : r.output with
--   | nil =>
--     use w'
--     constructor
--     · rw [r.rewrites_iff] at hr
--       obtain ⟨p, q, hv, hw⟩ := hr
--       rw [hv]
--       apply k2
--       apply Produces.single
--       nth_rewrite 2 [← h']
--       exact rewrites_produces hrin
--       rw [h'] at hw
--       simp at hw
--       rw [←hw]
--       exact hn
--     · rfl
--   | cons hd tl =>
--     obtain ⟨r', v', hn', hneq, hn'', hr'⟩ := l3 hr hn
--     use v'
--     constructor
--     exact hn''
--     apply Produces.single
--     use r'
--     constructor
--     have h := l2 hrin hn'
--     obtain ⟨⟩ := r'
--     simp at *
--     rw [hneq] at h
--     apply h
--     sorry
--     sorry
--     rw [h']
--     simp
--     exact hr'

lemma implies_eliminate_empty_related {v w : List (Symbol T g.NT)} (hneq : w ≠ []) {n : ℕ}
  (h : g.DerivesIn v w n) :
  ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w := by
  cases n with
  | zero =>
    cases h
    use v
  | succ n =>
    obtain ⟨u, huv, hvw⟩ := h.head_of_succ
    obtain ⟨u', hru', huw'⟩ := @implies_eliminate_empty_related _ _ hneq _ hvw
    obtain ⟨v', hvrv', hpv'u'⟩ := empty_related_produces_derives'' huv hru'
    use v'
    constructor
    exact hvrv'
    exact Derives.trans hpv'u' huw'

lemma implies_eliminate_empty {w : List (Symbol T g.NT)} {v : g.NT} {hneq : w ≠ []} {n : ℕ}
  (h : g.DerivesIn [Symbol.nonterminal v] w n) :
  (@eliminate_empty T g).Derives [Symbol.nonterminal v] w := by
  obtain ⟨w', hw', hw'w⟩ := implies_eliminate_empty_related hneq h
  cases hw'
  · rename_i h
    obtain ⟨h1, h1⟩ := Derives.eq_or_head hw'w
    · contradiction
    · apply l4 at hw'w
      contradiction
  · rename_i h
    cases h
    exact hw'w
  · rename_i h
    apply l5 at h
    rw [h] at hw'w
    apply l4 at hw'w
    contradiction

theorem eliminate_empty_correct :
  g.language = (@eliminate_empty T g).language \ {[]} := by
  sorry

end ContextFreeGrammar
