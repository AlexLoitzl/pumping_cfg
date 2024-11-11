/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.EpsilonElimination

namespace ContextFreeGrammar

variable {T : Type}
variable {g : ContextFreeGrammar.{0,0} T}

section UnitPairs

variable [DecidableEq g.NT]

abbrev unitRule (v1 v2 : g.NT) : ContextFreeRule T g.NT := ContextFreeRule.mk v1 [Symbol.nonterminal v2]

-- FIXME Actually only take things that are generators!
inductive UnitPair : g.NT → g.NT → Prop :=
  | refl (v : g.NT) (h : v ∈ g.generators): UnitPair v v
  | trans {v1 v2 v3 : g.NT} (hr : unitRule v1 v2 ∈ g.rules)
         (hu : UnitPair v2 v3): UnitPair v1 v3

@[refl]
lemma UnitPair.rfl {v1 : g.NT} {h : v1 ∈ generators} : UnitPair v1 v1 := UnitPair.refl v1 h

lemma unitPair.derives {v1 v2 : g.NT} (h : UnitPair v1 v2) :
  g.Derives [Symbol.nonterminal v1] [Symbol.nonterminal v2] := by
  induction h with
  | refl => rfl
  | trans hr _ ih =>
    apply Produces.trans_derives
    constructor
    constructor
    exact hr
    unfold unitRule
    constructor
    exact ih

end UnitPairs

section ComputeUnitPairs

variable [DecidableEq g.NT]

def generators_prod_diag : Finset (g.NT × g.NT) := (g.rules.map (fun r => (r.input, r.input))).toFinset

lemma generators_prod_diag_subset : g.generators_prod_diag ⊆ g.generators ×ˢ g.generators := by
  unfold generators_prod_diag generators
  cases g.rules with
  | nil => simp
  | cons hd tl =>
    simp
    intro p h
    simp at h
    cases h with
    | inl h =>
      rw [Finset.mem_product, h]
      simp
    | inr h =>
      obtain ⟨p', hpin, heq⟩ := h
      repeat rw [←heq]
      simp
      right
      use p'

lemma generators_prod_diag_unitPairs {p : g.NT × g.NT} (h : p ∈ g.generators_prod_diag) : UnitPair p.1 p.2  := by
  unfold generators_prod_diag at h
  revert h
  cases heq : g.rules with
  | nil => tauto
  | cons hd tl =>
    simp
    intro h
    cases h with
    | inl h =>
      rw [h]
      simp
      constructor
      apply in_generators
      rw [heq]
      exact List.mem_cons_self hd tl
    | inr h =>
      obtain ⟨v, hin, hv2⟩ := h
      rw [← hv2]
      simp
      constructor
      apply in_generators
      rw [heq]
      exact List.mem_cons_of_mem hd hin

def collect_unitPair (input output : g.NT) (pair : g.NT × g.NT) (pairs : Finset (g.NT × g.NT)) : Finset (g.NT × g.NT) :=
  if output = pair.1 then insert (input, pair.2) pairs else pairs

def collect_unitPairs (r : ContextFreeRule T g.NT) (pairs : List (g.NT × g.NT)) : Finset (g.NT × g.NT) :=
  match r.output with
  | [Symbol.nonterminal v] => pairs.foldr (collect_unitPair r.input v) {}
  | _ => {}

lemma rec_collect_unitPairs_unitPairs {input output : g.NT} {p : g.NT × g.NT} {pairs : List (g.NT × g.NT)}
  {collection : Finset (g.NT × g.NT)} (h : p ∈ pairs.foldr (collect_unitPair input output) collection) :
  p ∈ collection ∨ ∃ v, (output, v) ∈ pairs ∧ p = (input, v) := by
  revert collection
  induction pairs with
  | nil =>
    intro collection h
    left
    assumption
  | cons hd tl ih =>
    intro collection
    unfold collect_unitPair
    simp
    split <;> (rename_i heq; intro h)
    · simp at h
      cases h with
      | inl h =>
        right
        use hd.2
        constructor
        left
        rw [heq]
        rw[h]
      | inr h =>
        specialize ih h
        cases ih with
        | inl h' => left; assumption
        | inr h' =>
          obtain ⟨v, hv1, hv2⟩ := h'
          right
          use v
          rw [hv2]
          constructor
          right
          assumption
          rfl
    · specialize ih h
      cases ih with
      | inl h' => left; assumption
      | inr h' =>
        obtain ⟨v, hv1, hv2⟩ := h'
        right
        use v
        rw [hv2]
        constructor
        right
        assumption
        rfl

lemma collect_unitPairs_unitPair {r : ContextFreeRule T g.NT} (pairs : List (g.NT × g.NT)) (hrin : r ∈ g.rules)
  (h : ∀ p ∈ pairs, UnitPair p.1 p.2) : ∀ p ∈ collect_unitPairs r pairs, UnitPair p.1 p.2 := by
  intro p h'
  unfold collect_unitPairs at h'
  match heq : r.output with
  | [Symbol.nonterminal v] =>
    rw[heq] at h'
    simp at h'
    have h'' := rec_collect_unitPairs_unitPairs h'
    cases h'' <;> rename_i h''
    contradiction
    obtain ⟨v', h1, h2⟩ := h''
    constructor
    unfold unitRule
    rw [← heq, h2]
    exact hrin
    apply h at h1
    rw [h2]
    exact h1
  | [] =>
    rw[heq] at h'
    simp at h'
  | [Symbol.terminal _ ] =>
    rw[heq] at h'
    simp at h'
  | x :: y :: tl =>
    rw[heq] at h'
    simp at h'

--  Single round of fixpoint iteration
--  Add all rules' lefthand variable if all output symbols are in the set of nullable symbols
noncomputable def add_unitPairs (pairs : Finset (g.NT × g.NT)) : Finset (g.NT × g.NT) :=
  g.rules.attach.foldr (fun r p => collect_unitPairs r pairs.toList ∪ p) pairs

lemma collect_unitPairs_subset_generators_prod {r : ContextFreeRule T g.NT} (pairs : Finset (g.NT × g.NT))
  (hp : pairs ⊆ g.generators ×ˢ g.generators) (hrin : r ∈ g.rules):
  collect_unitPairs r pairs.toList ⊆ g.generators ×ˢ g.generators := by
  unfold collect_unitPairs
  intro p h
  match heq : r.output with
  | [Symbol.nonterminal v] =>
    rw [heq] at h
    simp at h
    obtain h' := rec_collect_unitPairs_unitPairs h
    cases h'
    contradiction
    simp
    rename_i h'
    obtain ⟨v', hin, hp2⟩ := h'
    rw [hp2]
    simp
    constructor
    · exact in_generators hrin
    · rw [Finset.mem_toList] at hin
      specialize hp hin
      simp at hp
      exact hp.2
  | [] =>
    rw [heq] at h
    simp at h
  | [Symbol.terminal _] =>
    rw [heq] at h
    simp at h
  | x :: y :: tl =>
    rw [heq] at h
    simp at h

lemma add_unitPairs_subset_generators_prod (pairs : Finset (g.NT × g.NT)) (p : pairs ⊆ g.generators ×ˢ g.generators) :
  add_unitPairs pairs ⊆ g.generators ×ˢ g.generators := by
  unfold add_unitPairs
  induction g.rules.attach with
  | nil => exact p
  | cons hd tl ih =>
    simp
    apply Finset.union_subset
    · apply collect_unitPairs_subset_generators_prod
      exact p
      exact hd.2
    · exact ih

lemma add_unitPairs_grows (pairs : Finset (g.NT × g.NT)) :
  pairs ⊆ (add_unitPairs pairs) := by
  unfold add_unitPairs
  induction g.rules.attach with
  | nil =>
    simp
  | cons hd tl ih =>
    apply subset_trans ih
    simp
    exact Finset.subset_union_right

-- Proof of our termination measure shrinking
lemma generators_prod_limits_unitPairs (pairs : Finset (g.NT × g.NT)) (p : pairs ⊆ g.generators ×ˢ g.generators)
  (hneq : pairs ≠ add_unitPairs pairs) :
  (g.generators ×ˢ g.generators).card - (add_unitPairs pairs).card < (g.generators ×ˢ g.generators).card - pairs.card := by
   have h := HasSubset.Subset.ssubset_of_ne (add_unitPairs_grows pairs) hneq
   apply Nat.sub_lt_sub_left
   · apply Nat.lt_of_lt_of_le
     · apply Finset.card_lt_card h
     · exact Finset.card_le_card (add_unitPairs_subset_generators_prod pairs p)
   · apply Finset.card_lt_card h

noncomputable def add_unitPairs_iter (pairs : Finset (g.NT × g.NT)) (p : pairs ⊆ g.generators ×ˢ g.generators)
  : Finset (g.NT × g.NT) :=
  let pairs' := add_unitPairs pairs
  if  pairs = pairs' then
    pairs
  else
    add_unitPairs_iter pairs' (add_unitPairs_subset_generators_prod pairs p)
  termination_by ((g.generators ×ˢ g.generators).card - pairs.card)
  decreasing_by
    rename_i h
    exact generators_prod_limits_unitPairs pairs p h


-- Compute all nullable variables of a grammar
noncomputable def compute_unitPairs : Finset (g.NT × g.NT) :=
  add_unitPairs_iter g.generators_prod_diag generators_prod_diag_subset

-- ********************************************************************** --
-- Only If direction of the main correctness theorem of compute_nullables --
-- ********************************************************************** --

lemma add_unitPairs_unitPairs (pairs : Finset (g.NT × g.NT)) (hin : ∀ p ∈ pairs, UnitPair p.1 p.2) :
  ∀ p ∈ add_unitPairs pairs, UnitPair p.1 p.2 := by
  unfold add_unitPairs
  induction g.rules.attach with
  | nil =>
    intro p
    simp
    exact hin p
  | cons hd tl ih =>
    intro p h
    simp at h
    cases h with
    | inl h =>
      apply collect_unitPairs_unitPair pairs.toList
      exact hd.2
      intro p hin'
      apply hin
      rwa[←Finset.mem_toList]
      exact h
    | inr h =>
      apply ih
      exact h

-- Main correctness result of the only if direction
lemma add_unitPair_iter_only_unitPairs (pairs : Finset (g.NT × g.NT))
  (h : pairs ⊆ g.generators ×ˢ g.generators) (hin : ∀ p ∈ pairs, UnitPair p.1 p.2) :
  ∀ p ∈ (add_unitPairs_iter pairs h), UnitPair p.1 p.2 := by
  unfold add_unitPairs_iter
  intro p
  simp
  split
  · tauto
  · apply add_unitPair_iter_only_unitPairs (add_unitPairs pairs)
          (add_unitPairs_subset_generators_prod pairs h)
    exact add_unitPairs_unitPairs pairs hin
  termination_by ((g.generators ×ˢ g.generators).card - pairs.card)
  decreasing_by
    rename_i h'
    exact generators_prod_limits_unitPairs pairs h h'

-- ***************************************************************** --
-- If direction of the main correctness theorem of compute_nullables --
-- ***************************************************************** --

-- lemma subset_add_if_nullable_subset {r: ContextFreeRule T g.NT} {nullable nullable' : Finset g.NT}
--   (p : nullable ⊆ nullable') : add_if_nullable r nullable ⊆ add_if_nullable r nullable' := by
--   intro v hvin
--   unfold add_if_nullable rule_is_nullable at hvin ⊢
--   by_cases  h : decide (∀ s ∈ r.output, symbol_is_nullable nullable s) = true <;> simp [h] at hvin; simp at h
--   · split <;> rename_i h'; simp at h'
--     · cases hvin with
--       | inl h =>
--         rw [h]
--         exact Finset.mem_insert_self r.input nullable'
--       | inr h =>
--         exact Finset.mem_insert_of_mem (p h)
--     · cases hvin with
--       | inl h'' =>
--         unfold symbol_is_nullable at h' h
--         simp at h' h
--         obtain ⟨s, hsin, hs⟩ := h'
--         specialize h s
--         cases s <;> simp at hs h
--         · contradiction
--         · rename_i u
--           apply h at hsin
--           apply p at hsin
--           contradiction
--       | inr h =>
--         exact p h
--   · split
--     · exact Finset.mem_insert_of_mem (p hvin)
--     · exact (p hvin)

-- private lemma add_if_nullable_subset_rec {l : List {x // x ∈ g.rules}} {nullable : Finset g.NT} :
--   nullable ⊆ List.foldr (fun x : {x // x ∈ g.rules} ↦ add_if_nullable ↑x) nullable l := by
--   induction l with
--   | nil => rfl
--   | cons h t ih =>
--     simp
--     apply Finset.Subset.trans ih
--     apply add_if_nullable_subset

-- lemma nullable_in_add_nullables {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
--   (h : rule_is_nullable nullable r) (hr : r ∈ g.rules) : r.input ∈ add_nullables nullable := by
--   unfold add_nullables
--   have h := List.mem_attach g.rules ⟨r, hr⟩
--   revert r nullable
--   induction g.rules.attach with
--   | nil =>
--     intro r nullable _ hrin
--     simp
--   | cons r t ih =>
--     intro r' nullable h hr' hr''
--     cases hr'' <;> simp at ih ⊢
--     · apply Finset.mem_of_subset
--       apply subset_add_if_nullable_subset
--       apply add_if_nullable_subset_rec
--       unfold add_if_nullable
--       simp [h]
--     · rename_i hr''
--       apply Finset.mem_of_subset
--       apply add_if_nullable_subset
--       apply ih h
--       exact hr''

-- lemma add_nullable_add_nullable_iter (nullable: Finset g.NT) (p : nullable ⊆ generators) :
--   add_nullables_iter nullable p = add_nullables (add_nullables_iter nullable p) := by
--   unfold add_nullables_iter
--   simp
--   split <;> rename_i h
--   · exact h
--   · apply add_nullable_add_nullable_iter
--   termination_by ((g.generators).card - nullable.card)
--   decreasing_by
--     rename_i h
--     exact generators_limits_nullable nullable p h

-- lemma nullable_in_compute_nullables (nullable : Finset g.NT) (p : nullable ⊆ generators) (v : g.NT)
--   (n : ℕ) (h: g.DerivesIn [Symbol.nonterminal v] [] n) : v ∈ add_nullables_iter nullable p := by
--   cases n with
--   | zero =>
--     cases h
--   | succ n =>
--     obtain ⟨u, hwu, hue⟩ := h.head_of_succ
--     obtain ⟨r, hrin, hwu⟩ := hwu
--     have h : rule_is_nullable (add_nullables_iter nullable p) r := by
--       have h1 : u = r.output := by
--         obtain ⟨p,q,h1,h2⟩ := (r.rewrites_iff _ _).1 hwu
--         cases p <;> simp at h1
--         cases q <;> simp at h1
--         simp at h2
--         exact h2
--       unfold rule_is_nullable
--       simp
--       intro s hsin
--       rw [←h1] at hsin
--       obtain ⟨v', hv'⟩ := hue.nullable_mem_nonterminal hsin
--       unfold symbol_is_nullable
--       rw [hv']
--       simp
--       have ⟨m,_, hse⟩ := hue.mem_nullable hsin
--       apply nullable_in_compute_nullables
--       rw [←hv']
--       exact hse
--     have h1 : v = r.input := by
--       obtain ⟨p,q,h2,_⟩ := (r.rewrites_iff _ _).1 hwu
--       cases p <;> simp at h2
--       cases q <;> simp at h2
--       exact h2
--     rw [add_nullable_add_nullable_iter]
--     rw [h1]
--     exact nullable_in_add_nullables h hrin

-- Main correctness theorem of computing all unit pairs --
lemma compute_unitPairs_iff (p : g.NT × g.NT) :
  p ∈ compute_unitPairs ↔ UnitPair p.1 p.2 := by
  constructor
  · intro h
    apply add_unitPair_iter_only_unitPairs g.generators_prod_diag generators_prod_diag_subset
    intro p hp
    exact generators_prod_diag_unitPairs hp
    exact h
  · -- intro h
    -- unfold NullableNonTerminal at h
    -- obtain ⟨m, h⟩ := (derives_iff_derivesIn _ _ _).1 h
    -- apply nullable_in_compute_nullables
    -- exact h
    sorry

end ComputeUnitPairs

section EliminateUnitRules


variable [DecidableEq g.NT]

def nonUnit_rules (p : g.NT × g.NT) : List (ContextFreeRule T g.NT) :=
  let fltrMp (r : ContextFreeRule T g.NT) : Option (ContextFreeRule T g.NT) :=
    if r.input = p.2 then
      match r.output with
      | [Symbol.nonterminal _] => none
      | o => ContextFreeRule.mk p.1 o
    else none
  g.rules.filterMap fltrMp

noncomputable def remove_unitRules (pairs : Finset (g.NT × g.NT)) : List (ContextFreeRule T g.NT) :=
  ((pairs.toList).map nonUnit_rules).join

noncomputable def eliminate_unitRules [DecidableEq g.NT] : ContextFreeGrammar T :=
  ContextFreeGrammar.mk g.NT g.initial (remove_unitRules compute_unitPairs)

end EliminateUnitRules

end ContextFreeGrammar
