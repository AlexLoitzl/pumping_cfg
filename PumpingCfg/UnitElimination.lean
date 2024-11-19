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

-- *********************************************************************************************** --
-- ****************************************** Unit Pairs ***************************************** --
-- *********************************************************************************************** --

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
-- Only If direction of the main correctness theorem of compute_unitPairs --
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
-- If direction of the main correctness theorem of compute_unitPairs --
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

-- *********************************************************************************************** --
-- ************************************ Unit Rule Elimination ************************************ --
-- *********************************************************************************************** --

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

-- ************************************************************************ --
-- Only If direction of the main correctness theorem of eliminate_unitRules --
-- ************************************************************************ --

-- -- First we prove that the grammar cannot derive empty (Given the input non-empty)

-- lemma in_remove_nullable_rule {r r': ContextFreeRule T g.NT} {nullable : Finset g.NT}
--   (h: r' ∈ remove_nullable_rule nullable r) : r'.output ≠ [] := by
--   unfold remove_nullable_rule at h
--   rw [List.mem_filterMap] at h
--   obtain ⟨a, h1, h2⟩ := h
--   cases a <;> simp at h2
--   · rw [←h2]
--     simp

-- lemma in_remove_not_epsilon {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
--   (h : r ∈ remove_nullables nullable) : r.output ≠ [] := by
--   unfold remove_nullables at h
--   rw [List.mem_join] at h
--   obtain ⟨l, hlin, hrin⟩ := h
--   rw [List.mem_map] at hlin
--   obtain ⟨r',hr'in, hr'l⟩ := hlin
--   rw [←hr'l] at hrin
--   exact in_remove_nullable_rule hrin

-- lemma produces_not_epsilon {v w : List (Symbol T g.NT)} (h : (g.eliminate_empty).Produces v w) :
--   w ≠ [] := by
--   unfold Produces at h
--   change ∃ r ∈ (remove_nullables compute_nullables), r.Rewrites v w at h
--   obtain ⟨r, hin, hr⟩ := h
--   intro hw
--   rw [hw] at hr
--   apply in_remove_not_epsilon hin
--   exact rewrites_empty_output hr

-- lemma derives_not_epsilon {v w : List (Symbol T g.NT)} (h : (g.eliminate_empty).Derives v w) (he : v ≠ []) :
--   w ≠ [] := by
--   induction h using Relation.ReflTransGen.head_induction_on with
--   | refl => exact he
--   | head hd _ ih =>
--     apply ih
--     exact produces_not_epsilon hd

-- -- Main proof of the only if direction: If the eliminate_empty grammar derives a string,
-- -- it is derivable in the original grammar

-- lemma remove_nullable_related {o o': List (Symbol T g.NT)} (nullable : Finset g.NT)
--   (p : ∀ x ∈ nullable, NullableNonTerminal x) (hin : o ∈ (remove_nullable nullable o')) :
--   NullableRelated o o' := by
--   revert o
--   induction o' with
--   | nil =>
--     intro o hin
--     unfold remove_nullable at hin
--     simp at hin
--     rw [hin]
--   | cons hd tl ih =>
--     intro o hin
--     unfold remove_nullable at hin
--     cases hd with
--     | nonterminal nt =>
--       simp at hin
--       cases hin <;> rename_i h
--       · by_cases h' : nt ∈ nullable <;> simp [h'] at h
--         constructor
--         exact ih h
--         exact p _ h'
--       · obtain ⟨o1, hoin, ho⟩ := h
--         rw [←ho]
--         constructor
--         exact ih hoin
--     | terminal t =>
--       simp at hin
--       obtain ⟨o1, hoin, ho⟩ := hin
--       rw [←ho]
--       constructor
--       exact ih hoin

-- lemma remove_nullable_rule_related {r': ContextFreeRule T g.NT}
--   {r : ContextFreeRule T (@eliminate_empty T g).NT} {h : r ∈ remove_nullable_rule compute_nullables r'} :
--   r.input = r'.input ∧ @NullableRelated _ g r.output r'.output := by
--   unfold remove_nullable_rule at h
--   rw [List.mem_filterMap] at h
--   obtain ⟨o, ho1, ho2⟩ := h
--   cases o <;> simp at ho2
--   rw [←ho2]
--   constructor
--   rfl
--   apply remove_nullable_related
--   intro
--   apply (compute_nullables_iff _).1
--   exact ho1

-- lemma eliminate_empty_rules (r : ContextFreeRule T (@eliminate_empty T g).NT) {h : r ∈ (@eliminate_empty T g).rules} :
--   ∃ r' ∈ g.rules, r.input = r'.input ∧ @NullableRelated _ g r.output r'.output := by
--   unfold eliminate_empty remove_nullables at h
--   simp at h
--   obtain ⟨r', hrin', hr'⟩ := h
--   use r'
--   constructor
--   exact hrin'
--   apply remove_nullable_rule_related
--   exact hr'

-- lemma eliminate_empty_step_derives {v w : List (Symbol T g.NT)} (h : (@eliminate_empty T g).Produces v w) :
--   g.Derives v w := by
--   obtain ⟨r, hrin, hr⟩ := h
--   obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
--   apply Derives.append_right
--   apply Derives.append_left
--   obtain ⟨r', hin, heq, hn⟩ := @eliminate_empty_rules _ _ _ r hrin
--   rw [heq]
--   apply Produces.trans_derives
--   exact rewrites_produces hin
--   apply hn.derives

lemma eliminate_unitRules_implies {v w : List (Symbol T g.NT)}
  (h : (@eliminate_unitRules T g).Derives v w) : g.Derives v w := by sorry
  -- induction h using Relation.ReflTransGen.head_induction_on with
  -- | refl => rfl
  -- | head hp _ ih =>
  --   apply Derives.trans
  --   exact eliminate_empty_step_derives hp
  --   exact ih

-- ******************************************************************* --
-- If direction of the main correctness theorem of eliminate_unitPairs --
-- ******************************************************************* --

-- lemma in_remove_nullable (nullable : Finset g.NT) (output : List (Symbol T g.NT)) :
--   output ∈ remove_nullable nullable output := by
--   induction output with
--   | nil =>
--     unfold remove_nullable
--     simp
--   | cons o output ih =>
--     unfold remove_nullable
--     cases o <;> simp
--     · exact ih
--     · rename_i nt
--       by_cases h : nt ∈ nullable <;> simp [h]
--       · right
--         exact ih
--       · exact ih

-- lemma in_remove_nullables (nullable : Finset g.NT) (r : ContextFreeRule T g.NT) (h : r ∈ g.rules)
--   (ho : r.output ≠ []):
--   r ∈ remove_nullables nullable := by
--   unfold remove_nullables
--   rw [List.mem_join]
--   use (remove_nullable_rule nullable r)
--   constructor
--   · simp
--     use r
--   · unfold remove_nullable_rule
--     rw [List.mem_filterMap]
--     use r.output
--     constructor
--     · apply in_remove_nullable
--     · obtain ⟨rin, rout⟩ := r
--       cases rout
--       contradiction
--       simp

-- lemma nullableRelated_in_remove_nullable {nullable : Finset g.NT} {o o': List (Symbol T g.NT)}
--   (h : NullableRelated o' o) (p : ∀ s, s ∈ nullable ↔ NullableNonTerminal s) :
--   o' ∈ remove_nullable nullable o := by
--   revert o'
--   induction o with
--   | nil =>
--     intro o' h
--     rw [h.empty_empty]
--     unfold remove_nullable
--     exact List.mem_singleton.2 rfl
--   | cons o os ih =>
--     unfold remove_nullable
--     intro o' h
--     cases o with
--     | terminal t =>
--       simp
--       cases h with
--       | empty_left =>
--         rename_i h
--         exfalso
--         exact nullable_not_terminal h
--       | cons_term os' _ h =>
--         use os'
--         constructor
--         · exact ih h
--         · rfl
--     | nonterminal nt =>
--       simp
--       cases h with
--       | empty_left _ h =>
--         left
--         split
--         · apply ih
--           apply NullableRelated.empty_left
--           change NullableWord ([Symbol.nonterminal nt] ++ os) at h
--           exact h.empty_of_append_right
--         · rename_i h'
--           exfalso
--           apply h'
--           rw [p]
--           exact h.empty_of_append_left
--       | cons_nterm_match os' _ h =>
--         right
--         use os'
--         constructor
--         · exact ih h
--         · rfl
--       | cons_nterm_nullable os' _ h _ hn =>
--         left
--         split <;> rename_i h'
--         · exact ih h
--         · exfalso
--           apply h'
--           rw [p]
--           exact hn

-- lemma nullableRelated_rule_in_rules {r : ContextFreeRule T g.NT} {o' : List (Symbol T g.NT)}
--   (hrin : r ∈ g.rules) (h : NullableRelated o' r.output) (hneq : o' ≠ []) :
--   { input := r.input, output := o' } ∈ (@eliminate_empty T g).rules := by
--   unfold eliminate_empty
--   simp
--   unfold remove_nullables
--   rw [List.mem_join]
--   use (remove_nullable_rule compute_nullables r)
--   constructor
--   rw [List.mem_map]
--   use r
--   unfold remove_nullable_rule
--   rw [List.mem_filterMap]
--   use o'
--   constructor
--   · exact nullableRelated_in_remove_nullable h compute_nullables_iff
--   · cases h : o' <;> simp
--     contradiction

-- lemma empty_related_produces_derives {v w w': List (Symbol T g.NT)} (hp : g.Produces v w)
--   (hn : NullableRelated w' w) : ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w' := by
--   unfold Produces at hp
--   obtain ⟨r, hrin, hr⟩ := hp
--   rw [r.rewrites_iff] at hr
--   obtain ⟨p,q, hv, hw⟩ := hr
--   rw [hw] at hn
--   obtain ⟨w1', w2', w3', heq, hw1, hw2, hw3⟩ := hn.append_split_three
--   cases w2' with
--   | nil =>
--     use w'
--     constructor
--     · rw [hv, heq]
--       apply (hw1.append _).append hw3
--       apply NullableRelated.empty_left
--       apply Produces.trans_derives
--       apply rewrites_produces hrin
--       exact hw2.empty_nullable
--     · rfl
--   | cons hd tl =>
--     use (w1' ++ [Symbol.nonterminal r.input] ++ w3')
--     constructor
--     · rw [hv]
--       apply (hw1.append _).append hw3
--       rfl
--     · rw [heq]
--       apply Produces.single
--       have hneq : (hd :: tl) ≠ [] := by simp
--       have h := nullableRelated_rule_in_rules hrin hw2 hneq
--       let r' : ContextFreeRule T g.NT := { input := r.input, output := hd :: tl }
--       use r'
--       constructor
--       exact h
--       change r'.Rewrites (w1' ++ [Symbol.nonterminal r'.input] ++ w3') (w1' ++ r'.output ++ w3')
--       apply ContextFreeRule.rewrites_of_exists_parts

-- lemma implies_eliminate_empty_related {v w : List (Symbol T g.NT)} (hneq : w ≠ []) {n : ℕ}
--   (h : g.DerivesIn v w n) :
--   ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w := by
--   cases n with
--   | zero =>
--     cases h
--     use v
--   | succ n =>
--     obtain ⟨u, huv, hvw⟩ := h.head_of_succ
--     obtain ⟨u', hru', huw'⟩ := @implies_eliminate_empty_related _ _ hneq _ hvw
--     obtain ⟨v', hvrv', hpv'u'⟩ := empty_related_produces_derives huv hru'
--     use v'
--     constructor
--     exact hvrv'
--     exact Derives.trans hpv'u' huw'

-- lemma implies_eliminate_empty {w : List (Symbol T g.NT)} {v : g.NT} {hneq : w ≠ []} {n : ℕ}
--   (h : g.DerivesIn [Symbol.nonterminal v] w n) :
--   (@eliminate_empty T g).Derives [Symbol.nonterminal v] w := by
--   obtain ⟨w', hw', hw'w⟩ := implies_eliminate_empty_related hneq h
--   cases hw'
--   · rename_i h
--     obtain ⟨h1, h1⟩ := Derives.eq_or_head hw'w
--     · contradiction
--     · apply Derives.empty_empty at hw'w
--       contradiction
--   · rename_i h
--     cases h
--     exact hw'w
--   · rename_i h
--     apply NullableRelated.empty_empty at h
--     rw [h] at hw'w
--     apply Derives.empty_empty at hw'w
--     contradiction

-- Main correctness theorem of eliminate_unitRules
theorem eliminate_unitRules_correct:
  g.language = (@eliminate_unitRules T g).language := by sorry

end EliminateUnitRules

end ContextFreeGrammar
