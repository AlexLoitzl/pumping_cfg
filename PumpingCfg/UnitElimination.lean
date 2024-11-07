/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.EpsilonElimination

namespace ContextFreeGrammar

variable {T : Type}
variable {g : ContextFreeGrammar T}

section UnitPairs

abbrev unitRule (v1 v2 : g.NT) : ContextFreeRule T g.NT := ContextFreeRule.mk v1 [Symbol.nonterminal v2]

inductive UnitPair : g.NT → g.NT → Prop :=
  | refl (v : g.NT) : UnitPair v v
  | trans {v1 v2 v3 : g.NT} (hr : unitRule v2 v3 ∈ g.rules)
         (hu : UnitPair v1 v2): UnitPair v1 v3

@[refl]
lemma UnitPair.rfl {v1 : g.NT} : UnitPair v1 v1 := UnitPair.refl v1

lemma unitPair.derives {v1 v2 : g.NT} (h : UnitPair v1 v2) :
  g.Derives [Symbol.nonterminal v1] [Symbol.nonterminal v2] := by
  induction h with
  | refl => rfl
  | trans hr _ ih =>
    constructor
    exact ih
    constructor
    constructor
    exact hr
    unfold unitRule
    constructor

end UnitPairs

section ComputUnitPairs

variable [DecidableEq g.NT]

--  Single round of fixpoint iteration
--  Add all rules' lefthand variable if all output symbols are in the set of nullable symbols
def add_unitPairs (pairs : Finset (g.NT × g.NT)) : Finset (g.NT × g.NT) := {}
  -- g.rules.attach.foldr (fun ⟨r, _⟩ => add_if_nullable r) nullable

lemma add_unitPairs_subset_generators_prod (pairs : Finset (g.NT × g.NT)) (p : pairs ⊆ g.generators ×ˢ g.generators) :
  add_unitPairs pairs ⊆ g.generators ×ˢ g.generators := by sorry
  -- unfold add_nullables
  -- induction g.rules.attach with
  -- | nil => simp; exact p
  -- | cons hd tl ih => exact add_if_nullable_subset_generators ih hd.2

lemma add_unitPairs_grows (pairs : Finset (g.NT × g.NT)) :
  pairs ⊆ (add_unitPairs pairs) := by sorry
  -- unfold add_nullables
  -- induction g.rules.attach with
  -- | nil => simp
  -- | cons hd tl ih =>
  --   apply subset_trans ih
  --   apply add_if_nullable_subset hd.1

-- Proof of our termination measure shrinking
lemma generators_prod_limits_unitPairs (pairs : Finset (g.NT × g.NT)) (p : pairs ⊆ g.generators ×ˢ g.generators)
  (hneq : pairs ≠ add_unitPairs pairs) :
  (g.generators ×ˢ g.generators).card - (add_unitPairs pairs).card < (g.generators ×ˢ g.generators).card - pairs.card := by sorry
  -- have h := HasSubset.Subset.ssubset_of_ne (add_nullables_grows nullable) hneq
  -- apply Nat.sub_lt_sub_left
  -- · apply Nat.lt_of_lt_of_le
  --   · apply Finset.card_lt_card h
  --   · exact Finset.card_le_card (add_nullables_subset_generators nullable p)
  -- · apply Finset.card_lt_card h

def add_unit_pairs_iter (pairs : Finset (g.NT × g.NT)) (p : pairs ⊆ g.generators ×ˢ g.generators) : Finset (g.NT × g.NT) :=
  let pairs' := add_unitPairs pairs
  if  pairs = pairs' then
    pairs
  else
    add_unit_pairs_iter pairs' (add_unitPairs_subset_generators_prod pairs p)
  termination_by ((g.generators ×ˢ g.generators).card - pairs.card)
  decreasing_by
    rename_i h
    exact generators_prod_limits_unitPairs pairs p h

end ComputUnitPairs

end ContextFreeGrammar
