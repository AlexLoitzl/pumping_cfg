/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.EpsilonElimination

universe uN uT
namespace ContextFreeGrammar

variable {T : Type uT}

section Stuff

variable {g : ContextFreeGrammar.{uN, uT} T}

lemma Produces.rule {n : g.NT} {u : List (Symbol T g.NT)}
    (hnu : g.Produces [Symbol.nonterminal n] u) :
    ⟨n, u⟩ ∈ g.rules := by
  obtain ⟨_, _, hr⟩ := hnu
  cases hr
  · rwa [List.append_nil]
  · contradiction

end Stuff

section UnitPairs

variable {g : ContextFreeGrammar.{uN, uT} T} [DecidableEq g.NT]

abbrev unitRule (nᵢ nₒ : g.NT) : ContextFreeRule T g.NT := ⟨nᵢ, [Symbol.nonterminal nₒ]⟩

/-- `UnitPair n₁ n₂`, (w.r.t. a ContextFreeGrammar `g`) means that `g` can derive `n₂` from
 `n₁` only using unitRules -/
inductive UnitPair : g.NT → g.NT → Prop where
  /- UnitPair is reflexive due to the empty derivation -/
  | refl {n : g.NT} (hng : n ∈ g.generators) : UnitPair n n
  /- UnitPair is transitive -/
  | trans {n₁ n₂ n₃ : g.NT} (hng : unitRule n₁ n₂ ∈ g.rules) (hnn : UnitPair n₂ n₃) : UnitPair n₁ n₃

@[refl]
lemma UnitPair.rfl {n : g.NT} (hn : n ∈ g.generators) : UnitPair n n := UnitPair.refl hn

lemma UnitPair.derives {n₁ n₂ : g.NT} (hnn : UnitPair n₁ n₂) :
    g.Derives [Symbol.nonterminal n₁] [Symbol.nonterminal n₂] := by
  induction hnn with
  | refl => rfl
  | trans hr _ ih => exact Produces.trans_derives ⟨_, hr, ContextFreeRule.Rewrites.head []⟩ ih

/- We use this to concisely state a rule is not a `unitRule` if it's output is NonUnit -/
abbrev NonUnit {N : Type*} (u : List (Symbol T N)) : Prop :=
  match u with
  | [Symbol.nonterminal _] => False
  | _ => True

lemma DerivesIn.unitPair_prefix {u : List T} {v : List (Symbol T g.NT)} {n : g.NT} {k : ℕ}
    (hvu : g.DerivesIn v (List.map Symbol.terminal u) k) (hng : n ∈ g.generators)
    (hv : [Symbol.nonterminal n] = v) :
    ∃ n' w m,
      UnitPair n n' ∧ g.Produces [Symbol.nonterminal n'] w ∧ NonUnit w ∧ m ≤ k
      ∧ g.DerivesIn w (List.map Symbol.terminal u) m := by
  induction hvu using DerivesIn.head_induction_on generalizing n with
  | refl =>
    cases u <;> simp only
      [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, List.nil_eq, List.map_eq_nil_iff,
      false_and] at hv
  | @head m v w hvw hwu ih =>
    by_cases hw : NonUnit w
    · use n, w, m, UnitPair.rfl hng
      rw [hv]
      exact ⟨hvw, hw, m.le_succ, hwu⟩
    · unfold NonUnit at hw
      match w with
      | [Symbol.nonterminal n'] =>
        have hn' : n' ∈ g.generators := by
          cases m with
          | zero => cases u <;> cases hwu
          | succ =>
            obtain ⟨w', hgw', _⟩ := hwu.head_of_succ
            exact nonterminal_in_generators hgw'.rule rfl
        obtain ⟨v'', w', m, hnv'', hgv'', hw', hm, hgw'⟩ := ih hn' rfl
        use v'', w', m
        constructor
        · constructor
          · rw [←hv] at hvw
            exact hvw.rule
          · exact hnv''
        · exact ⟨hgv'', hw', Nat.le_succ_of_le hm, hgw'⟩
      | [Symbol.terminal _] => simp at hw
      | [] => simp at hw
      | _ :: _ :: _ => simp at hw

end UnitPairs

-- *********************************************************************************************** --
-- ****************************************** Unit Pairs ***************************************** --
-- *********************************************************************************************** --

/-! Fixpoint iteration to compute all UnitPairs. -/
section ComputeUnitPairs

variable {g : ContextFreeGrammar.{uN,uT} T} [DecidableEq g.NT]

noncomputable def generators_prod_diag : Finset (g.NT × g.NT) :=
  (g.rules.toList.map (fun r ↦ (r.input, r.input))).toFinset

lemma generators_prod_diag_subset : g.generators_prod_diag ⊆ g.generators ×ˢ g.generators := by
  unfold generators_prod_diag generators
  cases g.rules.toList with
  | nil => simp
  | cons d l =>
    simp only [List.map_cons, List.toFinset_cons]
    intro p hp
    simp only [Finset.mem_insert, List.mem_toFinset, List.mem_map] at hp
    cases hp with
    | inl hpd =>
      simp [Finset.mem_product, hpd]
    | inr hlp =>
      obtain ⟨p', hp', hpp⟩ := hlp
      simp only [← hpp, Finset.mem_product, Finset.mem_insert, List.mem_toFinset, List.mem_map,
        and_self]
      right
      use p'

lemma generators_prod_diag_unitPairs {p : g.NT × g.NT} (hp : p ∈ g.generators_prod_diag) :
    UnitPair p.1 p.2 := by
  unfold generators_prod_diag at hp
  revert hp
  cases heq : g.rules.toList with
  | nil => tauto
  | cons r l =>
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, List.mem_map]
    intro hp
    cases hp with
    | inl hpr =>
      rw [hpr]
      change UnitPair r.input r.input
      constructor
      apply input_in_generators
      rw [←Finset.mem_toList, heq]
      exact List.mem_cons_self r l
    | inr hap =>
      obtain ⟨v, hvl, hvp⟩ := hap
      rw [← hvp]
      constructor
      apply input_in_generators
      rw [←Finset.mem_toList, heq]
      exact List.mem_cons_of_mem r hvl

def collect_unitPair (nᵢ nₒ : g.NT) (p : g.NT × g.NT) (S : Finset (g.NT × g.NT)) :=
  if nₒ = p.1 then insert (nᵢ, p.2) S else S

def collect_unitPairs (r : ContextFreeRule T g.NT) (S : List (g.NT × g.NT)) :=
  match r.output with
  | [Symbol.nonterminal v] => S.foldr (collect_unitPair r.input v) {}
  | _ => {}

lemma rec_collect_unitPairs_unitPairs {nᵢ nₒ : g.NT} {p : g.NT × g.NT}
    {L : List (g.NT × g.NT)} {S : Finset (g.NT × g.NT)}
    (hp : p ∈ L.foldr (collect_unitPair nᵢ nₒ) S) :
    p ∈ S ∨ ∃ v, (nₒ, v) ∈ L ∧ p = (nᵢ, v) := by
  revert S
  induction L with
  | nil =>
    intro S hp
    left
    exact hp
  | cons d l ih =>
    intro S
    unfold collect_unitPair
    simp only [List.foldr_cons, List.mem_cons]
    split <;> (rename_i hd; intro hp)
    · simp only [Finset.mem_insert] at hp
      cases hp with
      | inl hpd =>
        right
        use d.2
        constructor
        · left
          rw [hd]
        · exact hpd
      | inr hpS =>
        specialize ih hpS
        cases ih with
        | inl => left; assumption
        | inr hlp =>
          obtain ⟨v, hvl, hpv⟩ := hlp
          right
          use v
          rw [hpv]
          exact ⟨Or.inr hvl, rfl⟩
    · specialize ih hp
      cases ih with
      | inl => left; assumption
      | inr hlp =>
        obtain ⟨v, hvl, hpv⟩ := hlp
        right
        use v
        rw [hpv]
        exact ⟨Or.inr hvl, rfl⟩

lemma collect_unitPairs_unitPair {r : ContextFreeRule T g.NT} (S : List (g.NT × g.NT))
    (hrg : r ∈ g.rules) (hp : ∀ p ∈ S, UnitPair p.1 p.2) :
    ∀ p ∈ collect_unitPairs r S, UnitPair p.1 p.2 := by
  intro p hprS
  unfold collect_unitPairs at hprS
  match hro : r.output with
  | [Symbol.nonterminal v] =>
    rw [hro] at hprS
    simp only at hprS
    have hp' := rec_collect_unitPairs_unitPairs hprS
    cases hp' <;> rename_i hp''; contradiction
    obtain ⟨v', hS, hpr⟩ := hp''
    constructor
    · unfold unitRule
      rw [← hro, hpr]
      exact hrg
    · rw [hpr]
      exact (hp _ hS)
  | [] => simp [hro] at hprS
  | [Symbol.terminal _ ] => simp [hro] at hprS
  | _ :: _ :: _ => simp [hro] at hprS

noncomputable def add_unitPairs (S : Finset (g.NT × g.NT)) : Finset (g.NT × g.NT) :=
  g.rules.toList.attach.foldr (fun r p ↦ collect_unitPairs r S.toList ∪ p) S

lemma collect_unitPairs_subset_generators_prod {r : ContextFreeRule T g.NT}
    (S : Finset (g.NT × g.NT)) (hSg : S ⊆ g.generators ×ˢ g.generators)
    (hrg : r ∈ g.rules) :
    collect_unitPairs r S.toList ⊆ g.generators ×ˢ g.generators := by
  unfold collect_unitPairs
  intro p hp
  match heq : r.output with
  | [Symbol.nonterminal v] =>
    rw [heq] at hp
    simp at hp
    obtain hpp := rec_collect_unitPairs_unitPairs hp
    cases hpp
    · contradiction
    rw [Finset.mem_product]
    rename_i hp'
    obtain ⟨v', hvS, hp2⟩ := hp'
    rw [hp2]
    simp only
    constructor
    · exact input_in_generators hrg
    · rw [Finset.mem_toList] at hvS
      specialize hSg hvS
      rw[Finset.mem_product] at hSg
      exact hSg.2
  | [] => simp [heq] at hp
  | [Symbol.terminal _] => simp [heq] at hp
  | x :: y :: tl => simp [heq] at hp

lemma add_unitPairs_subset_generators_prod (S : Finset (g.NT × g.NT))
    (hsub : S ⊆ g.generators ×ˢ g.generators) :
    add_unitPairs S ⊆ g.generators ×ˢ g.generators := by
  unfold add_unitPairs
  induction g.rules.toList.attach with
  | nil => exact hsub
  | cons hd tl ih =>
    simp only [List.pure_def, List.bind_eq_flatMap, Finset.mem_toList, List.flatMap_subtype,
      List.flatMap_singleton', List.flatMap_cons, List.singleton_append, List.foldr_cons] at ih ⊢
    exact Finset.union_subset
      (collect_unitPairs_subset_generators_prod _ hsub (Finset.mem_toList.1 hd.2)) ih

lemma add_unitPairs_grows (S : Finset (g.NT × g.NT)) :
  S ⊆ (add_unitPairs S) := by
  unfold add_unitPairs
  induction g.rules.toList.attach with
  | nil => exact fun ⦃a⦄ a ↦ a
  | cons _ _ ih =>
    apply subset_trans ih
    simp

-- Proof of our termination measure shrinking
lemma generators_prod_limits_unitPairs (S : Finset (g.NT × g.NT))
    (hsub : S ⊆ g.generators ×ˢ g.generators) (hne : S ≠ add_unitPairs S) :
    (g.generators ×ˢ g.generators).card - (add_unitPairs S).card
      < (g.generators ×ˢ g.generators).card - S.card := by
   have hS := HasSubset.Subset.ssubset_of_ne (add_unitPairs_grows S) hne
   exact Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le (Finset.card_lt_card hS)
     (Finset.card_le_card (add_unitPairs_subset_generators_prod S hsub))) (Finset.card_lt_card hS)

noncomputable def add_unitPairs_iter (S : Finset (g.NT × g.NT))
    (hsub : S ⊆ g.generators ×ˢ g.generators) :
    Finset (g.NT × g.NT) :=
  let S' := add_unitPairs S
  if S = S' then
    S
  else
    add_unitPairs_iter S' (add_unitPairs_subset_generators_prod S hsub)
  termination_by ((g.generators ×ˢ g.generators).card - S.card)
  decreasing_by
    rename_i h
    exact generators_prod_limits_unitPairs S hsub h

-- Compute all unit S of a grammar
noncomputable def compute_unitPairs : Finset (g.NT × g.NT) :=
  add_unitPairs_iter g.generators_prod_diag generators_prod_diag_subset

-- ********************************************************************** --
-- Only If direction of the main correctness theorem of compute_unitPairs --
-- ********************************************************************** --

lemma add_unitPairs_unitPairs (S : Finset (g.NT × g.NT)) (hp : ∀ p ∈ S, UnitPair p.1 p.2) :
    ∀ p ∈ add_unitPairs S, UnitPair p.1 p.2 := by
  unfold add_unitPairs
  induction g.rules.toList.attach with
  | nil =>
    intro p
    simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_nil, List.foldr_nil]
    exact hp p
  | cons d l ih =>
    intro p hpS
    simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, Finset.mem_toList,
      List.flatMap_subtype, List.flatMap_singleton', List.singleton_append, List.foldr_cons,
      Finset.mem_union] at hpS
    cases hpS with
    | inl hpdS =>
      apply collect_unitPairs_unitPair S.toList (Finset.mem_toList.1 d.2) _ _ hpdS
      intro p hp'
      rw [Finset.mem_toList] at hp'
      exact hp p hp'
    | inr hplS =>
      apply ih
      convert hplS
      simp

-- Main correctness result of the only if direction
lemma add_unitPair_iter_only_unitPairs (S : Finset (g.NT × g.NT))
    (hSg : S ⊆ g.generators ×ˢ g.generators) (hp : ∀ p ∈ S, UnitPair p.1 p.2) :
    ∀ p ∈ (add_unitPairs_iter S hSg), UnitPair p.1 p.2 := by
  unfold add_unitPairs_iter
  intro p
  simp only
  split
  · tauto
  · exact add_unitPair_iter_only_unitPairs (add_unitPairs S)
          (add_unitPairs_subset_generators_prod S hSg) (add_unitPairs_unitPairs S hp) p
  termination_by ((g.generators ×ˢ g.generators).card - S.card)
  decreasing_by
    rename_i hS
    exact generators_prod_limits_unitPairs S hSg hS

-- ***************************************************************** --
-- If direction of the main correctness theorem of compute_unitPairs --
-- ***************************************************************** --

lemma add_unitPairs_add_unitPairs_iter (S : Finset (g.NT × g.NT))
    (hSg : S ⊆ g.generators ×ˢ g.generators) :
    add_unitPairs_iter S hSg = add_unitPairs (add_unitPairs_iter S hSg) := by
  unfold add_unitPairs_iter
  simp only
  split <;> rename_i h
  · exact h
  · apply add_unitPairs_add_unitPairs_iter
  termination_by ((g.generators ×ˢ g.generators).card - S.card)
  decreasing_by
    rename_i hS
    exact generators_prod_limits_unitPairs S hSg hS

lemma add_unitPairs_iter_grows {S : Finset (g.NT × g.NT)}
    {gSg : S ⊆ g.generators ×ˢ g.generators} :
    S ⊆ (add_unitPairs_iter S gSg) := by
  unfold add_unitPairs_iter
  intro p hpS
  simp only
  split
  · exact hpS
  · apply add_unitPairs_iter_grows (add_unitPairs_grows _ hpS)
  termination_by ((g.generators ×ˢ g.generators).card - S.card)
  decreasing_by
    rename_i hS
    exact generators_prod_limits_unitPairs S gSg hS

lemma in_collect_unitPairs {S : List (g.NT × g.NT)} {n₁ n₂ n₃ : g.NT}
    (hS : (n₂, n₃) ∈ S) :
    (n₁, n₃) ∈ collect_unitPairs (unitRule n₁ n₂) S := by
  unfold collect_unitPairs
  induction S with
  | nil => contradiction
  | cons d l ih =>
    simp only [List.mem_cons, List.foldr_cons] at hS ⊢
    unfold collect_unitPair
    cases hS with
    | inl hd =>
      simp [← hd]
    | inr hl =>
      split
      · simp only [Finset.mem_insert, Prod.mk.injEq, true_and]
        right
        exact ih hl
      · exact ih hl

lemma in_add_unitPairs {S : Finset (g.NT × g.NT)} {n₁ n₂ n₃ : g.NT}
    (hS : (n₂, n₃) ∈ S)
    (hg : ⟨n₁, [Symbol.nonterminal n₂]⟩ ∈ g.rules) :
    (n₁, n₃) ∈ add_unitPairs S := by
  unfold add_unitPairs
  have hgnn := g.rules.toList.mem_attach ⟨_, Finset.mem_toList.2 hg⟩
  revert hgnn n₂ S
  induction g.rules.toList.attach with
  | nil =>
    intro S n₂ _ hg h
    contradiction
  | cons r t ih =>
    intro S v2 hS hg h
    cases h
    · simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, Finset.mem_toList,
        List.flatMap_subtype, List.flatMap_singleton', List.singleton_append, List.foldr_cons,
        Finset.mem_union]
      left
      rw [← Finset.mem_toList] at hS
      exact in_collect_unitPairs hS
    · simp only [List.pure_def, List.bind_eq_flatMap, Finset.mem_toList, List.flatMap_subtype,
        List.flatMap_singleton', List.flatMap_cons, List.singleton_append, List.foldr_cons,
        Finset.mem_union] at ih ⊢
      rename_i ht
      exact Or.inr (ih hS hg ht)

lemma unitPair_in_add_unitPairs_iter {S : Finset (g.NT × g.NT)} {n₁ n₂ : g.NT}
    (hSg : S ⊆ g.generators ×ˢ g.generators) (hgsub : generators_prod_diag ⊆ S)
    (hp : UnitPair n₁ n₂) :
    (n₁, n₂) ∈ add_unitPairs_iter S hSg := by
  induction hp with
  | refl hvg =>
    apply Finset.mem_of_subset add_unitPairs_iter_grows
    apply Finset.mem_of_subset hgsub
    unfold generators at hvg
    unfold generators_prod_diag
    rw [List.mem_toFinset, List.mem_map] at hvg ⊢
    obtain ⟨r, hrg, hr⟩ := hvg
    use r
    rw [hr]
    exact ⟨hrg, rfl⟩
  | trans hur hp ih =>
    rw [add_unitPairs_add_unitPairs_iter]
    exact in_add_unitPairs ih hur

-- Main correctness theorem of computing all unit pairs --
lemma compute_unitPairs_iff {n₁ n₂ : g.NT} :
    (n₁, n₂) ∈ compute_unitPairs ↔ UnitPair n₁ n₂ := by
  constructor
  · intro hn
    apply add_unitPair_iter_only_unitPairs g.generators_prod_diag generators_prod_diag_subset _ _ hn
    intro
    exact generators_prod_diag_unitPairs
  · intro hnn
    apply unitPair_in_add_unitPairs_iter _ _ hnn
    rfl

end ComputeUnitPairs

-- *********************************************************************************************** --
-- ************************************ Unit Rule Elimination ************************************ --
-- *********************************************************************************************** --

section EliminateUnitRules

variable {g : ContextFreeGrammar T} [DecidableEq g.NT]

noncomputable def nonUnit_rules (p : g.NT × g.NT) : List (ContextFreeRule T g.NT) :=
  let f (r : ContextFreeRule T g.NT) : Option (ContextFreeRule T g.NT) :=
    if r.input = p.2 then
      match r.output with
      | [Symbol.nonterminal _] => none
      | o => some ⟨p.1, o⟩
    else none
  g.rules.toList.filterMap f

noncomputable def remove_unitRules [DecidableEq T] (S : Finset (g.NT × g.NT)) :=
  ((S.toList).map nonUnit_rules).flatten.toFinset


/- Given `g`, computes a new grammar g' in which all unit rules are removed and for each unit pair
 (`X`, `Y`), i.e., there is a derivation only using unit rules from `X` to `Y`, we add rules
 r : X -> W, if the rule r' : Y -> W is in the grammar (and non unit) -/
noncomputable def eliminate_unitRules [DecidableEq T] (g : ContextFreeGrammar T) [DecidableEq g.NT] :=
  ContextFreeGrammar.mk g.NT g.initial (remove_unitRules compute_unitPairs)

-- ************************************************************************ --
-- Only If direction of the main correctness theorem of eliminate_unitRules --
-- ************************************************************************ --

lemma nonUnit_rules_mem {p : g.NT × g.NT} {r : ContextFreeRule T g.NT} (hrp : r ∈ nonUnit_rules p) :
    r.input = p.1 ∧ ∃ r' ∈ g.rules, r.output = r'.output ∧ r'.input = p.2 := by
  revert hrp
  simp only [List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some,
    forall_exists_index, and_imp, nonUnit_rules]
  intro r' _ _
  split
  · simp
  · rw [Option.some.injEq]
    intro hr
    rw [← hr]
    simp only [true_and]
    use r'

lemma remove_unitRules_stuff [DecidableEq T] {S : Finset (g.NT × g.NT)}
    {r : ContextFreeRule T g.NT} (hrS : r ∈ remove_unitRules S) :
    ∃ p r', p ∈ S ∧ r' ∈ g.rules ∧ r.input = p.1 ∧ r.output = r'.output ∧ r'.input = p.2 := by
  unfold remove_unitRules at hrS
  simp only [List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists]
    at hrS
  obtain ⟨_, ⟨⟨u, v, _, rfl⟩, hruv⟩⟩ := hrS
  obtain ⟨_, ⟨r', _, _, _⟩⟩ := nonUnit_rules_mem hruv
  use (u, v), r'

lemma eliminate_unitRules_implies [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : g.eliminate_unitRules.Derives u v) : g.Derives u v := by
  change List (Symbol T g.eliminate_unitRules.NT) at u v
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    obtain ⟨r, hrin, hr⟩ := hp
    unfold eliminate_unitRules at hrin
    obtain ⟨⟨_, _⟩, r', hpin, hrin', heq1, heq2, heq3⟩ := remove_unitRules_stuff hrin
    simp only at heq1 heq3
    rw [r.rewrites_iff] at hr
    obtain ⟨p, q, hv, hu⟩ := hr
    rw [hv]
    apply Derives.trans
    · apply Derives.append_right
      apply Derives.append_left
      apply Derives.trans_produces
      · rewrite [compute_unitPairs_iff] at hpin
        rewrite [heq1]
        apply hpin.derives
      · rw [← heq3]
        exact rewrites_produces hrin'
    · rwa [← heq2, ←hu]

-- ******************************************************************* --
-- If direction of the main correctness theorem of eliminate_unitPairs --
-- ******************************************************************* --

lemma nonUnit_rules_correct {n₁ n₂ : g.NT} {w : List (Symbol T g.NT)}
    (hg : ⟨n₁, w⟩ ∈ g.rules) (hw : NonUnit w) :
    ⟨n₂, w⟩ ∈ nonUnit_rules (n₂, n₁) := by
  simp only [nonUnit_rules, List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some]
  use ⟨n₁, w⟩
  simp only [true_and]
  use hg
  match w with
  | [Symbol.nonterminal _] => exact False.elim hw
  | [Symbol.terminal _] => rfl
  | [] => rfl
  | _ :: _ :: _ => simp

lemma remove_unitRules_correct [DecidableEq T] {n₁ n₂ : g.NT} {u : List (Symbol T g.NT)}
    {S : Finset (g.NT × g.NT)} (hug : ⟨n₂, u⟩ ∈ g.rules) (hu : NonUnit u)
    (hnn : (n₁, n₂) ∈ S) :
    ⟨n₁, u⟩ ∈ remove_unitRules S := by
  unfold remove_unitRules
  simp only [List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists]
  use nonUnit_rules (n₁, n₂)
  constructor
  · use n₁, n₂
  · exact nonUnit_rules_correct hug hu

lemma eliminate_unitRules_produces [DecidableEq T] {n₁ n₂ : g.NT} {u : List (Symbol T g.NT)}
    (hnn : UnitPair n₁ n₂) (hgu : g.Produces [Symbol.nonterminal n₂] u) (hu : NonUnit u) :
    g.eliminate_unitRules.Produces [Symbol.nonterminal n₁] u := by
  unfold eliminate_unitRules Produces
  constructor -- TODO
  constructor
  exact remove_unitRules_correct hgu.rule hu ((compute_unitPairs_iff).2 hnn)
  nth_rewrite 2 [← u.append_nil]
  exact ContextFreeRule.Rewrites.head []

lemma nonUnit_rules_nonUnit {r : ContextFreeRule T g.NT}
    (hrg : r ∈ g.rules) (hro : NonUnit r.output) :
    r ∈ nonUnit_rules (r.input, r.input) := by
  simp only [nonUnit_rules, List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some]
  use r, hrg
  simp only [true_and]
  match hr : r.output with
  | [Symbol.nonterminal _] => rw [hr] at hro; simp only [NonUnit] at hro
  | [Symbol.terminal _] => simp only [Option.some.injEq]; rw [← hr]
  | [] => simp only [Option.some.injEq]; rw [← hr]
  | _ :: _ :: _ => simp only [Option.some.injEq]; rw [← hr]

variable [DecidableEq T]

lemma nonUnit_in_eliminate_unitRules {r : ContextFreeRule T g.NT}
    (hrg : r ∈ g.rules) (hro : NonUnit r.output) :
    r ∈ g.eliminate_unitRules.rules := by
  simp only [eliminate_unitRules, remove_unitRules,
    List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists]
  refine ⟨nonUnit_rules (r.input, r.input), ⟨r.input, r.input, ?_, rfl⟩,
    nonUnit_rules_nonUnit hrg hro⟩
  rw [compute_unitPairs_iff]
  exact UnitPair.rfl (nonterminal_in_generators hrg rfl)

lemma implies_eliminate_unitRules {u : List (Symbol T g.NT)} {v : List T} {k : ℕ}
    (huv : g.DerivesIn u (List.map Symbol.terminal v) k) :
    g.eliminate_unitRules.Derives u (List.map Symbol.terminal v):= by
  cases k with
  | zero =>
    cases huv
    rfl
  | succ =>
    obtain ⟨u, hp, hd⟩ := huv.head_of_succ
    obtain ⟨r, hr, hru⟩ := hp
    obtain ⟨p, q, hw, hu⟩ := hru.exists_parts
    by_cases hro : NonUnit r.output
    · apply Produces.trans_derives _ (implies_eliminate_unitRules hd)
      exact ⟨r, nonUnit_in_eliminate_unitRules hr hro, hru⟩
    · match hr' : r.output with
      | [Symbol.nonterminal v] =>
        rw [hr'] at hu
        rw [hu] at hd
        obtain ⟨_, _, _, _, m, _, hs, hd1, hd2, hd3, -⟩ := hd.three_split
        obtain ⟨s', s₃, hs', hs'', hs₃⟩ := List.map_eq_append_iff.1 hs
        obtain ⟨s₁, s₂, hs''', hs₁, hs₂⟩ := List.map_eq_append_iff.1 hs''
        rw [← hs₁] at hd1
        rw [← hs₂] at hd2
        rw [← hs₃] at hd3
        rw [hs, hw, ←hs₁, ←hs₂, ←hs₃]
        apply Derives.append_left_trans
        apply implies_eliminate_unitRules hd3
        apply Derives.append_left_trans _ (implies_eliminate_unitRules hd1)
        have hvg : v ∈ g.generators := by
          cases m with
          | zero => cases s₂ <;> cases hd2
          | succ =>
            obtain ⟨w', hp, _⟩ := hd2.head_of_succ
            apply nonterminal_in_generators
            apply hp.rule
            rfl
        obtain ⟨u, w', _, hvu, hp, hw', _, hd2'⟩ := hd2.unitPair_prefix hvg rfl
        apply Produces.trans_derives _ (implies_eliminate_unitRules hd2')
        · apply eliminate_unitRules_produces _ hp hw'
          apply UnitPair.trans _ hvu
          unfold unitRule
          rwa [← hr']
      | [Symbol.terminal _] => rw [hr'] at hro; simp at hro
      | [] => rw [hr'] at hro; simp at hro
      | _ :: _ :: _ => rw [hr'] at hro; simp [NonUnit] at hro

-- Main correctness theorem of `eliminate_unitRules`
theorem eliminate_unitRules_correct :
    g.language = g.eliminate_unitRules.language := by
  unfold language Generates
  have hg : g.eliminate_unitRules.initial = g.initial := rfl
  apply Set.eq_of_subset_of_subset
  · intro w hw
    rw [Set.mem_setOf_eq] at hw
    rw [hg]
    obtain ⟨n, hn⟩ := (derives_iff_derivesIn _ _ _).1 hw
    exact implies_eliminate_unitRules hn
  · intro w hw
    rw [Set.mem_setOf_eq, ←hg]
    exact eliminate_unitRules_implies hw

end EliminateUnitRules

end ContextFreeGrammar
