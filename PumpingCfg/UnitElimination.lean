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

/-- Convenient to talk about the rule rewriting a nonterminal `nᵢ` to another nonterminal nₒ -/
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

/-- We use this to concisely state a rule is not a `unitRule` if it's output is NonUnit -/
abbrev NonUnit {N : Type*} (u : List (Symbol T N)) : Prop :=
  match u with
  | [Symbol.nonterminal _] => False
  | _ => True

lemma DerivesIn.unitPair_prefix {u : List T} {v : List (Symbol T g.NT)} {n : g.NT} {m : ℕ}
    (hvu : g.DerivesIn v (List.map Symbol.terminal u) m) (hng : n ∈ g.generators)
    (hv : [Symbol.nonterminal n] = v) :
    ∃ n' w k,
      UnitPair n n' ∧ g.Produces [Symbol.nonterminal n'] w ∧ NonUnit w ∧ k ≤ m
      ∧ g.DerivesIn w (List.map Symbol.terminal u) k := by
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
            exact input_mem_generators hgw'.rule
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

/-! Fixpoint iteration to compute all UnitPairs. A unit pair is a pair (n₁, n₂) of nonterminals
 s.t. `g` can transform n₁ to n₂ only using unit rules, i.e., a chain of productions rewriting
 nonterminals to nonterminals -/

section ComputeUnitPairs

variable {g : ContextFreeGrammar.{uN,uT} T} [DecidableEq g.NT]

/-- `generators_prod_diag g` is the diagonal of `g.generators × g.generators` -/
noncomputable def generators_prod_diag : Finset (g.NT × g.NT) :=
  (g.rules.toList.map (fun r ↦ (r.input, r.input))).toFinset

lemma generators_prod_diag_subset : g.generators_prod_diag ⊆ g.generators ×ˢ g.generators := by
  unfold generators_prod_diag generators
  cases g.rules.toList with
  | nil => simp
  | cons a l =>
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
      apply input_mem_generators
      rw [←Finset.mem_toList, heq]
      exact List.mem_cons_self r l
    | inr hap =>
      obtain ⟨v, hvl, hvp⟩ := hap
      rw [← hvp]
      constructor
      apply input_mem_generators
      rw [←Finset.mem_toList, heq]
      exact List.mem_cons_of_mem r hvl

/-- Reflects transitivity of unit pairs. If (n₂, n₃) are a unit pair and `g` rewrites n₁ to n₂,
 then (n₁, n₃) are also a unit pair -/
def collect_unitPair (nᵢ nₒ : g.NT) (p : g.NT × g.NT) (l : Finset (g.NT × g.NT)) :=
  if nₒ = p.1 then insert (nᵢ, p.2) l else l

/-- If `r` is a unit rule, add all unit pairs (r.input, n) to `l` for all unit pairs (r.output, n)
  in `l` -/
def collect_unitPairs (r : ContextFreeRule T g.NT) (l : List (g.NT × g.NT)) :=
  match r.output with
  | [Symbol.nonterminal v] => l.foldr (collect_unitPair r.input v) {}
  | _ => {}

lemma rec_collect_unitPairs_unitPairs {nᵢ nₒ : g.NT} {p : g.NT × g.NT} {l : List (g.NT × g.NT)}
    {x : Finset (g.NT × g.NT)} (hp : p ∈ l.foldr (collect_unitPair nᵢ nₒ) x) :
    p ∈ x ∨ ∃ v, (nₒ, v) ∈ l ∧ p = (nᵢ, v) := by
  revert x
  induction l with
  | nil =>
    intro S hp
    left
    exact hp
  | cons a l ih =>
    intro S
    unfold collect_unitPair
    simp only [List.foldr_cons, List.mem_cons]
    split <;> (rename_i hd; intro hp)
    · simp only [Finset.mem_insert] at hp
      cases hp with
      | inl hpd =>
        right
        use a.2
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

lemma collect_unitPairs_unitPair {r : ContextFreeRule T g.NT} (l : List (g.NT × g.NT)) (hrg : r ∈ g.rules)
    (hp : ∀ p ∈ l, UnitPair p.1 p.2) :
    ∀ p ∈ collect_unitPairs r l, UnitPair p.1 p.2 := by
  intro p hprl
  unfold collect_unitPairs at hprl
  match hro : r.output with
  | [Symbol.nonterminal _] =>
    rw [hro] at hprl
    simp only at hprl
    have hp' := rec_collect_unitPairs_unitPairs hprl
    cases hp' <;> rename_i hp''; contradiction
    obtain ⟨v', hl, hpr⟩ := hp''
    constructor
    · unfold unitRule
      rw [← hro, hpr]
      exact hrg
    · rw [hpr]
      exact (hp _ hl)
  | [] => simp [hro] at hprl
  | [Symbol.terminal _ ] => simp [hro] at hprl
  | _ :: _ :: _ => simp [hro] at hprl

/-- Single step of fixpoint iteration, adding unit pairs to `l` for all rules `r` in `g.rules` -/
noncomputable def add_unitPairs (l : Finset (g.NT × g.NT)) : Finset (g.NT × g.NT) :=
  g.rules.toList.attach.foldr (fun r p ↦ collect_unitPairs r l.toList ∪ p) l

lemma collect_unitPairs_subset_generators_prod {r : ContextFreeRule T g.NT} (l : Finset (g.NT × g.NT))
    (hlg : l ⊆ g.generators ×ˢ g.generators) (hrg : r ∈ g.rules) :
    collect_unitPairs r l.toList ⊆ g.generators ×ˢ g.generators := by
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
    obtain ⟨v', hvl, hp2⟩ := hp'
    rw [hp2]
    simp only
    constructor
    · exact input_mem_generators hrg
    · rw [Finset.mem_toList] at hvl
      specialize hlg hvl
      rw[Finset.mem_product] at hlg
      exact hlg.2
  | [] => simp [heq] at hp
  | [Symbol.terminal _] => simp [heq] at hp
  | x :: y :: tl => simp [heq] at hp

lemma add_unitPairs_subset_generators_prod (l : Finset (g.NT × g.NT)) (hlg : l ⊆ g.generators ×ˢ g.generators) :
    add_unitPairs l ⊆ g.generators ×ˢ g.generators := by
  unfold add_unitPairs
  induction g.rules.toList.attach with
  | nil => exact hlg
  | cons hd tl ih =>
    simp only [List.pure_def, List.bind_eq_flatMap, Finset.mem_toList, List.flatMap_subtype,
      List.flatMap_singleton', List.flatMap_cons, List.singleton_append, List.foldr_cons] at ih ⊢
    exact Finset.union_subset
      (collect_unitPairs_subset_generators_prod _ hlg (Finset.mem_toList.1 hd.2)) ih

lemma add_unitPairs_grows (l : Finset (g.NT × g.NT)) : l ⊆ (add_unitPairs l) := by
  unfold add_unitPairs
  induction g.rules.toList.attach with
  | nil => exact fun ⦃a⦄ a ↦ a
  | cons _ _ ih =>
    apply subset_trans ih
    simp

lemma generators_prod_limits_unitPairs (l : Finset (g.NT × g.NT)) (hlg : l ⊆ g.generators ×ˢ g.generators)
    (hne : l ≠ add_unitPairs l) :
    (g.generators ×ˢ g.generators).card - (add_unitPairs l).card
      < (g.generators ×ˢ g.generators).card - l.card := by
   have hl := HasSubset.Subset.ssubset_of_ne (add_unitPairs_grows l) hne
   exact Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le (Finset.card_lt_card hl)
     (Finset.card_le_card (add_unitPairs_subset_generators_prod l hlg))) (Finset.card_lt_card hl)

/-- Fixpoint iteration computing the unit pairs of `g`. -/
noncomputable def add_unitPairs_iter (l : Finset (g.NT × g.NT)) (hlg : l ⊆ g.generators ×ˢ g.generators) :
    Finset (g.NT × g.NT) :=
  let l' := add_unitPairs l
  if l = l' then
    l
  else
    add_unitPairs_iter l' (add_unitPairs_subset_generators_prod l hlg)
  termination_by ((g.generators ×ˢ g.generators).card - l.card)
  decreasing_by
    rename_i h
    exact generators_prod_limits_unitPairs l hlg h

/-- Compute the least-fixpoint of `add_unitPairs_iter`, i.e., all (and only) unit pairs -/
noncomputable def compute_unitPairs : Finset (g.NT × g.NT) :=
  add_unitPairs_iter g.generators_prod_diag generators_prod_diag_subset

-- ********************************************************************** --
-- Only If direction of the main correctness theorem of compute_unitPairs --
-- ********************************************************************** --

lemma add_unitPairs_unitPairs (l : Finset (g.NT × g.NT)) (hl : ∀ p ∈ l, UnitPair p.1 p.2) :
    ∀ p ∈ add_unitPairs l, UnitPair p.1 p.2 := by
  unfold add_unitPairs
  induction g.rules.toList.attach with
  | nil =>
    intro p
    simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_nil, List.foldr_nil]
    exact hl p
  | cons a _ ih =>
    intro p hpl
    simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, Finset.mem_toList,
      List.flatMap_subtype, List.flatMap_singleton', List.singleton_append, List.foldr_cons,
      Finset.mem_union] at hpl
    cases hpl with
    | inl hpdl =>
      apply collect_unitPairs_unitPair l.toList (Finset.mem_toList.1 a.2) _ _ hpdl
      intro p hp'
      rw [Finset.mem_toList] at hp'
      exact hl p hp'
    | inr hpl =>
      apply ih
      convert hpl
      simp

-- Main correctness result of the only if direction
lemma add_unitPair_iter_only_unitPairs (l : Finset (g.NT × g.NT))
    (hlg : l ⊆ g.generators ×ˢ g.generators) (hl : ∀ p ∈ l, UnitPair p.1 p.2) :
    ∀ p ∈ (add_unitPairs_iter l hlg), UnitPair p.1 p.2 := by
  unfold add_unitPairs_iter
  intro p
  simp only
  split
  · tauto
  · exact add_unitPair_iter_only_unitPairs (add_unitPairs l)
          (add_unitPairs_subset_generators_prod l hlg) (add_unitPairs_unitPairs l hl) p
  termination_by ((g.generators ×ˢ g.generators).card - l.card)
  decreasing_by
    rename_i hl
    exact generators_prod_limits_unitPairs l hlg hl

-- ***************************************************************** --
-- If direction of the main correctness theorem of compute_unitPairs --
-- ***************************************************************** --

lemma add_unitPairs_add_unitPairs_iter (l : Finset (g.NT × g.NT)) (hlg : l ⊆ g.generators ×ˢ g.generators) :
    add_unitPairs_iter l hlg = add_unitPairs (add_unitPairs_iter l hlg) := by
  unfold add_unitPairs_iter
  simp only
  split <;> rename_i h
  · exact h
  · apply add_unitPairs_add_unitPairs_iter
  termination_by ((g.generators ×ˢ g.generators).card - l.card)
  decreasing_by
    rename_i hl
    exact generators_prod_limits_unitPairs l hlg hl

lemma add_unitPairs_iter_grows {l : Finset (g.NT × g.NT)}
    {hlg : l ⊆ g.generators ×ˢ g.generators} :
    l ⊆ (add_unitPairs_iter l hlg) := by
  unfold add_unitPairs_iter
  intro p hpl
  simp only
  split
  · exact hpl
  · apply add_unitPairs_iter_grows (add_unitPairs_grows _ hpl)
  termination_by ((g.generators ×ˢ g.generators).card - l.card)
  decreasing_by
    rename_i hl
    exact generators_prod_limits_unitPairs l hlg hl

lemma in_collect_unitPairs {l : List (g.NT × g.NT)} {n₁ n₂ n₃ : g.NT} (hl : (n₂, n₃) ∈ l) :
    (n₁, n₃) ∈ collect_unitPairs (unitRule n₁ n₂) l := by
  unfold collect_unitPairs
  induction l with
  | nil => contradiction
  | cons _ _ ih =>
    simp only [List.mem_cons, List.foldr_cons] at hl ⊢
    unfold collect_unitPair
    cases hl with
    | inl hd =>
      simp [← hd]
    | inr hl =>
      split
      · simp only [Finset.mem_insert, Prod.mk.injEq, true_and]
        right
        exact ih hl
      · exact ih hl

lemma in_add_unitPairs {l : Finset (g.NT × g.NT)} {n₁ n₂ n₃ : g.NT} (hl : (n₂, n₃) ∈ l)
    (hg : ⟨n₁, [Symbol.nonterminal n₂]⟩ ∈ g.rules) :
    (n₁, n₃) ∈ add_unitPairs l := by
  unfold add_unitPairs
  have hgnn := g.rules.toList.mem_attach ⟨_, Finset.mem_toList.2 hg⟩
  revert hgnn n₂ l
  induction g.rules.toList.attach with
  | nil =>
    intro _ n₂ _ hg h
    contradiction
  | cons r t ih =>
    intro _ v2 hl hg h
    cases h
    · simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, Finset.mem_toList,
        List.flatMap_subtype, List.flatMap_singleton', List.singleton_append, List.foldr_cons,
        Finset.mem_union]
      left
      rw [← Finset.mem_toList] at hl
      exact in_collect_unitPairs hl
    · simp only [List.pure_def, List.bind_eq_flatMap, Finset.mem_toList, List.flatMap_subtype,
        List.flatMap_singleton', List.flatMap_cons, List.singleton_append, List.foldr_cons,
        Finset.mem_union] at ih ⊢
      rename_i ht
      exact Or.inr (ih hl hg ht)

lemma unitPair_in_add_unitPairs_iter {l : Finset (g.NT × g.NT)} {n₁ n₂ : g.NT}
    (hlg : l ⊆ g.generators ×ˢ g.generators) (hgl : generators_prod_diag ⊆ l) (hp : UnitPair n₁ n₂) :
    (n₁, n₂) ∈ add_unitPairs_iter l hlg := by
  induction hp with
  | refl hvg =>
    apply Finset.mem_of_subset add_unitPairs_iter_grows
    apply Finset.mem_of_subset hgl
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

/-- For a given unit pair (n₁, n₂), computes rules r : n₁ -> o, s.t. there is a rule r' : n₂ -> o
 in `g` (and `o` is non-unit) -/
noncomputable def nonUnit_rules (p : g.NT × g.NT) : List (ContextFreeRule T g.NT) :=
  let f (r : ContextFreeRule T g.NT) : Option (ContextFreeRule T g.NT) :=
    if r.input = p.2 then
      match r.output with
      | [Symbol.nonterminal _] => none
      | o => some ⟨p.1, o⟩
    else none
  g.rules.toList.filterMap f

noncomputable def remove_unitRules [DecidableEq T] (l : Finset (g.NT × g.NT)) :=
  ((l.toList).map nonUnit_rules).flatten.toFinset


/-- Given `g`, computes a new grammar g' in which all unit rules are removed and for each unit pair
 (n₁, n₂), we add rules r : n₁ -> o, if the rule r' : n₂ -> o is in the grammar (and non-unit) -/
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

lemma remove_unitRules_stuff [DecidableEq T] {l : Finset (g.NT × g.NT)} {r : ContextFreeRule T g.NT}
    (hrl : r ∈ remove_unitRules l) :
    ∃ p r', p ∈ l ∧ r' ∈ g.rules ∧ r.input = p.1 ∧ r.output = r'.output ∧ r'.input = p.2 := by
  unfold remove_unitRules at hrl
  simp only [List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists]
    at hrl
  obtain ⟨_, ⟨⟨u, v, _, rfl⟩, hruv⟩⟩ := hrl
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
        exact Produces.input_output hrin'
    · rwa [← heq2, ←hu]

-- ******************************************************************* --
-- If direction of the main correctness theorem of eliminate_unitPairs --
-- ******************************************************************* --

lemma nonUnit_rules_correct {n₁ n₂ : g.NT} {w : List (Symbol T g.NT)} (hg : ⟨n₁, w⟩ ∈ g.rules)
    (hw : NonUnit w) :
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
    {l : Finset (g.NT × g.NT)} (hug : ⟨n₂, u⟩ ∈ g.rules) (hu : NonUnit u) (hnn : (n₁, n₂) ∈ l) :
    ⟨n₁, u⟩ ∈ remove_unitRules l := by
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

lemma nonUnit_rules_nonUnit {r : ContextFreeRule T g.NT} (hrg : r ∈ g.rules)
    (hro : NonUnit r.output) :
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
  exact UnitPair.rfl (input_mem_generators hrg)

lemma implies_eliminate_unitRules {u : List (Symbol T g.NT)} {v : List T} {m : ℕ}
    (huv : g.DerivesIn u (List.map Symbol.terminal v) m) :
    g.eliminate_unitRules.Derives u (List.map Symbol.terminal v):= by
  cases m with
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
            exact input_mem_generators hp.rule
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
