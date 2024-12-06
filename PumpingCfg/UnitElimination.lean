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

-- TODO I am using this three times. Is this reason to upstream?
variable {g : ContextFreeGrammar.{uN, uT} T}

lemma Produces.rule {nt : g.NT} {u : List (Symbol T g.NT)}
    (hntu : g.Produces [Symbol.nonterminal nt] u) :
    ContextFreeRule.mk nt u ∈ g.rules := by
  obtain ⟨r, hrin, hr⟩ := hntu
  cases hr
  simp
  exact hrin
  contradiction

end Stuff

section UnitPairs

variable {g : ContextFreeGrammar.{uN, uT} T}
variable [DecidableEq g.NT]

abbrev unitRule (nt1 nt2 : g.NT) := @ContextFreeRule.mk T g.NT nt1 [Symbol.nonterminal nt2]

/-- `UnitPair nt1 nt2`, (w.r.t. a ContextFreeGrammar `g`) means that `g` can derive `nt2` from
 `nt1` only using unitRules -/
inductive UnitPair : g.NT → g.NT → Prop where
  /- UnitPair is reflexive due to the empty derivation -/
  | refl (nt : g.NT) (hmem : nt ∈ g.generators): UnitPair nt nt
  /- UnitPair is transitive -/
  | trans {nt1 nt2 nt3 : g.NT} (hmem : unitRule nt1 nt2 ∈ g.rules)
         (hp : UnitPair nt2 nt3): UnitPair nt1 nt3

@[refl]
lemma UnitPair.rfl {nt : g.NT} {hmem : nt ∈ g.generators} : UnitPair nt nt := UnitPair.refl nt hmem

lemma UnitPair.derives {nt1 nt2 : g.NT} (h : UnitPair nt1 nt2) :
  g.Derives [Symbol.nonterminal nt1] [Symbol.nonterminal nt2] := by
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

/- We use this to concisely state a rule is not a `unitRule` if it's output is NonUnit -/
abbrev NonUnit {N : Type*} (u : List (Symbol T N)) :=
  match u with
  | [Symbol.nonterminal _] => False
  | _ => True

lemma DerivesIn.unitPair_prefix {u : List T} {v : List (Symbol T g.NT)} {nt : g.NT} {n : ℕ}
    (hvu : g.DerivesIn v (List.map Symbol.terminal u) n) (hmem : nt ∈ g.generators)
    (hv : [Symbol.nonterminal nt] = v) :
    ∃ nt' w m, UnitPair nt nt' ∧ g.Produces [Symbol.nonterminal nt'] w ∧ NonUnit w ∧ m ≤ n
      ∧ g.DerivesIn w (List.map Symbol.terminal u) m := by
  induction hvu using DerivesIn.induction_refl_head generalizing nt with
  | refl =>
    cases u <;> simp at hv
  | @head n v w hvw hwu ih =>
    by_cases h' : NonUnit w
    · use nt, w, n
      constructor
      exact @UnitPair.rfl _ _ _ nt hmem
      rw [hv]
      repeat first | assumption | omega | constructor
    · unfold NonUnit at h'
      match w with
      | [Symbol.nonterminal nt'] =>
        have h' : nt' ∈ g.generators := by
          cases n with
          | zero => cases u <;> cases hwu
          | succ n =>
            obtain ⟨w', hnt'w', _⟩ := hwu.head_of_succ
            apply nonterminal_in_generators
            apply hnt'w'.rule
            rfl
        obtain ⟨v'', w', m, h1, h2, h3, h4, h5⟩ := @ih nt' h' rfl
        use v'', w', m
        constructor
        · constructor
          · unfold unitRule
            rw [←hv] at hvw
            exact hvw.rule
          · exact h1
        · repeat first | assumption | omega | constructor
      | [Symbol.terminal _] => simp at h'
      | [] => simp at h'
      | _ :: _ :: _ => simp at h'

end UnitPairs

-- *********************************************************************************************** --
-- ****************************************** Unit Pairs ***************************************** --
-- *********************************************************************************************** --

/-! Fixpoint iteration to compute all UnitPairs. -/
section ComputeUnitPairs

variable {g : ContextFreeGrammar.{uN,uT} T}
variable [DecidableEq g.NT]

noncomputable def generators_prod_diag : Finset (g.NT × g.NT) :=
  (g.rules.toList.map (fun r ↦ (r.input, r.input))).toFinset

lemma generators_prod_diag_subset : g.generators_prod_diag ⊆ g.generators ×ˢ g.generators := by
  unfold generators_prod_diag generators
  cases g.rules.toList with
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

lemma generators_prod_diag_unitPairs {p : g.NT × g.NT} (hmem : p ∈ g.generators_prod_diag) :
    UnitPair p.1 p.2  := by
  unfold generators_prod_diag at hmem
  revert hmem
  cases heq : g.rules.toList with
  | nil => tauto
  | cons hd tl =>
    simp
    intro h
    cases h with
    | inl h =>
      rw [h]
      simp
      constructor
      apply input_in_generators
      rw [←Finset.mem_toList, heq]
      exact List.mem_cons_self hd tl
    | inr h =>
      obtain ⟨v, hin, hv2⟩ := h
      rw [← hv2]
      simp
      constructor
      apply input_in_generators
      rw [←Finset.mem_toList, heq]
      exact List.mem_cons_of_mem hd hin

def collect_unitPair (input output : g.NT) (p : g.NT × g.NT) (pairs : Finset (g.NT × g.NT)) :=
  if output = p.1 then insert (input, p.2) pairs else pairs

def collect_unitPairs (r : ContextFreeRule T g.NT) (pairs : List (g.NT × g.NT)) :=
  match r.output with
  | [Symbol.nonterminal v] => pairs.foldr (collect_unitPair r.input v) {}
  | _ => {}

lemma rec_collect_unitPairs_unitPairs {input output : g.NT} {p : g.NT × g.NT}
    {pairs : List (g.NT × g.NT)} {collection : Finset (g.NT × g.NT)}
    (hmem : p ∈ pairs.foldr (collect_unitPair input output) collection) :
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

lemma collect_unitPairs_unitPair {r : ContextFreeRule T g.NT} (pairs : List (g.NT × g.NT))
    (hmem : r ∈ g.rules) (hp : ∀ p ∈ pairs, UnitPair p.1 p.2) :
    ∀ p ∈ collect_unitPairs r pairs, UnitPair p.1 p.2 := by
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
    exact hmem
    apply hp at h1
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

noncomputable def add_unitPairs (pairs : Finset (g.NT × g.NT)) : Finset (g.NT × g.NT) :=
  g.rules.toList.attach.foldr (fun r p ↦ collect_unitPairs r pairs.toList ∪ p) pairs

lemma collect_unitPairs_subset_generators_prod {r : ContextFreeRule T g.NT}
    (pairs : Finset (g.NT × g.NT)) (hsub : pairs ⊆ g.generators ×ˢ g.generators)
    (hmem : r ∈ g.rules) :
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
    · exact input_in_generators hmem
    · rw [Finset.mem_toList] at hin
      specialize hsub hin
      simp at hsub
      exact hsub.2
  | [] =>
    rw [heq] at h
    simp at h
  | [Symbol.terminal _] =>
    rw [heq] at h
    simp at h
  | x :: y :: tl =>
    rw [heq] at h
    simp at h

lemma add_unitPairs_subset_generators_prod (pairs : Finset (g.NT × g.NT))
    (hsub : pairs ⊆ g.generators ×ˢ g.generators) :
    add_unitPairs pairs ⊆ g.generators ×ˢ g.generators := by
  unfold add_unitPairs
  induction g.rules.toList.attach with
  | nil => exact hsub
  | cons hd tl ih =>
    simp at ih ⊢
    apply Finset.union_subset
    · apply collect_unitPairs_subset_generators_prod
      exact hsub
      exact Finset.mem_toList.1 hd.2
    · exact ih

lemma add_unitPairs_grows (pairs : Finset (g.NT × g.NT)) :
  pairs ⊆ (add_unitPairs pairs) := by
  unfold add_unitPairs
  induction g.rules.toList.attach with
  | nil =>
    simp
  | cons hd tl ih =>
    apply subset_trans ih
    simp

-- Proof of our termination measure shrinking
lemma generators_prod_limits_unitPairs (pairs : Finset (g.NT × g.NT))
    (hsub : pairs ⊆ g.generators ×ˢ g.generators) (hne : pairs ≠ add_unitPairs pairs) :
    (g.generators ×ˢ g.generators).card - (add_unitPairs pairs).card
      < (g.generators ×ˢ g.generators).card - pairs.card := by
   have h := HasSubset.Subset.ssubset_of_ne (add_unitPairs_grows pairs) hne
   apply Nat.sub_lt_sub_left
   · apply Nat.lt_of_lt_of_le
     · apply Finset.card_lt_card h
     · exact Finset.card_le_card (add_unitPairs_subset_generators_prod pairs hsub)
   · apply Finset.card_lt_card h

noncomputable def add_unitPairs_iter (pairs : Finset (g.NT × g.NT))
    (hsub : pairs ⊆ g.generators ×ˢ g.generators) :
    Finset (g.NT × g.NT) :=
  let pairs' := add_unitPairs pairs
  if  pairs = pairs' then
    pairs
  else
    add_unitPairs_iter pairs' (add_unitPairs_subset_generators_prod pairs hsub)
  termination_by ((g.generators ×ˢ g.generators).card - pairs.card)
  decreasing_by
    rename_i h
    exact generators_prod_limits_unitPairs pairs hsub h

-- Compute all unit pairs of a grammar
noncomputable def compute_unitPairs : Finset (g.NT × g.NT) :=
  add_unitPairs_iter g.generators_prod_diag generators_prod_diag_subset

-- ********************************************************************** --
-- Only If direction of the main correctness theorem of compute_unitPairs --
-- ********************************************************************** --

lemma add_unitPairs_unitPairs (pairs : Finset (g.NT × g.NT)) (hp : ∀ p ∈ pairs, UnitPair p.1 p.2) :
    ∀ p ∈ add_unitPairs pairs, UnitPair p.1 p.2 := by
  unfold add_unitPairs
  induction g.rules.toList.attach with
  | nil =>
    intro p
    simp
    exact hp p
  | cons hd tl ih =>
    intro p h
    simp at h
    cases h with
    | inl h =>
      apply collect_unitPairs_unitPair pairs.toList
      exact Finset.mem_toList.1 hd.2
      intro p hin'
      apply hp
      rwa[←Finset.mem_toList]
      exact h
    | inr h =>
      apply ih
      simp
      exact h

-- Main correctness result of the only if direction
lemma add_unitPair_iter_only_unitPairs (pairs : Finset (g.NT × g.NT))
    (hsub : pairs ⊆ g.generators ×ˢ g.generators) (hp : ∀ p ∈ pairs, UnitPair p.1 p.2) :
    ∀ p ∈ (add_unitPairs_iter pairs hsub), UnitPair p.1 p.2 := by
  unfold add_unitPairs_iter
  intro p
  simp
  split
  · tauto
  · apply add_unitPair_iter_only_unitPairs (add_unitPairs pairs)
          (add_unitPairs_subset_generators_prod pairs hsub)
    exact add_unitPairs_unitPairs pairs hp
  termination_by ((g.generators ×ˢ g.generators).card - pairs.card)
  decreasing_by
    rename_i h'
    exact generators_prod_limits_unitPairs pairs hsub h'

-- ***************************************************************** --
-- If direction of the main correctness theorem of compute_unitPairs --
-- ***************************************************************** --

lemma add_unitPairs_add_unitPairs_iter (pairs: Finset (g.NT × g.NT))
    (hsub : pairs ⊆ g.generators ×ˢ g.generators) :
    add_unitPairs_iter pairs hsub = add_unitPairs (add_unitPairs_iter pairs hsub) := by
  unfold add_unitPairs_iter
  simp
  split <;> rename_i h
  · exact h
  · apply add_unitPairs_add_unitPairs_iter
  termination_by ((g.generators ×ˢ g.generators).card - pairs.card)
  decreasing_by
    rename_i h'
    exact generators_prod_limits_unitPairs pairs hsub h'

lemma add_unitPairs_iter_grows {pairs : Finset (g.NT × g.NT)}
    {hsub : pairs ⊆ g.generators ×ˢ g.generators} :
    pairs ⊆ (add_unitPairs_iter pairs hsub) := by
  unfold add_unitPairs_iter
  intro p h'
  simp
  split
  · exact h'
  · apply add_unitPairs_iter_grows
    apply add_unitPairs_grows
    exact h'
  termination_by ((g.generators ×ˢ g.generators).card - pairs.card)
  decreasing_by
    rename_i h'
    exact generators_prod_limits_unitPairs pairs hsub h'

lemma in_collect_unitPairs {pairs : List (g.NT × g.NT)} {nt1 nt2 nt3 : g.NT}
    (hmem : (nt2, nt3) ∈ pairs) :
    (nt1, nt3) ∈ collect_unitPairs (unitRule nt1 nt2) pairs := by
  unfold collect_unitPairs
  simp
  induction pairs with
  | nil => contradiction
  | cons hd tl ih =>
    simp at hmem ⊢
    unfold collect_unitPair
    cases hmem with
    | inl hmem =>
      rw [← hmem]
      simp
    | inr hmem =>
      split
      · simp
        right
        exact ih hmem
      · exact ih hmem

lemma in_add_unitPairs {pairs : Finset (g.NT × g.NT)} {nt1 nt2 nt3 : g.NT}
    (hpmem : (nt2, nt3) ∈ pairs)
    (hrmem : ContextFreeRule.mk nt1 [Symbol.nonterminal nt2] ∈ g.rules) :
    (nt1, nt3) ∈ add_unitPairs pairs := by
  unfold add_unitPairs
  have h := List.mem_attach g.rules.toList ⟨_, Finset.mem_toList.2 hrmem⟩
  revert h nt2 pairs
  induction g.rules.toList.attach with
  | nil =>
    intro pairs nt2 _ hrmem h
    contradiction
  | cons r t ih =>
    intro pairs v2 hpmem hrmem h
    cases h <;> simp at ih ⊢
    · left
      rw [← Finset.mem_toList] at hpmem
      exact in_collect_unitPairs hpmem
    · rename_i h
      right
      apply ih hpmem hrmem h

lemma unitPair_in_add_unitPairs_iter {pairs : Finset (g.NT × g.NT)} {nt1 nt2 : g.NT}
    (hpsub : pairs ⊆ g.generators ×ˢ g.generators) (hgsub : generators_prod_diag ⊆ pairs)
    (hp : UnitPair nt1 nt2) :
    (nt1, nt2) ∈ add_unitPairs_iter pairs hpsub := by
  induction hp with
  | refl v hin =>
    apply Finset.mem_of_subset add_unitPairs_iter_grows
    apply Finset.mem_of_subset hgsub
    unfold generators at hin
    unfold generators_prod_diag
    rw [List.mem_toFinset, List.mem_map] at hin ⊢
    obtain ⟨r, hrin, hr⟩ := hin
    use r
    rw [hr]
    exact ⟨hrin, rfl⟩
  | @trans v1 v2 v3 hur hp ih =>
    rw [add_unitPairs_add_unitPairs_iter]
    apply in_add_unitPairs ih hur

-- Main correctness theorem of computing all unit pairs --
lemma compute_unitPairs_iff {nt1 nt2 : g.NT} :
    (nt1,nt2) ∈ compute_unitPairs ↔ UnitPair nt1 nt2 := by
  constructor
  · intro h
    change (UnitPair (nt1,nt2).1 (nt1,nt2).2)
    apply add_unitPair_iter_only_unitPairs g.generators_prod_diag generators_prod_diag_subset
    intro p hp
    exact generators_prod_diag_unitPairs hp
    exact h
  · intro h
    unfold compute_unitPairs
    apply unitPair_in_add_unitPairs_iter
    rfl
    exact h

end ComputeUnitPairs

-- *********************************************************************************************** --
-- ************************************ Unit Rule Elimination ************************************ --
-- *********************************************************************************************** --

section EliminateUnitRules

variable {g : ContextFreeGrammar T}
variable [DecidableEq g.NT]

noncomputable def nonUnit_rules (p : g.NT × g.NT) : List (ContextFreeRule T g.NT) :=
  let fltrMp (r : ContextFreeRule T g.NT) : Option (ContextFreeRule T g.NT) :=
    if r.input = p.2 then
      match r.output with
      | [Symbol.nonterminal _] => none
      | o => ContextFreeRule.mk p.1 o
    else none
  g.rules.toList.filterMap fltrMp

noncomputable def remove_unitRules [DecidableEq T] (pairs : Finset (g.NT × g.NT)) :=
  ((pairs.toList).map nonUnit_rules).flatten.toFinset


/- Given `g`, computes a new grammar g' in which all unit rules are removed and for each unit pair
 (`X`, `Y`), i.e., there is a derivation only using unit rules from `X` to `Y`, we add rules
 r : X -> W, if the rule r' : Y -> W is in the grammar (and non unit) -/
noncomputable def eliminate_unitRules [DecidableEq T] (g : ContextFreeGrammar T) [DecidableEq g.NT] :=
  ContextFreeGrammar.mk g.NT g.initial (remove_unitRules compute_unitPairs)

-- ************************************************************************ --
-- Only If direction of the main correctness theorem of eliminate_unitRules --
-- ************************************************************************ --

lemma nonUnit_rules_mem {p : g.NT × g.NT} {r : ContextFreeRule T g.NT} (hmem : r ∈ nonUnit_rules p) :
    r.input = p.1 ∧ ∃ r' ∈ g.rules, r.output = r'.output ∧ r'.input = p.2 := by
  revert hmem
  unfold nonUnit_rules
  simp
  intro r' hrin' hr'
  split <;> simp ; rename_i w u heq
  intro hr
  rw [← hr]
  simp
  use r'

lemma remove_unitRules_stuff [DecidableEq T] {pairs : Finset (g.NT × g.NT)}
    {r : ContextFreeRule T g.NT} (hmem : r ∈ remove_unitRules pairs) :
    ∃ p r', p ∈ pairs ∧ r' ∈ g.rules ∧ r.input = p.1 ∧ r.output = r'.output ∧ r'.input = p.2 := by
  unfold remove_unitRules at hmem
  simp at hmem
  obtain ⟨_, ⟨⟨u,v, hpmem, rfl⟩, hrmem⟩⟩ := hmem
  obtain ⟨h1, ⟨r', hrmem', ho, hi⟩⟩ := nonUnit_rules_mem hrmem
  use (u, v), r'

lemma eliminate_unitRules_implies [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : g.eliminate_unitRules.Derives u v) : g.Derives u v := by
  induction huv using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head v u hp _ ih =>
    obtain ⟨r, hrin, hr⟩ := hp
    unfold eliminate_unitRules at hrin
    obtain ⟨⟨p1,p2⟩, r', hpin, hrin', heq1, heq2, heq3⟩ := remove_unitRules_stuff hrin
    simp at heq1 heq3
    rw [r.rewrites_iff] at hr
    obtain ⟨p, q, hv, hu⟩ := hr
    rw [hv]
    apply Derives.trans
    · apply Derives.append_right
      apply Derives.append_left
      apply Derives.trans_produces
      rewrite [compute_unitPairs_iff] at hpin
      rewrite [heq1]
      apply hpin.derives
      rw [← heq3]
      exact rewrites_produces hrin'
    · rwa [← heq2, ←hu]

-- ******************************************************************* --
-- If direction of the main correctness theorem of eliminate_unitPairs --
-- ******************************************************************* --

lemma nonUnit_rules_correct {nt1 nt2 : g.NT} {w : List (Symbol T g.NT)}
    (hmem : {input := nt1, output := w} ∈ g.rules) (hw : NonUnit w) :
    {input := nt2, output := w} ∈ nonUnit_rules (nt2, nt1) := by
  unfold nonUnit_rules
  simp
  use ContextFreeRule.mk nt1 w
  simp
  constructor
  exact hmem
  unfold NonUnit at hw
  match h' : w with
  | [Symbol.nonterminal v] => simp at hw
  | [Symbol.terminal _] => rfl
  | [] => rfl
  | _ :: _ :: _ => simp

lemma remove_unitRules_correct [DecidableEq T] {nt1 nt2 : g.NT} {u : List (Symbol T g.NT)}
    {pairs : Finset (g.NT × g.NT)} (hrmem : {input := nt2, output := u} ∈ g.rules) (hw : NonUnit u)
    (hpmem : (nt1, nt2) ∈ pairs) :
    {input := nt1, output := u} ∈ remove_unitRules pairs := by
  unfold remove_unitRules
  simp
  use nonUnit_rules (nt1, nt2)
  constructor
  · use nt1, nt2
  · exact nonUnit_rules_correct hrmem hw

lemma eliminate_unitRules_produces [DecidableEq T] {nt1 nt2 : g.NT} {u : List (Symbol T g.NT)}
    (hp : UnitPair nt1 nt2) (hntu : g.Produces [Symbol.nonterminal nt2] u)
    (hu : NonUnit u) : g.eliminate_unitRules.Produces [Symbol.nonterminal nt1] u := by
  unfold eliminate_unitRules Produces
  simp
  constructor
  constructor
  exact remove_unitRules_correct hntu.rule hu ((compute_unitPairs_iff).2 hp)
  nth_rewrite 2 [← u.append_nil]
  constructor

lemma nonUnit_rules_nonUnit {r : ContextFreeRule T g.NT} (hmem : r ∈ g.rules)
    (hn : NonUnit r.output) :
    r ∈ nonUnit_rules (r.input, r.input) := by
  unfold nonUnit_rules
  simp
  use r
  constructor
  exact hmem
  simp
  unfold NonUnit at hn
  match h : r.output with
  | [Symbol.nonterminal v] => rw [h] at hn; simp at hn
  | [Symbol.terminal _] => simp; rw [← h]
  | [] => simp; rw [← h]
  | _ :: _ :: _ => simp; rw [← h]

lemma nonUnit_in_eliminate_unitRules [DecidableEq T] {r : ContextFreeRule T g.NT} (hmem : r ∈ g.rules)
    (hn : NonUnit r.output) :
    (r ∈ g.eliminate_unitRules.rules) := by
  unfold eliminate_unitRules
  simp
  unfold remove_unitRules
  simp
  use (nonUnit_rules (r.input, r.input))
  constructor
  · use r.input, r.input
    constructor
    · rw [compute_unitPairs_iff]
      apply UnitPair.rfl
      exact nonterminal_in_generators hmem rfl
    · rfl
  · exact nonUnit_rules_nonUnit hmem hn

lemma implies_eliminate_unitRules [DecidableEq T] {u : List (Symbol T g.NT)} {v : List T} {n : ℕ}
    (huv : g.DerivesIn u (List.map Symbol.terminal v) n) :
    g.eliminate_unitRules.Derives u (List.map Symbol.terminal v):= by
  cases n with
  | zero =>
    cases huv
    rfl
  | succ n =>
    obtain ⟨u, hp, hd⟩ := huv.head_of_succ
    obtain ⟨r, hrin, hr⟩ := hp
    obtain ⟨p,q, hw, hu⟩ := hr.exists_parts
    by_cases h' : NonUnit r.output
    · apply Produces.trans_derives
      use r
      exact ⟨nonUnit_in_eliminate_unitRules hrin h', hr⟩
      exact implies_eliminate_unitRules hd
    · unfold NonUnit at h'
      match h : r.output with
      | [Symbol.nonterminal v] =>
        rw [h] at hu
        rw [hu] at hd
        obtain ⟨s1', s2', s3', m1, m2, m3, hs, hd1, hd2, hd3, hn⟩ := hd.three_split
        obtain ⟨s', s3, hs', hs'', hs3⟩ := List.map_eq_append_iff.1 hs
        obtain ⟨s1, s2, hs''', hs1, hs2⟩ := List.map_eq_append_iff.1 hs''
        rw [← hs1] at hd1
        rw [← hs2] at hd2
        rw [← hs3] at hd3
        rw [hs, hw, ←hs1, ←hs2, ←hs3]
        apply Derives.append_left_trans
        apply implies_eliminate_unitRules hd3
        apply Derives.append_left_trans
        have h' : v ∈ g.generators := by
          cases m2 with
          | zero => cases s2 <;> cases hd2
          | succ n =>
            obtain ⟨w', hp, _⟩ := hd2.head_of_succ
            apply nonterminal_in_generators
            apply hp.rule
            rfl
        obtain ⟨u, w', m2', hvu, hp, hw', _, hd2'⟩ := hd2.unitPair_prefix h' rfl
        apply Produces.trans_derives
        · apply eliminate_unitRules_produces _ hp hw'
          apply UnitPair.trans
          unfold unitRule
          rwa [← h]
          exact hvu
        · exact implies_eliminate_unitRules hd2'
        exact implies_eliminate_unitRules hd1
      | [Symbol.terminal _] => rw [h] at h'; simp at h'
      | [] => rw [h] at h'; simp at h'
      | _ :: _ :: _ => rw [h] at h'; simp at h'

-- Main correctness theorem of eliminate_unitRules
theorem eliminate_unitRules_correct [DecidableEq T] :
    g.language = g.eliminate_unitRules.language := by
  unfold language Generates
  have h' : g.eliminate_unitRules.initial = g.initial := by unfold eliminate_unitRules; rfl
  apply Set.eq_of_subset_of_subset
  · intro w h
    simp at h ⊢
    have h' : g.eliminate_unitRules.initial = g.initial := by unfold eliminate_unitRules; rfl
    rw [h']
    obtain ⟨n, h⟩ := (derives_iff_derivesIn _ _ _).1 h
    exact implies_eliminate_unitRules h
  · intro w h
    simp at h ⊢
    rw [←h']
    exact eliminate_unitRules_implies h

end EliminateUnitRules

end ContextFreeGrammar
