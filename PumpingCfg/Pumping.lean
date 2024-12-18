/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/

import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.ChomskyNormalForm.Basic
import Mathlib.Computability.ChomskyNormalForm.Translation
import PumpingCfg.Utils
import PumpingCfg.ParseTree
import Mathlib.Data.Set.Card

universe uT uN

variable {T : Type uT}

namespace ChomskyNormalFormGrammar

noncomputable def generators (g : ChomskyNormalFormGrammar.{uN, uT} T) [DecidableEq g.NT] :
    Finset g.NT :=
  (g.rules.toList.map ChomskyNormalFormRule.input).toFinset

variable {g : ChomskyNormalFormGrammar.{uN, uT} T}

lemma pumping_string {u v : List (Symbol T g.NT)} {n : g.NT}
    (h : g.Derives [Symbol.nonterminal n] (u ++ [Symbol.nonterminal n] ++ v)) (i : ℕ):
    g.Derives [Symbol.nonterminal n] (u^+^i ++ [Symbol.nonterminal n] ++ v^+^i) := by
  induction i with
  | zero =>
    simpa using Derives.refl [Symbol.nonterminal n]
  | succ n ih =>
    apply Derives.trans ih
    apply Derives.trans
    apply Derives.append_right
    apply Derives.append_left
    exact h
    repeat rw [List.append_assoc]
    rw [← nTimes_succ_l]
    repeat rw [← List.append_assoc]
    rw [← nTimes_succ_r]

lemma subtree_height_le {n₁ n₂ : g.NT} {p₁ : parseTree n₁} {p₂ : parseTree n₂} (hpp : p₂.IsSubtreeOf p₁) :
    p₂.height ≤ p₁.height := by
  induction hpp with
  | leaf_refl hrn => rfl
  | node_refl p₁ p₂ hrn => rfl
  | left_sub p₁ p₂ p hrn₁ hpp₁ ih => exact Nat.le_add_right_of_le (le_sup_of_le_left ih)
  | right_sub p₁ p₂ p hrn₁ hpp₂ ih => exact Nat.le_add_right_of_le (le_sup_of_le_right ih)

variable [DecidableEq g.NT] [DecidableEq (Σ _n : g.NT, parseTree _n)]
/-
lemma subtree_repeat_root_height_ind {n : g.NT} {p : parseTree n}
    (s : Set (Σ _n : g.generators, parseTree _n.val)) (hs : ∀ e₁ ∈ s, ∀ e₂ ∈ s, e₁.fst = e₂.fst → e₁ = e₂)
    (hp : g.generators.card.succ ≤ p.height + s.ncard) (hps : ∀ pₛ ∈ s, p.IsSubtreeOf pₛ.snd) :
    (∃ n' : g.NT, ∃ p' p'' : parseTree n',
      p'.IsSubtreeOf p ∧ p''.IsSubtreeOf p' ∧ p' ≠ p'') ∨
    (∃ t : parseTree n, ⟨⟨n, by sorry⟩, t⟩ ∈ s ∧ p.IsSubtreeOf t) := by
  induction p generalizing s with
  | @tree_leaf n t hnt =>
    simp [parseTree.height] at hp
    rw [add_comm] at hp
    rw [Nat.add_le_add_iff_left] at hp
    -- TODO pidgeonhole applied to `hp` with `p` somehow gives that `hs` implies that `⟨n, _⟩ ∈ s`
    sorry
  | @tree_node n₀ c₁ c₂ t₁ t₂ hnc ih₁ ih₂ =>
    if hh : ∃ t₀ : parseTree n₀, ⟨⟨n₀, by sorry⟩, t₀⟩ ∈ s then
      right
      obtain ⟨t₀, ht₀⟩ := hh
      exact ⟨t₀, ht₀, hps _ ht₀⟩
    else
      left
      have hcard : (s ∪ {⟨⟨n₀, by sorry⟩, .tree_node t₁ t₂ hnc⟩}).ncard = 1 + s.ncard := sorry
      specialize ih₁ (s ∪ {⟨⟨n₀, by sorry⟩, .tree_node t₁ t₂ hnc⟩})
      specialize ih₂ (s ∪ {⟨⟨n₀, by sorry⟩, .tree_node t₁ t₂ hnc⟩})
      simp only [parseTree.height] at hp
      rw [add_assoc, ←hcard, max_add, le_max_iff] at hp
      cases hp with
      | inl hcard₁ =>
        specialize ih₁ (by sorry) hcard₁
        sorry
      | inr hcard₂ =>
        specialize ih₂ (by sorry) hcard₂
        sorry

lemma subtree_repeat_root_height_aux_aux_aux {n : g.NT} {p : parseTree n}
    (hp : g.generators.card.succ = p.height) :
    ∃ n' : g.NT, ∃ p' p'' : parseTree n',
      p'.IsSubtreeOf p ∧ p''.IsSubtreeOf p' ∧ p' ≠ p'' := by
  cases subtree_repeat_root_height_ind ∅ (by simp) (le_of_eq (by simpa using hp)) (by simp) with
  | inl h => exact h
  | inr h => simp at h
-/

lemma subtree_repeat_root_height_ind {n : g.NT} {p : parseTree n}
    (s : Finset (Σ _n : g.NT, parseTree _n)) (hs : ∀ e₁ ∈ s, ∀ e₂ ∈ s, e₁.fst = e₂.fst → e₁ = e₂)
    (hp : g.generators.card.succ ≤ p.height + s.card) (hps : ∀ pₛ ∈ s, p.IsSubtreeOf pₛ.snd) :
    (∃ n' : g.NT, ∃ p' p'' : parseTree n',
      p'.IsSubtreeOf p ∧ p''.IsSubtreeOf p' ∧ p' ≠ p'') ∨
    (∃ n₀, ∃ t t' : parseTree n₀, ⟨n₀, t⟩ ∈ s ∧ t'.IsSubtreeOf p) := by
  induction p generalizing s with
  | @tree_leaf n t hnt =>
    simp [parseTree.height] at hp
    rw [add_comm] at hp
    rw [Nat.add_le_add_iff_left] at hp
    -- TODO pidgeonhole applied to `hp` with `p` somehow gives that `hs` implies that `⟨n, _⟩ ∈ s`
    sorry
  | @tree_node n₀ c₁ c₂ t₁ t₂ hnc ih₁ ih₂ =>
    if hh : ∃ t₀ : parseTree n₀, ⟨n₀, t₀⟩ ∈ s then
      right
      obtain ⟨t₀, ht₀⟩ := hh
      refine ⟨_, t₀, .tree_node t₁ t₂ hnc, ht₀, parseTree.IsSubtreeOf.node_refl t₁ t₂ hnc⟩
    else
      have hcard : (insert ⟨n₀, .tree_node t₁ t₂ hnc⟩ s).card = 1 + s.card := by
        have : ⟨n₀, .tree_node t₁ t₂ hnc⟩ ∉ s := by
          intro cont
          apply hh
          exact ⟨_, cont⟩
        rw [add_comm]
        exact Finset.card_insert_of_not_mem this
      specialize ih₁ (insert ⟨n₀, .tree_node t₁ t₂ hnc⟩ s)
      specialize ih₂ (insert ⟨n₀, .tree_node t₁ t₂ hnc⟩ s)
      simp only [parseTree.height] at hp
      rw [add_assoc, ←hcard, max_add, le_max_iff] at hp
      have hmem : ∀ e₁ ∈ insert ⟨n₀, t₁.tree_node t₂ hnc⟩ s,
                    ∀ e₂ ∈ insert ⟨n₀, t₁.tree_node t₂ hnc⟩ s,
                      e₁.fst = e₂.fst → e₁ = e₂ := by
        intros e₁ he₁ e₂ he₂ hee
        simp at he₁ he₂
        cases he₁ with
        | inl he₁ =>
          cases he₂ with
          | inl he₂ =>
            rw [he₁, he₂]
          | inr he₂ =>
            exfalso
            apply hh
            rw [he₁] at hee
            simp at hee
            rw [hee]
            use e₂.snd
        | inr he₁ =>
          cases he₂ with
          | inl he₂ =>
            exfalso
            apply hh
            rw [he₂] at hee
            simp at hee
            rw [←hee]
            use e₁.snd
          | inr he₂ =>
            exact hs _ he₁ _ he₂ hee
      cases hp with
      | inl hcard₁ =>
        have h₂ : ∀ e ∈ insert ⟨n₀, t₁.tree_node t₂ hnc⟩ s, t₁.IsSubtreeOf e.snd := by
          intros e he
          simp at he
          cases he with
          | inl he =>
            rw [he]
            constructor
            rfl
          | inr he =>
            apply parseTree.IsSubtreeOf.trans;swap
            exact hps _ he
            constructor
            rfl
        cases ih₁ hmem hcard₁ h₂ with
        | inl h =>
          left
          obtain ⟨n', p', p'', hp', hp'', hp⟩ := h
          exact ⟨n', p', p'', parseTree.IsSubtreeOf.left_sub t₁ t₂ p' hnc hp', hp'', hp⟩
        | inr h =>
          obtain ⟨n₀, t, t', ht, ht'⟩ := h
          simp at ht
          cases ht with
          | inr h =>
            right
            use n₀, t, t', h
            exact parseTree.IsSubtreeOf.left_sub t₁ t₂ t' hnc ht'
          | inl h =>
            simp at h
            obtain ⟨hn₀, ht⟩ := h
            left
            use n₀, t₁.tree_node t₂ (hn₀ ▸ hnc), t'
            constructor
            · subst hn₀
              exact parseTree.IsSubtreeOf.node_refl t₁ t₂ (Eq.symm (Eq.refl n₀) ▸ hnc)
            constructor
            · apply parseTree.IsSubtreeOf.left_sub
              exact ht'
            · intro ht
              obtain h := parseTree.subtree_height ht'
              rw [← ht] at h
              simp [parseTree.height] at h
              omega
      | inr hcard₂ =>
        -- This entire branch is the same as `inl hcard₁` :/
        have h₂ : ∀ e ∈ insert ⟨n₀, t₁.tree_node t₂ hnc⟩ s, t₂.IsSubtreeOf e.snd := by
          intros e he
          simp at he
          cases he with
          | inl he =>
            rw [he]
            apply parseTree.IsSubtreeOf.right_sub
            rfl
          | inr he =>
            apply parseTree.IsSubtreeOf.trans;swap
            exact hps _ he
            apply parseTree.IsSubtreeOf.right_sub
            rfl
        cases ih₂ hmem hcard₂ h₂ with
        | inl h =>
          left
          obtain ⟨n', p', p'', hp', hp'', hp⟩ := h
          exact ⟨n', p', p'', parseTree.IsSubtreeOf.right_sub t₁ t₂ p' hnc hp', hp'', hp⟩
        | inr h =>
          obtain ⟨n₀, t, t', ht, ht'⟩ := h
          simp at ht
          cases ht with
          | inr h =>
            right
            use n₀, t, t', h
            exact parseTree.IsSubtreeOf.right_sub t₁ t₂ t' hnc ht'
          | inl h =>
            simp at h
            obtain ⟨hn₀, ht⟩ := h
            left
            use n₀, t₁.tree_node t₂ (hn₀ ▸ hnc), t'
            constructor
            · subst hn₀
              exact parseTree.IsSubtreeOf.node_refl t₁ t₂ (Eq.symm (Eq.refl n₀) ▸ hnc)
            constructor
            · apply parseTree.IsSubtreeOf.right_sub
              exact ht'
            · intro ht
              obtain h := parseTree.subtree_height ht'
              rw [← ht] at h
              simp [parseTree.height] at h
              omega

lemma subtree_repeat_root_height_aux_aux_aux {n : g.NT} {p : parseTree n}
    (hp : g.generators.card.succ = p.height) :
    ∃ n' : g.NT, ∃ p' p'' : parseTree n',
      p'.IsSubtreeOf p ∧ p''.IsSubtreeOf p' ∧ p' ≠ p'' := by
  cases subtree_repeat_root_height_ind ∅ (by simp) (le_of_eq (by simpa using hp)) (by simp) with
  | inl h => exact h
  | inr h => simp at h

lemma subtree_repeat_root_height_aux_aux {n : g.NT} {p : parseTree n}
    (hgp : g.generators.card.succ = p.height) :
    ∃ n' : g.NT, ∃ p' p'' : parseTree n',
      p'.IsSubtreeOf p ∧ p''.IsSubtreeOf p' ∧ p'.height ≤ g.generators.card.succ ∧ p' ≠ p'' := by
  obtain ⟨n', p', p'', hp', hp'', hp⟩ := subtree_repeat_root_height_aux_aux_aux hgp
  exact ⟨n', p', p'', hp', hp'', hgp ▸ subtree_height_le hp', hp⟩

lemma subtree_repeat_root_height_aux {n : g.NT} {p : parseTree n}
    (hgp : g.generators.card.succ ≤ p.height) :
    ∃ n' : g.NT, ∃ p' p'' : parseTree n',
      p'.IsSubtreeOf p ∧ p''.IsSubtreeOf p' ∧ p'.height ≤ g.generators.card.succ ∧ p' ≠ p'' := by
  induction p with
  | @tree_leaf n t =>
    exfalso
    have hn : n ∈ g.generators := by
      simp [generators]
      use ChomskyNormalFormRule.leaf n t
    simp [parseTree.height] at hgp
    rw [hgp] at hn
    simp at hn
  | tree_node t₁ t₂ hnc ih₁ ih₂ =>
    rw [Nat.le_iff_lt_or_eq] at hgp
    cases hgp with
    | inr hp => exact subtree_repeat_root_height_aux_aux hp
    | inl hp =>
      simp [parseTree.height] at hp
      cases hp with
      | inl hp₁ =>
        obtain ⟨n', p', p'', hp', hp'', hpg, hpp⟩ := ih₁ hp₁
        exact ⟨n', p', p'', parseTree.IsSubtreeOf.left_sub t₁ t₂ p' hnc hp', hp'', hpg, hpp⟩
      | inr hp₂ =>
        obtain ⟨n', p', p'', hp', hp'', hpg, hpp⟩ := ih₂ hp₂
        exact ⟨n', p', p'', parseTree.IsSubtreeOf.right_sub t₁ t₂ p' hnc hp', hp'', hpg, hpp⟩

lemma subtree_repeat_root_height {n : g.NT} {p : parseTree n}
    (hp : p.yield.length ≥ 2 ^ g.generators.card) :
    ∃ n' : g.NT, ∃ p' p'' : parseTree n',
      p'.IsSubtreeOf p ∧ p''.IsSubtreeOf p' ∧ p'.height ≤ g.generators.card.succ ∧ p' ≠ p'' := by
  apply subtree_repeat_root_height_aux
  have hp1 := p.height_pos
  have hp2 := hp.trans p.yield_length_le_two_pow_height
  rw [Nat.pow_le_pow_iff_right] at hp2 <;> omega

lemma cnf_pumping {w : List T} (hwg : w ∈ g.language) (hw : w.length ≥ 2 ^ g.generators.card) :
    ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      (v ++ y).length > 0       ∧
      (v ++ x ++ y).length ≤ 2 ^ g.generators.card  ∧
      ∀ i : ℕ, u ++ v^+^i ++ x ++ y^+^i ++ z ∈ g.language := by
  obtain ⟨p, rfl⟩ := hwg.yield
  obtain ⟨n, p₁, p₂, hp₁, hp₂, hpg, hpp⟩ := subtree_repeat_root_height hw
  obtain ⟨v, y, hpvy, hvy, hgpvy⟩ := parseTree.strict_subtree_decomposition hp₂ hpp
  obtain ⟨u, z, hpuz, hgpuz⟩ := parseTree.subtree_decomposition hp₁
  refine ⟨u, v, p₂.yield, y, z, ?_, hvy, ?_, ?_⟩
  · simp_rw [hpuz, hpvy, List.append_assoc]
  · rw [← hpvy]
    apply le_trans p₁.yield_length_le_two_pow_height
    apply Nat.pow_le_pow_of_le_right <;> omega
  · intro k
    apply Derives.trans hgpuz
    · repeat rw [List.map_append]
      apply Derives.append_right
      repeat rw [List.append_assoc]
      apply Derives.append_left
      have hpump := pumping_string hgpvy k
      apply Derives.trans
      exact hpump
      apply Derives.trans
      apply Derives.append_right
      apply Derives.append_left
      apply p₂.yield_derives
      repeat rw [List.append_assoc]
      simpa [nTimes] using Derives.refl _

end ChomskyNormalFormGrammar

theorem pumping_lemma {L : Language T} (hL : L.IsContextFree) :
    ∃ p : ℕ, ∀ w ∈ L, w.length ≥ p → ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      (v ++ y).length > 0       ∧
      (v ++ x ++ y).length ≤ p  ∧
      ∀ i : ℕ, u ++ v^+^i ++ x ++ y^+^i ++ z ∈ L := by
  obtain ⟨g, rfl⟩ := hL
  classical
  use 2 ^ g.toCNF.generators.card
  intro w hwL hwg
  by_cases hw : w = []
  · simp [hw] at hwg
  · have h : w ∈ g.language \ {[]} := ⟨hwL, hw⟩
    rw [ContextFreeGrammar.toCNF_correct] at h
    obtain ⟨u, v, x, y, z, hw, hvy, hvxy, hL⟩ := ChomskyNormalFormGrammar.cnf_pumping h hwg
    refine ⟨u, v, x, y, z, hw, hvy, hvxy, ?_⟩
    intro i
    apply Set.diff_subset
    rw [ContextFreeGrammar.toCNF_correct]
    exact hL i
