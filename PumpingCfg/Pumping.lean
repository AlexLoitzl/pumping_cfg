/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/

import Mathlib.Computability.ChomskyNormalForm.Translation
import PumpingCfg.Utils
import PumpingCfg.ParseTree
import Mathlib.Data.Set.Card

theorem pidgeonhole {α β : Type*} {A : Finset α} {B : Finset β} {f : A → B} (hf : f.Injective) : A.card ≤ B.card := by
  if emptiness : A = ∅ then
    simp_all
  else
    obtain ⟨a₀, ha₀⟩ := Finset.nonempty_iff_ne_empty.mpr emptiness
    clear emptiness
    classical
    let f' : α → β := fun a => f (if ha : a ∈ A then ⟨a, ha⟩ else ⟨a₀, ha₀⟩)
    apply Finset.card_le_card_of_injOn f'
    · aesop
    · intro a₁ ha₁ a₂ ha₂ haa
      have haa' : f ⟨a₁, ha₁⟩ = f ⟨a₂, ha₂⟩ := by
        rw [Finset.mem_coe] at ha₁ ha₂
        simp only [f', ha₁, ha₂] at haa
        exact Subtype.eq haa
      simpa using hf haa'

universe uT uN

variable {T : Type uT}

namespace ChomskyNormalFormGrammar

noncomputable def generators (g : ChomskyNormalFormGrammar.{uN, uT} T) [DecidableEq g.NT] :
    Finset g.NT :=
  (g.rules.toList.map ChomskyNormalFormRule.input).toFinset

variable {g : ChomskyNormalFormGrammar.{uN, uT} T}

lemma pumping_string {u v : List (Symbol T g.NT)} {n : g.NT}
    (hg : g.Derives [Symbol.nonterminal n] (u ++ [Symbol.nonterminal n] ++ v)) (i : ℕ):
    g.Derives [Symbol.nonterminal n] (u^+^i ++ [Symbol.nonterminal n] ++ v^+^i) := by
  induction i with
  | zero =>
    simpa using Derives.refl [Symbol.nonterminal n]
  | succ n ih =>
    apply ih.trans
    apply ((hg.append_left _).append_right _).trans
    rw [List.append_assoc, List.append_assoc, ← nTimes_succ_l, ← List.append_assoc, ← List.append_assoc, ← nTimes_succ_r]

lemma subtree_height_le {n₁ n₂ : g.NT} {p₁ : parseTree n₁} {p₂ : parseTree n₂} (hpp : p₂.IsSubtreeOf p₁) :
    p₂.height ≤ p₁.height := by
  induction hpp with
  | leaf_refl hrn => rfl
  | node_refl p₁ p₂ hrn => rfl
  | left_sub _ _ _ _ _ ih => exact Nat.le_add_right_of_le (le_sup_of_le_left ih)
  | right_sub _ _ _ _ _ ih => exact Nat.le_add_right_of_le (le_sup_of_le_right ih)

variable [DecidableEq g.NT]

lemma input_mem_generators {r : ChomskyNormalFormRule T g.NT} (hrg : r ∈ g.rules) :
    r.input ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at hrg
  revert hrg
  induction g.rules.toList with
  | nil => simp
  | cons _ _ ih => aesop

variable [DecidableEq (Σ _n : g.NT, parseTree _n)]

lemma subtree_repeat_root_height_ind {n : g.NT} {p : parseTree n}
    (s : Finset (Σ _n : g.NT, parseTree _n)) (hs : ∀ e₁ ∈ s, ∀ e₂ ∈ s, e₁.fst = e₂.fst → e₁ = e₂)
    (hp : g.generators.card.succ ≤ p.height + s.card) (hps : ∀ pₛ ∈ s, p.IsSubtreeOf pₛ.snd) :
    (∃ n' : g.NT, ∃ p' p'' : parseTree n',
      p'.IsSubtreeOf p ∧ p''.IsSubtreeOf p' ∧ p' ≠ p'') ∨
    (∃ n₀, ∃ t t' : parseTree n₀, ⟨n₀, t⟩ ∈ s ∧ t'.IsSubtreeOf p) := by
  induction p generalizing s with
  | @leaf n t hnt =>
    rw [Nat.succ_eq_add_one, parseTree.height, add_comm, Nat.add_le_add_iff_left] at hp
    by_contra! was_goal
    have pidgeon : ¬(∃ f : { q // q ∈ (insert ⟨n, parseTree.leaf t hnt⟩ s) } → g.generators, f.Injective) := by
      push_neg
      intro f hf
      have := pidgeonhole hf
      have : (insert ⟨n, parseTree.leaf t hnt⟩ s).card = s.card + 1 :=
        Finset.card_insert_of_not_mem (was_goal.right n (.leaf t hnt) (.leaf t hnt) · (parseTree.IsSubtreeOf.leaf_refl hnt))
      omega
    apply pidgeon
    use fun z =>
      ⟨z.val.fst, by
        cases z.val.snd with
        | leaf _ hnt =>
          exact input_mem_generators hnt
        | node t₁ t₂ hnc =>
          exact input_mem_generators hnc
      ⟩
    intro x y hxy
    have hx := x.property
    have hy := y.property
    rw [Finset.mem_insert] at hx hy
    cases hx with
    | inl hxt =>
      simp only [hxt, Subtype.mk.injEq] at hxy
      cases hy with
      | inl hyt =>
        apply Subtype.eq
        rw [hxt, hyt]
      | inr hys =>
        exfalso
        exact was_goal.right n (hxy ▸ y.val.snd) (parseTree.leaf t hnt) (by convert hys; aesop)
          (parseTree.IsSubtreeOf.leaf_refl hnt)
    | inr hxs =>
      cases hy with
      | inl hyt =>
        simp only [hyt, Subtype.mk.injEq] at hxy
        exfalso
        exact was_goal.right n (hxy ▸ x.val.snd) (parseTree.leaf t hnt) (by convert hxs <;> aesop)
          (parseTree.IsSubtreeOf.leaf_refl hnt)
      | inr hys =>
        exact Subtype.eq (hs x hxs y hys (by simp_all))
  | @node n₀ _ _ t₁ t₂ hnc ih₁ ih₂ =>
    if hn₀ : ∃ t₀ : parseTree n₀, ⟨n₀, t₀⟩ ∈ s then
      right
      obtain ⟨t₀, ht₀⟩ := hn₀
      refine ⟨_, t₀, parseTree.node t₁ t₂ hnc, ht₀, parseTree.IsSubtreeOf.node_refl t₁ t₂ hnc⟩
    else
      have hcard : (insert ⟨n₀, parseTree.node t₁ t₂ hnc⟩ s).card = 1 + s.card := by
        rw [add_comm]
        exact Finset.card_insert_of_not_mem (hn₀ ⟨_, ·⟩)
      specialize ih₁ (insert ⟨n₀, parseTree.node t₁ t₂ hnc⟩ s)
      specialize ih₂ (insert ⟨n₀, parseTree.node t₁ t₂ hnc⟩ s)
      simp only [parseTree.height] at hp
      rw [add_assoc, ←hcard, max_add, le_max_iff] at hp
      have hes :
        ∀ e₁ ∈ insert ⟨n₀, t₁.node t₂ hnc⟩ s,
        ∀ e₂ ∈ insert ⟨n₀, t₁.node t₂ hnc⟩ s,
          e₁.fst = e₂.fst → e₁ = e₂ := by
        intro e₁ he₁ e₂ he₂ hee
        rw [Finset.mem_insert] at he₁ he₂
        cases he₁ with
        | inl he₁ =>
          cases he₂ with
          | inl he₂ =>
            rw [he₁, he₂]
          | inr he₂ =>
            exfalso
            apply hn₀
            rw [he₁] at hee
            dsimp only at hee
            rw [hee]
            use e₂.snd
        | inr he₁ =>
          cases he₂ with
          | inl he₂ =>
            exfalso
            apply hn₀
            rw [he₂] at hee
            dsimp only at hee
            rw [←hee]
            use e₁.snd
          | inr he₂ =>
            exact hs _ he₁ _ he₂ hee
      cases hp with
      | inl hcard₁ =>
        have hst₁ : ∀ e ∈ insert ⟨n₀, t₁.node t₂ hnc⟩ s, t₁.IsSubtreeOf e.snd := by
          intro e he
          rw [Finset.mem_insert] at he
          cases he with
          | inl he => exact he ▸ parseTree.IsSubtreeOf.left_sub t₁ t₂ t₁ hnc parseTree.IsSubtreeOf.refl
          | inr he => exact (parseTree.IsSubtreeOf.left_sub t₁ t₂ t₁ hnc parseTree.IsSubtreeOf.refl).trans (hps _ he)
        cases ih₁ hes hcard₁ hst₁ with
        | inl hp =>
          left
          obtain ⟨n', p', p'', hp', hp'', hp⟩ := hp
          exact ⟨n', p', p'', parseTree.IsSubtreeOf.left_sub t₁ t₂ p' hnc hp', hp'', hp⟩
        | inr ht =>
          obtain ⟨n₀, t, t', ht, ht'⟩ := ht
          rw [Finset.mem_insert] at ht
          cases ht with
          | inr hts =>
            right
            exact ⟨n₀, t, t', hts, parseTree.IsSubtreeOf.left_sub t₁ t₂ t' hnc ht'⟩
          | inl httt =>
            rw [Sigma.mk.inj_iff] at httt
            obtain ⟨hn₀, ht⟩ := httt
            left
            use n₀, t₁.node t₂ (hn₀ ▸ hnc), t', hn₀ ▸ parseTree.IsSubtreeOf.node_refl t₁ t₂ hnc, parseTree.IsSubtreeOf.left_sub _ _ _ _ ht'
            intro ht
            obtain htt' := parseTree.subtree_height ht'
            rw [← ht] at htt'
            simp only [parseTree.height] at htt'
            omega
      | inr hcard₂ =>
        -- This entire branch is the same as `inl hcard₁` except for `left_sub`/`right_sub` and `t₁`/`t₂` :/
        have hst₂ : ∀ e ∈ insert ⟨n₀, t₁.node t₂ hnc⟩ s, t₂.IsSubtreeOf e.snd := by
          intro e he
          rw [Finset.mem_insert] at he
          cases he with
          | inl he => exact he ▸ parseTree.IsSubtreeOf.right_sub t₁ t₂ t₂ hnc parseTree.IsSubtreeOf.refl
          | inr he => exact (parseTree.IsSubtreeOf.right_sub t₁ t₂ t₂ hnc parseTree.IsSubtreeOf.refl).trans (hps _ he)
        cases ih₂ hes hcard₂ hst₂ with
        | inl hp =>
          left
          obtain ⟨n', p', p'', hp', hp'', hp⟩ := hp
          exact ⟨n', p', p'', parseTree.IsSubtreeOf.right_sub t₁ t₂ p' hnc hp', hp'', hp⟩
        | inr ht =>
          obtain ⟨n₀, t, t', ht, ht'⟩ := ht
          rw [Finset.mem_insert] at ht
          cases ht with
          | inr hts =>
            right
            exact ⟨n₀, t, t', hts, parseTree.IsSubtreeOf.right_sub t₁ t₂ t' hnc ht'⟩
          | inl httt =>
            rw [Sigma.mk.inj_iff] at httt
            obtain ⟨hn₀, ht⟩ := httt
            left
            use n₀, t₁.node t₂ (hn₀ ▸ hnc), t', hn₀ ▸ parseTree.IsSubtreeOf.node_refl t₁ t₂ hnc, parseTree.IsSubtreeOf.right_sub _ _ _ _ ht'
            intro ht
            obtain htt' := parseTree.subtree_height ht'
            rw [← ht] at htt'
            simp only [parseTree.height] at htt'
            omega

lemma subtree_repeat_root_height_aux_aux_aux {n : g.NT} {p : parseTree n}
    (hp : g.generators.card.succ = p.height) :
    ∃ n' : g.NT, ∃ p' p'' : parseTree n',
      p'.IsSubtreeOf p ∧ p''.IsSubtreeOf p' ∧ p' ≠ p'' := by
  cases subtree_repeat_root_height_ind ∅ (by simp) (le_of_eq (by simpa using hp)) (by simp) with
  | inl hp' => exact hp'
  | inr hp' => simp at hp'

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
  | @leaf n t =>
    exfalso
    have hn : n ∈ g.generators := by
      simp [generators]
      use ChomskyNormalFormRule.leaf n t
    simp [parseTree.height] at hgp
    rw [hgp] at hn
    simp at hn
  | node t₁ t₂ hnc ih₁ ih₂ =>
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

lemma pumping {w : List T} (hwg : w ∈ g.language) (hw : w.length ≥ 2 ^ g.generators.card) :
    ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      (v ++ y).length > 0       ∧
      (v ++ x ++ y).length ≤ 2 ^ g.generators.card  ∧
      ∀ i : ℕ, u ++ v^+^i ++ x ++ y^+^i ++ z ∈ g.language := by
  obtain ⟨p, rfl⟩ := hwg.yield
  obtain ⟨n, p₁, p₂, hp₁, hp₂, hpg, hpp⟩ := subtree_repeat_root_height hw
  obtain ⟨v, y, hpvy, hvy, hgpvy⟩ := parseTree.strict_subtree_decomposition hp₂ hpp
  obtain ⟨u, z, hpuz, hguz⟩ := parseTree.subtree_decomposition hp₁
  refine ⟨u, v, p₂.yield, y, z, ?_, hvy, ?_, ?_⟩
  · simp_rw [hpuz, hpvy, List.append_assoc]
  · rw [← hpvy]
    apply le_trans p₁.yield_length_le_two_pow_height
    apply Nat.pow_le_pow_of_le_right <;> omega
  · intro k
    apply hguz.trans
    repeat rw [List.map_append]
    apply Derives.append_right
    repeat rw [List.append_assoc]
    apply Derives.append_left
    apply (pumping_string hgpvy k).trans
    apply ((Derives.append_left p₂.yield_derives _).append_right _).trans
    simpa [nTimes] using Derives.refl _

end ChomskyNormalFormGrammar

theorem Language.IsContextFree.pumping {L : Language T} (hL : L.IsContextFree) :
    ∃ p : ℕ, ∀ w ∈ L, w.length ≥ p → ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      (v ++ y).length > 0       ∧
      (v ++ x ++ y).length ≤ p  ∧
      ∀ i : ℕ, u ++ v^+^i ++ x ++ y^+^i ++ z ∈ L := by
  obtain ⟨g, rfl⟩ := hL
  classical
  use 2 ^ g.toCNF.generators.card
  intro w hwg hw2
  by_cases hw : w = []
  · simp [hw] at hw2
  · obtain ⟨u, v, x, y, z, hw, hvy, hvxy, hL⟩ := g.toCNF.pumping (g.toCNF_correct ▸ ⟨hwg, hw⟩) hw2
    exact ⟨u, v, x, y, z, hw, hvy, hvxy, fun i => Set.diff_subset (g.toCNF_correct ▸ hL i)⟩

#print axioms Language.IsContextFree.pumping
