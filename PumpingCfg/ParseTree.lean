/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import PumpingCfg.ChomskyNormalForm
import PumpingCfg.ChomskyNormalFormTranslation
import PumpingCfg.ChomskyCountingSteps

universe uN uT

variable {T : Type uT}

namespace ChomskyNormalFormRule

lemma Rewrites.word {T N : Type*} {r : ChomskyNormalFormRule T N} {u : List T} {v : List (Symbol T N)}
    (hruv : r.Rewrites (u.map Symbol.terminal) v) :
    False := by
  induction u generalizing v with
  | nil => cases hruv
  | cons u₁ u ih =>
    cases hruv with
    | cons _ _ hru => exact ih hru

end ChomskyNormalFormRule

namespace ChomskyNormalFormGrammar

variable {g : ChomskyNormalFormGrammar.{uN,uT} T}

-------------------------------------------
------------------ STUFF ------------------
-------------------------------------------

inductive parseTree : g.NT → Type _ where
  | tree_leaf {n : g.NT} (t : T)
      (hnt : (ChomskyNormalFormRule.leaf n t) ∈ g.rules) : parseTree n
  | tree_node {n c₁ c₂ : g.NT} (t₁ : parseTree c₁) (t₂ : parseTree c₂)
      (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules) : parseTree n

-- noncomputable instance {n : g.NT} [eqt : DecidableEq T] [DecidableEq g.NT] :
--     DecidableEq (ParseTree n) := by
--   intro x y
--   match x, y with
--   | ParseTree.tree_leaf _ _, ParseTree.tree_leaf _ _ =>
--     simp only [ParseTree.tree_leaf.injEq]
--     apply eqt
--   | @ParseTree.tree_node _ _ _ c₁ c₂ t₁ t₂ h₁, @ParseTree.tree_node _ _ _ c₃ c₄ t₃ t₄ h₂ =>
--     simp only [ParseTree.tree_node.injEq]
--     exact Classical.propDecidable (c₁ = c₃ ∧ c₂ = c₄ ∧ HEq t₁ t₃ ∧ HEq t₂ t₄)
--   | ParseTree.tree_leaf _ _, ParseTree.tree_node _ _ _ =>
--     simp only [reduceCtorEq]
--     exact instDecidableFalse
--   | ParseTree.tree_node _ _ _, ParseTree.tree_leaf _ _ =>
--     simp only [reduceCtorEq]
--     exact instDecidableFalse

namespace parseTree

def yield {n : g.NT} (p : parseTree n) : List T :=
  match p with
  | tree_leaf t _ => [t]
  | tree_node t₁ t₂ _ => yield t₁ ++ yield t₂

def height {n : g.NT} (p : parseTree n) : ℕ :=
  match p with
  | tree_leaf _ _ => 1
  | tree_node t₁ t₂ _ => max (height t₁) (height t₂) + 1

/-- `IsSubTreeOf p₁ p₂` encodes that `p₁` is a subtree of `p₂` -/
inductive IsSubtreeOf : {n₁ : g.NT} →  {n₂ : g.NT} → parseTree n₁ → parseTree n₂ → Prop where
  | leaf_refl {t : T} {n : g.NT} (hrn : (ChomskyNormalFormRule.leaf n t) ∈ g.rules) :
      IsSubtreeOf (tree_leaf t hrn) (tree_leaf t hrn)
  | node_refl {nl nr n : g.NT} (pl : parseTree nl) (pr : parseTree nr)
      (hrn : (ChomskyNormalFormRule.node n nl nr) ∈ g.rules) :
      IsSubtreeOf (tree_node pl pr hrn) (tree_node pl pr hrn)
  | left_sub {nl nr n₁ n₂ : g.NT} (pl : parseTree nl) (pr : parseTree nr) (p : parseTree n₂)
      (hrn₁ : (ChomskyNormalFormRule.node n₁ nl nr) ∈ g.rules) (hppl : IsSubtreeOf p pl) :
      IsSubtreeOf p (tree_node pl pr hrn₁)
  | right_sub {nl nr n₁ n₂ : g.NT} (pl : parseTree nl) (pr : parseTree nr) (p : parseTree n₂)
      (hrn₁ : (ChomskyNormalFormRule.node n₁ nl nr) ∈ g.rules) (hppr : IsSubtreeOf p pr) :
      IsSubtreeOf p (tree_node pl pr hrn₁)

variable {n : g.NT} {p : parseTree n}

lemma yield_derives : g.Derives [Symbol.nonterminal n] (p.yield.map Symbol.terminal) := by
  induction p with
  | tree_leaf t hg =>
    exact Produces.single ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
  | tree_node l r hg ihl ihr =>
    simp only [yield]
    apply Produces.trans_derives ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
    rw [ChomskyNormalFormRule.output, List.map_append, ← List.singleton_append]
    exact (ihr.append_left _).trans (ihl.append_right _)

lemma height_pos : p.height > 0 := by cases p <;> simp [height]

lemma yield_length_le_two_pow_height : p.yield.length ≤ 2^(p.height - 1) := by
  induction p with
  | tree_leaf => simp [yield, height]
  | tree_node t₁ t₂ hpg ih₁ ih₂=>
    simp only [yield, height, List.length_append, Nat.add_one_sub_one]
    have ht : t₁.yield.length + t₂.yield.length ≤ 2 ^ (t₁.height -1) + 2 ^ (t₂.height -1) := by
      omega
    have ht' : 2 ^ (t₁.height - 1) + 2 ^ (t₂.height - 1)
        ≤ 2 ^ (max t₁.height t₂.height - 1) + 2 ^ (max t₁.height t₂.height - 1) := by
      apply Nat.add_le_add <;> apply Nat.pow_le_pow_of_le_right <;> omega
    apply le_trans ht
    apply le_trans ht'
    have ht'' : max t₁.height t₂.height = max t₁.height t₂.height - 1 + 1 := by
      rw [Nat.sub_one_add_one]
      have : 0 < max t₁.height t₂.height := lt_sup_of_lt_left t₁.height_pos
      omega
    nth_rewrite 3 [ht'']
    rw [Nat.two_pow_succ]

lemma yield_length_pos : p.yield.length > 0 := by
  induction p with
  | tree_leaf => simp [yield]
  | tree_node =>
    simp only [yield, List.length_append]
    omega

lemma subtree_replacement {u v : List T} {n₁ n₂ : g.NT} {p : parseTree n₁} {p₁ : parseTree n₂}
    (p₂ : parseTree n₂) (hpp : IsSubtreeOf p₁ p) (huv : p.yield = u ++ p₁.yield ++ v) :
    ∃ p' : parseTree n₁, p'.yield = u ++ p₂.yield ++ v := by sorry

lemma subtree_decomposition {n₁ n₂ : g.NT} {p₁ : parseTree n₁} {p₂ : parseTree n₂}
    (hpp : IsSubtreeOf p₂ p₁) :
    ∃ u v, p₁.yield = u ++ p₂.yield ++ v := by
  induction hpp with
  | leaf_refl => exact ⟨[], [], rfl⟩
  | node_refl =>
    use [], []
    simp
  | left_sub _ p₂ _ _ _ ih =>
    simp [yield]
    obtain ⟨u, v, huv⟩ := ih
    rw [huv]
    use u, v ++ p₂.yield
    simp
  | right_sub p₁ _ _ _ _ ih =>
    simp [yield]
    obtain ⟨u, v, huv⟩ := ih
    rw [huv]
    use p₁.yield ++ u, v
    simp

lemma strict_subtree_decomposition {n : g.NT} {p₁ : parseTree n} {p₂ : parseTree n}
    (hpp₁ : IsSubtreeOf p₂ p₁) (hne : p₁ ≠ p₂) :
    ∃ u v, p₁.yield = u ++ p₂.yield ++ v ∧ (u ++ v).length > 0 := by
  cases hpp₁ with
  | leaf_refl | node_refl => contradiction
  | left_sub _ p₃ _ _ hp₂ =>
    obtain ⟨u, v, huv⟩ := subtree_decomposition hp₂
    simp_rw [yield, huv]
    use u, v ++ p₃.yield
    constructor
    · simp
    · have h := p₃.yield_length_pos
      repeat rw [List.length_append]
      omega
  | right_sub p₃ _ _ _ hp₂ =>
    obtain ⟨u, v, huv⟩ := subtree_decomposition hp₂
    simp_rw [yield, huv]
    use p₃.yield ++ u , v
    constructor
    · simp
    · have h := p₃.yield_length_pos
      repeat rw [List.length_append]
      omega

end parseTree

lemma Produces.rule {n : g.NT} {u : List (Symbol T g.NT)}
    (hnu : g.Produces [Symbol.nonterminal n] u) :
    ∃ r ∈ g.rules, r.input = n ∧ r.output = u := by
  obtain ⟨r, hrg, hnu⟩ := hnu
  cases hnu
  · exact ⟨_, hrg, rfl, rfl⟩
  · exact ⟨_, hrg, rfl, rfl⟩
  · contradiction

lemma DerivesIn.terminal_refl {u v : List T} {m : ℕ}
    (huv : g.DerivesIn (u.map Symbol.terminal) (v.map Symbol.terminal) m) :
    u = v := by
  cases m with
  | zero =>
    apply Function.Injective.list_map _ huv.zero_steps_eq
    apply Symbol.terminal.inj
  | succ m =>
    obtain ⟨w, huw, hwv⟩ := huv.head_of_succ
    obtain ⟨r, hrg, huw⟩ := huw
    exfalso
    exact huw.word

private lemma DerivesIn.yield_rec {n : g.NT} {u : List T} {m : ℕ}
    (hvu : g.DerivesIn [Symbol.nonterminal n] (u.map Symbol.terminal) m) :
    ∃ p : parseTree n, p.yield = u := by
  cases m with
  | zero =>
    apply DerivesIn.zero_steps_eq at hvu
    cases u <;> simp at hvu
  | succ m =>
    obtain ⟨w, hvw, hwu⟩ := hvu.head_of_succ
    obtain ⟨r, hrg, hr₁, hr₂⟩ := hvw.rule
    cases r with
    | leaf n t =>
      rw [ChomskyNormalFormRule.input] at hr₁
      rw [ChomskyNormalFormRule.output] at hr₂
      rw [hr₁] at hrg
      rw [← hr₂] at hwu
      exact ⟨parseTree.tree_leaf t hrg, hwu.terminal_refl⟩
    | node nᵢ n₁ n₂ =>
      rw [ChomskyNormalFormRule.input] at hr₁
      rw [ChomskyNormalFormRule.output] at hr₂
      rw [hr₁] at hrg
      rw [← hr₂, ← List.singleton_append] at hwu
      obtain ⟨u₁, u₂, k₁, k₂, hu, hnu₁, hnu₂, hm⟩ := hwu.append_split
      rw [List.map_eq_append_iff] at hu
      obtain ⟨u₁', u₂', hu, hu₁, hu₂⟩ := hu
      rw [← hu₁] at hnu₁
      rw [← hu₂] at hnu₂
      obtain ⟨p₁, hp₁⟩ := hnu₁.yield_rec
      obtain ⟨p₂, hp₂⟩ := hnu₂.yield_rec
      use parseTree.tree_node p₁ p₂ hrg
      unfold parseTree.yield
      rw [hp₁, hp₂, hu]

lemma Derives.yield {n : g.NT} {u : List T}
    (hnu : g.Derives [Symbol.nonterminal n] (u.map Symbol.terminal)) :
    ∃ p : parseTree n, p.yield = u := by
  rw [derives_iff_derivesIn] at hnu
  exact hnu.choose_spec.yield_rec

end ChomskyNormalFormGrammar
