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
    cases hruv
    rename_i hru
    exact ih hru

end ChomskyNormalFormRule

namespace ChomskyNormalFormGrammar

variable {g : ChomskyNormalFormGrammar.{uN,uT} T}

-------------------------------------------
------------------ STUFF ------------------
-------------------------------------------

inductive parseTree : g.NT → Type _ where
  | tree_leaf {n : g.NT} (t : T)
      (h : (ChomskyNormalFormRule.leaf n t) ∈ g.rules) : parseTree n
  | tree_node {n c₁ c₂ : g.NT} (t₁ : parseTree c₁) (t₂ : parseTree c₂)
      (h : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules) : parseTree n

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

-- TODO
/-- `SubTree p₁ p₂` encodes that `p₁` is a subtree of `p2` -/
inductive Subtree {n₁ n₂ : g.NT} : parseTree n₁ → parseTree n₂ → Prop where
  | refl_leaf {t : T} (hmk : n₁ = n₂) (hrn₁ : (ChomskyNormalFormRule.leaf n₁ t) ∈ g.rules)
      (hrn₂ : (ChomskyNormalFormRule.leaf n₂ t) ∈ g.rules) :
      Subtree (tree_leaf t hrn₁) (tree_leaf t hrn₂)

variable {n : g.NT} {p : parseTree n}

lemma yield_derives : g.Derives [Symbol.nonterminal n] (p.yield.map Symbol.terminal) := by
  induction p with
  | tree_leaf t hg =>
    simp only [yield]
    exact Produces.single ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
  | tree_node l r hg ihl ihr =>
    simp only [yield]
    apply Produces.trans_derives
    exact ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
    rw [ChomskyNormalFormRule.output, List.map_append, ← List.singleton_append]
    exact (ihr.append_left _).trans (ihl.append_right _)

lemma height_pos : p.height > 0 := by cases p <;> simp [height]

lemma yield_length_le_two_pow_height : p.yield.length ≤ 2^(p.height - 1) := by
  induction p with
  | tree_leaf => simp [yield, height]
  | tree_node t₁ t₂ hpg ih₁ ih₂=>
    simp [height, yield]
    have h : t₁.yield.length + t₂.yield.length ≤ 2 ^ (t₁.height -1) + 2 ^ (t₂.height -1) := by omega
    have h'' : 2 ^ (t₁.height -1) + 2 ^ (t₂.height - 1)
        ≤ 2 ^ ((max t₁.height t₂.height) -1) + 2 ^ ((max t₁.height t₂.height) -1) := by
      apply Nat.add_le_add <;> apply Nat.pow_le_pow_of_le_right <;> omega
    apply le_trans h
    apply le_trans h''
    have h''' : (max t₁.height t₂.height) = (max t₁.height t₂.height) -1 + 1 := by
      rw [Nat.sub_one_add_one]
      have h : 0 < (max t₁.height t₂.height) := lt_sup_of_lt_left t₁.height_pos
      omega
    nth_rewrite 3 [h''']
    rw [Nat.two_pow_succ]

lemma subtree_decomposition {n₁ n₂ : g.NT} {p₁ : parseTree n₁} {p₂ : parseTree n₂}
    (hpp : Subtree p₂ p₁) :
    ∃ u v, p₁.yield = u ++ p₂.yield ++ v := by sorry

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
    apply Function.Injective.list_map; swap
    exact huv.zero_steps_eq
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
      simp at hr₁ hr₂
      rw [hr₁] at hrg
      rw [← hr₂] at hwu
      use (parseTree.tree_leaf t hrg)
      simp only [parseTree.yield]
      exact hwu.terminal_refl
    | node nᵢ n₁ n₂ =>
      simp at hr₂
      simp at hr₁
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
      rw [hp₁, hp₂]
      exact hu.symm

lemma Derives.yield {n : g.NT} {u : List T}
    (hnu : g.Derives [Symbol.nonterminal n] (u.map Symbol.terminal)) :
    ∃ p : parseTree n, p.yield = u := by
  rw [derives_iff_derivesIn] at hnu
  exact DerivesIn.yield_rec hnu.choose_spec

end ChomskyNormalFormGrammar
