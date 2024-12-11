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
  (h: r.Rewrites (u.map Symbol.terminal) v) :
  False := by
  induction u generalizing v with
  | nil => cases h
  | cons u₁ u ih =>
    cases  h; rename_i h
    exact ih h

end ChomskyNormalFormRule

namespace ChomskyNormalFormGrammar

variable {g : ChomskyNormalFormGrammar.{uN,uT} T}

-------------------------------------------
------------------ STUFF ------------------
-------------------------------------------

inductive ParseTree : g.NT → Type _ where
  | tree_leaf {n : g.NT} (t : T)
      (h : (ChomskyNormalFormRule.leaf n t) ∈ g.rules) : ParseTree n
  | tree_node {n c₁ c₂ : g.NT} (t₁ : ParseTree c₁) (t₂ : ParseTree c₂)
      (h : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules) : ParseTree n

namespace ParseTree

def yield {n : g.NT} (p : ParseTree n) : List T :=
  match p with
  | tree_leaf t _ => [t]
  | tree_node t1 t2 _ => yield t1 ++ yield t2

variable {n : g.NT} {p : ParseTree n}

lemma yield_derives : g.Derives [Symbol.nonterminal n] (List.map Symbol.terminal p.yield) := by
  induction p with
  | tree_leaf t hg =>
    simp only [yield]
    exact Produces.single ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
  | tree_node l r hg ihl ihr =>
    simp only [yield]
    apply Produces.trans_derives
    exact ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
    rw [ChomskyNormalFormRule.output, List.map_append, ←List.singleton_append]
    exact (ihr.append_left _).trans (ihl.append_right _)

end ParseTree

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
    (hvu : g.DerivesIn [Symbol.nonterminal n] (List.map Symbol.terminal u) m) :
    ∃ p : ParseTree n, p.yield = u := by
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
      rw [←hr₂] at hwu
      use (ParseTree.tree_leaf t hrg)
      simp only [ParseTree.yield]
      exact hwu.terminal_refl
    | node nᵢ n₁ n₂ =>
      simp at hr₂
      simp at hr₁
      rw [hr₁] at hrg
      rw [←hr₂, ← List.singleton_append] at hwu
      obtain ⟨u₁, u₂, k₁, k₂, hu, hnu₁, hnu₂, hm⟩ := hwu.append_split
      rw [List.map_eq_append_iff] at hu
      obtain ⟨u₁', u₂', hu, hu₁, hu₂⟩ := hu
      rw [←hu₁] at hnu₁
      rw [←hu₂] at hnu₂
      obtain ⟨p₁, hp₁⟩ := hnu₁.yield_rec
      obtain ⟨p₂, hp₂⟩ := hnu₂.yield_rec
      use ParseTree.tree_node p₁ p₂ hrg
      unfold ParseTree.yield
      rw [hp₁, hp₂]
      exact hu.symm

lemma Derives.yield {n : g.NT} {u : List T}
    (h : g.Derives [Symbol.nonterminal n] (List.map Symbol.terminal u)) :
    ∃ p : ParseTree n, p.yield = u := by
  rw [derives_iff_derivesIn] at h
  obtain ⟨_, h⟩ := h
  exact DerivesIn.yield_rec h

end ChomskyNormalFormGrammar
