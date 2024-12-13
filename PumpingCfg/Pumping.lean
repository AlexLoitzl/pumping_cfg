/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.Utils
import PumpingCfg.ChomskyNormalForm
import PumpingCfg.ParseTree

universe uT uN

variable {T : Type uT}

namespace ChomskyNormalFormGrammar

noncomputable def generators (g : ChomskyNormalFormGrammar.{uN, uT} T) [DecidableEq g.NT] :
    Finset g.NT :=
  (g.rules.toList.map ChomskyNormalFormRule.input).toFinset

variable {g : ChomskyNormalFormGrammar.{uN, uT} T} [DecidableEq g.NT]

lemma pumping_subtree {u v : List T} {n : g.NT} {p₁ p₂ : parseTree n} (hne : p₁ ≠ p₂)
    (hpp : p₂.Subtree p₁) (huv : p₁.yield = u ++ p₂.yield ++ v) :
    ∀ i : ℕ, ∃ p : parseTree n, p.yield = u^^i ++ p₂.yield ++ v^^i := by sorry

lemma subtree_repeat_root_height {n : g.NT} {p : parseTree n}
    (hp : p.yield.length ≥ 2 ^ g.generators.card) :
    ∃ (n' : g.NT) (p₁ p₂ : parseTree n'),
      p₁.Subtree p ∧ p₂.Subtree p₁ ∧ p₁.height ≤ g.generators.card ∧ p₁ ≠ p₂:= by sorry

lemma cnf_pumping {w : List T} (hwg : w ∈ g.language) (hw : w.length ≥ 2 ^ g.generators.card) :
    ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      (v ++ y).length > 0       ∧
      (v ++ x ++ y).length ≤ 2 ^ g.generators.card  ∧
      ∀ i : ℕ, u ++ v^^i ++ x ++ y^^i ++ z ∈ g.language := by
  obtain ⟨p, rfl⟩ := hwg.yield
  obtain ⟨n, p₁, p₂, hp₁, hp₂, hpg, hpp⟩ := subtree_repeat_root_height hw
  obtain ⟨v, y, hpvy, hvy⟩ := parseTree.strict_subtree_decomposition hp₂ hpp
  obtain ⟨u, z, hpuz⟩ := parseTree.subtree_decomposition hp₁
  refine ⟨u, v, p₂.yield, y, z, ?_, hvy, ?_, ?_⟩
  · simp_rw [hpuz, hpvy, List.append_assoc]
  · rw [← hpvy]
    apply le_trans p₁.yield_length_le_two_pow_height
    apply Nat.pow_le_pow_of_le_right <;> omega
  · intro k
    obtain ⟨q₁, hq₁⟩ := pumping_subtree hpp hp₂ hpvy k
    obtain ⟨q, hq⟩ := parseTree.subtree_replacement q₁ hp₁ hpuz
    simpa [hq, hq₁] using q.yield_derives

end ChomskyNormalFormGrammar

theorem pumping_lemma {L : Language T} (hL : L.IsContextFree) :
    ∃ p : ℕ, ∀ w ∈ L, w.length ≥ p → ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      (v ++ y).length > 0       ∧
      (v ++ x ++ y).length ≤ p  ∧
      ∀ i : ℕ, u ++ v^^i ++ x ++ y^^i ++ z ∈ L := by
  obtain ⟨g, rfl⟩ := hL
  classical
  use 2 ^ g.generators.card
  intro w hwL hwg
  have fixme : g.language = g.language \ {[]} := sorry
  have todo : g.generators.card = g.toCNF.generators.card := sorry
  rw [fixme, ContextFreeGrammar.toCNF_correct] at hwL ⊢
  exact todo ▸ ChomskyNormalFormGrammar.cnf_pumping hwL (todo ▸ hwg)
