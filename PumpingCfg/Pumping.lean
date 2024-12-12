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

section PumpingCNF
namespace ChomskyNormalFormGrammar

noncomputable def generators (g : ChomskyNormalFormGrammar.{uN, uT} T) [DecidableEq g.NT] : Finset g.NT :=
  (g.rules.toList.map ChomskyNormalFormRule.input).toFinset

variable {g : ChomskyNormalFormGrammar.{uN, uT} T} [DecidableEq g.NT]

lemma pumping_subtree {u v : List T} {n : g.NT} {p₁ p₂ : parseTree n} (hne: p₁ ≠ p₂)
  (hpp : p₂.Subtree p₁) (hy : p₁.yield = u ++ p₂.yield ++ v) :
  ∀ i : ℕ, ∃ p : parseTree n, p.yield = u^^i ++ p₂.yield ++ v^^i := by sorry

lemma subtree_repeat_root_height {n : g.NT} {p : parseTree n}
    (hp : p.yield.length ≥ 2^g.generators.card) :
    ∃ (n' : g.NT) (p₁ p₂ : parseTree n'),
      p₁.Subtree p ∧ p₂.Subtree p₁ ∧ p₁.height ≤ g.generators.card := by sorry

lemma cnf_pumping_lemma {w : List T} (hwg : w ∈ g.language) (hw : w.length ≥ 2^g.generators.card) :
    ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      (v ++ y).length > 0       ∧
      (v ++ x ++ y).length ≤ 2^g.generators.card  ∧
      ∀ i : ℕ, u ++ v ^^ i ++ x ++ y ^^ i ++ z ∈ g.language := by
  sorry

end ChomskyNormalFormGrammar
end PumpingCNF

theorem pumping_lemma {L : Language T} (hL : L.IsContextFree) :
  ∃ p : ℕ, ∀ w ∈ L, w.length ≥ p → ∃ u v x y z : List T,
    w = u ++ v ++ x ++ y ++ z ∧
    (v ++ y).length > 0       ∧
    (v ++ x ++ y).length ≤ p  ∧
    ∀ i : ℕ, u ++ v ^^ i ++ x ++ y ^^ i ++ z ∈ L := by
  sorry
