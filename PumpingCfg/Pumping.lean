/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.Utils

theorem pumping_lemma {T : Type} {L : Language T} (hL : L.IsContextFree) :
  ∃ p : ℕ, ∀ w ∈ L, w.length ≥ p → ∃ u v x y z : List T,
    w = u ++ v ++ x ++ y ++ z ∧
    (v ++ y).length > 0       ∧
    (v ++ x ++ y).length ≤ p  ∧
    ∀ i : ℕ, u ++ (v ^^ i) ++ x ++ y ^^ i ++ z ∈ L :=
  sorry
