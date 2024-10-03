/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.Utils

-- Type of terminals. Can be unrestricted I think
variable {T : Type}

-- Define measure "max_spread" which captures the biggest spread n of all rules Vᵢ -> sᵢ₀...sᵢₙ
def spread (r: ContextFreeRule T N) : ℕ := r.output.length

def max_spread (g: ContextFreeGrammar T) : ℕ :=
  List.foldl (Nat.max) 0 (List.map spread g.rules)

-- Prove that the derivation has at least some steps?
lemma derives_max_spread_incr (g: ContextFreeGrammar T) (u v : List (Symbol T g.NT)) (hd: g.Derives u v): ⊤ := sorry

-- Why do I have to write Language.IsContextfree rather than L.isContextfree?
-- I definitely need to restrict the type of variables with Fintype
theorem pumping_lemma {T : Type} {L : Language T} (cf: Language.IsContextFree L) :
  ∃ p : ℕ, ∀ w ∈ L, w.length ≥ p → ∃ u v x y z : List T,
    w = u ++ v ++ x ++ y ++ z ∧
    (v ++ y).length > 0       ∧
    (v ++ x ++ y).length ≤ p  ∧
    ∀ i : ℕ, u ++ (v ^^ i) ++ x ++ y ^^ i ++ z ∈ L :=
  sorry
