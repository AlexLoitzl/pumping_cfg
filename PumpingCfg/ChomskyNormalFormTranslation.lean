/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.ChomskyNormalForm
import PumpingCfg.EpsilonElimination
import PumpingCfg.UnitElimination
import PumpingCfg.TerminalRestriction
import PumpingCfg.LengthRestriction

-- Type of terminals.
variable {T : Type}

namespace CNFRule

-- Type of nonterminals.
variable {N : Type}

def toCFGRule (r : CNFRule T N) : ContextFreeRule T N :=
  match r with
  | leaf n t => { input := n, output := [Symbol.terminal t] }
  | node n l r => { input := n, output := [Symbol.nonterminal l, Symbol.nonterminal r] }

lemma Rewrites.toCFGRule_match {v w : List (Symbol T N)} {r : CNFRule T N} (hwv : r.Rewrites v w) :
    r.toCFGRule.Rewrites v w := by
  induction hwv <;> tauto

lemma Rewrites.match_toCFGRule {v w : List (Symbol T N)} {r : CNFRule T N} (hwv : r.toCFGRule.Rewrites v w) :
    r.Rewrites v w := by
  induction hwv with
  | head => cases r <;> tauto
  | cons x _ ih => exact Rewrites.cons r x ih

end CNFRule

namespace CNF

def toCFG (g : CNF T) : ContextFreeGrammar T where
  NT := g.NT
  initial := g.initial
  rules := g.rules.map CNFRule.toCFGRule

variable {g : CNF T}

lemma Produces.toCFG_match {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) : g.toCFG.Produces v w := by
  rcases hvw with ⟨r, rin, hrw⟩
  exact ⟨r.toCFGRule, List.mem_map_of_mem _ rin, CNFRule.Rewrites.toCFGRule_match hrw⟩

lemma Derives.toCFG_match {v w : List (Symbol T g.NT)} (hvw : g.Derives v w) : g.toCFG.Derives v w := by
  induction hvw with
  | refl => rfl
  | tail _ last ih =>
    apply ih.trans_produces
    exact Produces.toCFG_match last

lemma Generates.toCFG_match {s : List (Symbol T g.NT)} (hg : g.Generates s) : g.toCFG.Generates s :=
  Derives.toCFG_match hg

lemma Produces.match_toCFG {v w : List (Symbol T g.NT)} (hvw : g.toCFG.Produces v w) : g.Produces v w := by
  rcases hvw with ⟨r, rin, hrw⟩
  simp only [toCFG, List.mem_map] at rin
  rcases rin with ⟨r', rin', rfl⟩
  exact ⟨r', rin', CNFRule.Rewrites.match_toCFGRule hrw⟩

lemma Derives.match_toCFG {v w : List (Symbol T g.NT)} (hvw : g.toCFG.Derives v w) : g.Derives v w := by
  induction hvw with
  | refl => rfl
  | tail _ last ih =>
    apply ih.trans_produces
    exact Produces.match_toCFG last

lemma Generates.match_toCFG {s : List (Symbol T g.NT)} (hg : g.toCFG.Generates s) : g.Generates s :=
  Derives.match_toCFG hg

theorem toCFG_correct {s : List (Symbol T g.NT)} : g.Generates s ↔ g.toCFG.Generates s :=
  ⟨Generates.toCFG_match, Generates.match_toCFG⟩


end CNF
