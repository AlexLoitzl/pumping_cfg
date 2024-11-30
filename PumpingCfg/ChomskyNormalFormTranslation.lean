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

namespace ContextFreeGrammar

noncomputable def toCNF (g : ContextFreeGrammar.{0,0} T) [DecidableEq g.NT] : CNF T :=
  g.eliminate_empty.eliminate_unitRules.restrict_terminals.restrict_length

variable {g : ContextFreeGrammar T}

lemma terminal_restriction_nonUnit (h : ∀ r ∈ g.rules, NonUnit r.output) :
  ∀ r' ∈ g.restrict_terminals.rules, NonUnit r'.output := by
  unfold restrict_terminals restrict_terminal_rules restrict_terminal_rule new_terminal_rules
  simp
  intro r' r hrin h'
  cases h' <;> rename_i h'
  · revert h'
    split <;> intro h'
    · rw [h']
      constructor
    · rw [h']
      simp
      apply lift_string_nonUnit
      apply h
      exact hrin
      assumption
  · obtain ⟨s, ⟨hsin, h'⟩⟩ := h'
    cases s <;> simp at h'
    rw [←h']
    constructor

lemma terminal_restriction_nonempty (h : ∀ r ∈ g.rules, r.output ≠ []) :
  ∀ r' ∈ g.restrict_terminals.rules, r'.output ≠ [] := by
  unfold restrict_terminals restrict_terminal_rules restrict_terminal_rule new_terminal_rules
  simp
  intro r' r hrin h'
  cases h' <;> rename_i h'
  · revert h'
    split <;> intro h'
    · rw [h']
      simp
    · rw [h']
      simp
      apply h
      exact hrin
  · obtain ⟨s, ⟨hsin, h'⟩⟩ := h'
    cases s <;> simp at h'
    rw [←h']
    simp

variable [DecidableEq g.NT]

lemma eliminate_unitRules_nonempty (h : ∀ r ∈ g.rules, r.output ≠ []) : ∀ r' ∈ g.eliminate_unitRules.rules, r'.output ≠ [] := by
  unfold eliminate_unitRules remove_unitRules nonUnit_rules
  simp
  intro r _ _ _ _ h'
  rw [←h']
  simp
  intro r' hrin'
  split
  · split
    · intro; contradiction
    · simp
      intro heq
      rw [←heq]
      simp
      apply h
      exact hrin'
  · intro; contradiction

lemma eliminate_empty_nonempty : ∀ r ∈ g.eliminate_empty.rules, r.output ≠ [] := by
  unfold eliminate_empty
  simp
  intro r hrin
  exact in_remove_not_epsilon hrin

lemma eliminate_unitRules_nonUnit : ∀ r ∈ g.eliminate_unitRules.rules, NonUnit r.output := by
  unfold eliminate_unitRules remove_unitRules nonUnit_rules
  simp
  intro r l nt1 nt2 _ h hrin
  rw [← h] at hrin
  simp at hrin
  obtain ⟨r', _, hr'⟩ := hrin
  revert hr'
  split
  · split
    · simp
    · simp
      intro heq
      rw [←heq]
      rename_i h
      simp
      unfold NonUnit
      split
      · apply h
        assumption
      · constructor
  · simp

theorem toCNF_correct : g.language \ {[]} = g.toCNF.language := by
  unfold toCNF
  rw [eliminate_empty_correct, eliminate_unitRules_correct, restrict_terminals_correct, restrict_length_correct]
  unfold wellformed
  intro r hrin
  unfold ContextFreeRule.wellformed
  match h : r.output with
  | [] =>
    simp
    apply terminal_restriction_nonempty at hrin
    exact hrin h
    exact eliminate_unitRules_nonempty eliminate_empty_nonempty
  | [Symbol.terminal _] => constructor
  | [Symbol.nonterminal _] =>
    simp
    apply terminal_restriction_nonUnit at hrin
    · rw [h] at hrin
      contradiction
    · exact eliminate_unitRules_nonUnit
  | _ :: _ :: _ =>

    sorry

end ContextFreeGrammar
