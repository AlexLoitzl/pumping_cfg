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


universe uN uT

variable {T : Type uT}

namespace CNFRule

-- Type of nonterminals.
variable {N : Type uN}

def toCFGRule (r : CNFRule T N) : ContextFreeRule T N :=
  match r with
  | leaf n t => { input := n, output := [Symbol.terminal t] }
  | node n l r => { input := n, output := [Symbol.nonterminal l, Symbol.nonterminal r] }

lemma Rewrites.toCFGRule_match {u v : List (Symbol T N)} {r : CNFRule T N} (huv : r.Rewrites u v) :
    r.toCFGRule.Rewrites u v := by
  induction huv <;> tauto

lemma Rewrites.match_toCFGRule {u v : List (Symbol T N)} {r : CNFRule T N}
    (huv : r.toCFGRule.Rewrites u v) :
    r.Rewrites u v := by
  induction huv with
  | head => cases r <;> tauto
  | cons x _ ih => exact Rewrites.cons r x ih

end CNFRule

namespace CNF

variable [DecidableEq T]

noncomputable def toCFG (g : CNF T) [DecidableEq g.NT] : ContextFreeGrammar T where
  NT := g.NT
  initial := g.initial
  rules := (g.rules.toList.map CNFRule.toCFGRule).toFinset

variable {g : CNF T} [DecidableEq g.NT]

lemma Produces.toCFG_match {u v : List (Symbol T g.NT)} (huv : g.Produces u v) :
    g.toCFG.Produces u v := by
  rcases huv with ⟨r, rin, hrw⟩
  use r.toCFGRule
  constructor
  · unfold toCFG
    simp
    use r
  · exact CNFRule.Rewrites.toCFGRule_match hrw

lemma Derives.toCFG_match {u v : List (Symbol T g.NT)} (huv : g.Derives u v) :
    g.toCFG.Derives u v := by
  induction huv with
  | refl => rfl
  | tail _ last ih =>
    apply ih.trans_produces
    exact Produces.toCFG_match last

lemma Generates.toCFG_match {u : List (Symbol T g.NT)} (hs : g.Generates u) : g.toCFG.Generates u :=
  Derives.toCFG_match hs

lemma Produces.match_toCFG {u v : List (Symbol T g.NT)} (huv : g.toCFG.Produces u v) :
    g.Produces u v := by
  rcases huv with ⟨r, rin, hrw⟩
  simp only [toCFG, List.mem_map] at rin
  rw [List.mem_toFinset] at rin
  obtain ⟨r', rin', rfl⟩ := List.mem_map.1 rin
  exact ⟨r', Finset.mem_toList.1 rin', CNFRule.Rewrites.match_toCFGRule hrw⟩

lemma Derives.match_toCFG {u v : List (Symbol T g.NT)} (huv : g.toCFG.Derives u v) :
    g.Derives u v := by
  induction huv with
  | refl => rfl
  | tail _ last ih =>
    apply ih.trans_produces
    exact Produces.match_toCFG last

lemma Generates.match_toCFG {u : List (Symbol T g.NT)} (hu : g.toCFG.Generates u) : g.Generates u :=
  Derives.match_toCFG hu

theorem toCFG_correct {u : List (Symbol T g.NT)} : g.Generates u ↔ g.toCFG.Generates u :=
  ⟨Generates.toCFG_match, Generates.match_toCFG⟩

end CNF

namespace ContextFreeGrammar

noncomputable def toCNF [DecidableEq T] (g : ContextFreeGrammar T) [DecidableEq g.NT]
    [DecidableEq g.eliminate_empty.eliminate_unitRules.restrict_terminals.NT] -- FIXME How can I provide it
    : CNF T :=
  g.eliminate_empty.eliminate_unitRules.restrict_terminals.restrict_length

variable {g : ContextFreeGrammar T}

lemma new_terminal_rules_terminals {r : ContextFreeRule T g.NT} :
    ∀ r' ∈ new_terminal_rules r, ∃ t, r'.output = [Symbol.terminal t] := by
  unfold new_terminal_rules
  simp
  intro r' s hs
  split <;> intro h <;> simp at h
  · rw [← h]
    simp

variable [DecidableEq g.NT] [DecidableEq T]

lemma terminal_restriction_nonUnit (hn : ∀ r ∈ g.rules, NonUnit r.output) :
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
      apply right_embed_string_nonUnit
      apply hn
      exact hrin
      assumption
  · obtain ⟨s, ⟨hsin, h'⟩⟩ := h'
    cases s <;> simp at h'
    rw [←h']
    constructor

lemma terminal_restriction_nonempty (hne : ∀ r ∈ g.rules, r.output ≠ []) :
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
      apply hne
      exact hrin
  · obtain ⟨s, ⟨hsin, h'⟩⟩ := h'
    cases s <;> simp at h'
    rw [←h']
    simp

lemma restrict_terminals_no_terminals :
    ∀ r ∈ g.restrict_terminals.rules, (∃ t, r.output = [Symbol.terminal t])
      ∨ (∀ s ∈ r.output, ∃ nt, s = Symbol.nonterminal nt) := by
  unfold restrict_terminals restrict_terminal_rules restrict_terminal_rule
  simp
  intro r' r _
  split <;> intro h
  · cases h <;> rename_i h
    · left
      rw [h]
      simp
    · left
      exact new_terminal_rules_terminals r' h
  · cases h <;> rename_i h
    · right
      rw [h]
      simp
      intro s hs
      cases s
      · right
        rename_i t
        use t
        rfl
      · left
        rename_i nt
        use nt
        rfl
    · left
      exact new_terminal_rules_terminals r' h

lemma eliminate_unitRules_nonempty (hne : ∀ r ∈ g.rules, r.output ≠ []) :
    ∀ r' ∈ g.eliminate_unitRules.rules, r'.output ≠ [] := by
  unfold eliminate_unitRules remove_unitRules nonUnit_rules
  simp
  intro r _ _ _ _ h'
  rw [←h']
  simp
  intro r' hrin' hr'
  split
  · intro; contradiction
  · simp
    intro heq
    rw [←heq]
    simp
    apply hne
    exact hrin'

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
  obtain ⟨r', _, heq, hr'⟩ := hrin
  revert hr'
  split
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

variable [DecidableEq g.eliminate_empty.eliminate_unitRules.restrict_terminals.NT] -- FIXME again

theorem toCNF_correct : g.language \ {[]} = g.toCNF.language := by
  unfold toCNF
  rw [eliminate_empty_correct, eliminate_unitRules_correct,
    restrict_terminals_correct, restrict_length_correct]
  unfold Wellformed
  intro r hrin
  match h : r.output with
  | [] =>
    exfalso
    apply terminal_restriction_nonempty at hrin
    exact hrin h
    exact eliminate_unitRules_nonempty eliminate_empty_nonempty
  | [Symbol.terminal _] =>
    cases r; simp at h; rw [h]
    constructor
  | [Symbol.nonterminal _] =>
    exfalso
    apply terminal_restriction_nonUnit at hrin
    · rw [h] at hrin
      contradiction
    · exact eliminate_unitRules_nonUnit
  | _ :: _ :: _ =>
    cases r
    apply restrict_terminals_no_terminals at hrin
    cases hrin <;> rename_i hrin
    · obtain ⟨t, hr⟩ := hrin
      rw [hr] at h
      simp at h
    · rw [h] at hrin
      simp at hrin
      obtain ⟨nt1, hnt1⟩ := hrin.1
      obtain ⟨nt2, hnt2⟩ := hrin.2.1
      simp at h
      rw [h, hnt1, hnt2]
      constructor
      simp
      intro s hsin
      cases hsin with
      | head => constructor
      | tail _ hsin =>
        cases hsin with
        | head => constructor
        | tail _ hsin =>
          obtain ⟨nt3, hs⟩ := hrin.2.2 s hsin
          rw [hs]
          constructor

end ContextFreeGrammar
