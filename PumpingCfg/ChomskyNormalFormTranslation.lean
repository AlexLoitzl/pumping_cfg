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

namespace ChomskyNormalFormRule

-- Type of nonterminals.
variable {N : Type uN}

def toCFGRule (r : ChomskyNormalFormRule T N) : ContextFreeRule T N :=
  match r with
  | leaf n t => { input := n, output := [Symbol.terminal t] }
  | node n l r => { input := n, output := [Symbol.nonterminal l, Symbol.nonterminal r] }

lemma Rewrites.toCFGRule_match {u v : List (Symbol T N)} {r : ChomskyNormalFormRule T N}
    (huv : r.Rewrites u v) :
    r.toCFGRule.Rewrites u v := by
  induction huv <;> tauto

lemma Rewrites.match_toCFGRule {u v : List (Symbol T N)} {r : ChomskyNormalFormRule T N}
    (huv : r.toCFGRule.Rewrites u v) :
    r.Rewrites u v := by
  induction huv with
  | head => cases r <;> tauto
  | cons x _ ih => exact Rewrites.cons r x ih

end ChomskyNormalFormRule

namespace ChomskyNormalFormGrammar

variable [DecidableEq T]

noncomputable def toCFG (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] : ContextFreeGrammar T where
  NT := g.NT
  initial := g.initial
  rules := (g.rules.toList.map ChomskyNormalFormRule.toCFGRule).toFinset

variable {g : ChomskyNormalFormGrammar T} [DecidableEq g.NT]

lemma Produces.toCFG_match {u v : List (Symbol T g.NT)} (huv : g.Produces u v) :
    g.toCFG.Produces u v := by
  rcases huv with ⟨r, rin, hrw⟩
  use r.toCFGRule
  constructor
  · simp only [toCFG, List.mem_toFinset, List.mem_map, Finset.mem_toList]
    use r
  · exact ChomskyNormalFormRule.Rewrites.toCFGRule_match hrw

lemma Derives.toCFG_match {u v : List (Symbol T g.NT)} (huv : g.Derives u v) :
    g.toCFG.Derives u v := by
  induction huv with
  | refl => rfl
  | tail _ last ih =>
    apply ih.trans_produces
    exact Produces.toCFG_match last

lemma Generates.toCFG_match {u : List (Symbol T g.NT)} (hu : g.Generates u) : g.toCFG.Generates u :=
  Derives.toCFG_match hu

lemma Produces.match_toCFG {u v : List (Symbol T g.NT)} (huv : g.toCFG.Produces u v) :
    g.Produces u v := by
  rcases huv with ⟨r, rin, hrw⟩
  simp only [toCFG, List.mem_map] at rin
  rw [List.mem_toFinset] at rin
  obtain ⟨r', rin', rfl⟩ := List.mem_map.1 rin
  exact ⟨r', Finset.mem_toList.1 rin', ChomskyNormalFormRule.Rewrites.match_toCFGRule hrw⟩

lemma Derives.match_toCFG {u v : List (Symbol T g.NT)} (huv : g.toCFG.Derives u v) :
    g.Derives u v := by
  induction huv with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces (Produces.match_toCFG last)

lemma Generates.match_toCFG {u : List (Symbol T g.NT)} (hu : g.toCFG.Generates u) : g.Generates u :=
  Derives.match_toCFG hu

theorem toCFG_correct {u : List (Symbol T g.NT)} : g.Generates u ↔ g.toCFG.Generates u :=
  ⟨Generates.toCFG_match, Generates.match_toCFG⟩

end ChomskyNormalFormGrammar

namespace ContextFreeGrammar

noncomputable def toChomskyNormalForm [DecidableEq T] (g : ContextFreeGrammar T) [DecidableEq g.NT]
    : ChomskyNormalFormGrammar T :=
  g.eliminate_empty.eliminate_unitRules.restrict_terminals.restrict_length (e := by
    unfold restrict_terminals eliminate_unitRules eliminate_empty
    exact instDecidableEqSum)

variable {g : ContextFreeGrammar T}

lemma new_terminal_rules_terminals {r : ContextFreeRule T g.NT} :
    ∀ r' ∈ new_terminal_rules r, ∃ t, r'.output = [Symbol.terminal t] := by
  unfold new_terminal_rules
  simp only [List.mem_filterMap, forall_exists_index, and_imp]
  intro r' s hs
  split <;> intro h <;> simp only [reduceCtorEq, Option.some.injEq] at h
  · rw [← h]
    simp

variable [DecidableEq g.NT] [DecidableEq T]

lemma terminal_restriction_nonUnit (hn : ∀ r ∈ g.rules, NonUnit r.output) :
    ∀ r' ∈ g.restrict_terminals.rules, NonUnit r'.output := by
  simp only [restrict_terminals, restrict_terminal_rules, restrict_terminal_rule, new_terminal_rules,
    List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and,
    List.mem_cons, List.mem_filterMap, forall_exists_index, and_imp]
  intro r' r hrin h'
  cases h' <;> rename_i h'
  · revert h'
    split <;> intro h'
    · rw [h']
      constructor
    · rw [h']
      simp only
      apply right_embed_string_nonUnit (hn _ hrin)
      assumption
  · obtain ⟨s, ⟨hsin, h'⟩⟩ := h'
    cases s <;> simp [reduceCtorEq, Option.some.injEq] at h'
    rw [←h']
    constructor

lemma terminal_restriction_nonempty (hne : ∀ r ∈ g.rules, r.output ≠ []) :
    ∀ r' ∈ g.restrict_terminals.rules, r'.output ≠ [] := by
  simp only [restrict_terminals, restrict_terminal_rules, restrict_terminal_rule, new_terminal_rules,
    List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and,
    List.mem_cons, List.mem_filterMap, ne_eq, forall_exists_index, and_imp]
  intro r' r hrin h'
  cases h' <;> rename_i h'
  · revert h'
    split <;> intro h'
    · rw [h']
      simp
    · rw [h']
      simp only [List.map_eq_nil_iff, ne_eq]
      exact hne _ hrin
  · obtain ⟨s, ⟨hsin, h'⟩⟩ := h'
    cases s <;> simp [reduceCtorEq, Option.some.injEq] at h'
    rw [←h']
    simp

lemma restrict_terminals_no_terminals :
    ∀ r ∈ g.restrict_terminals.rules, (∃ t, r.output = [Symbol.terminal t])
      ∨ (∀ s ∈ r.output, ∃ nt, s = Symbol.nonterminal nt) := by
  unfold restrict_terminals restrict_terminal_rules restrict_terminal_rule
  simp only [restrict_terminals, restrict_terminal_rules, restrict_terminal_rule, List.mem_toFinset,
    List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and, List.mem_cons,
    Sum.exists, forall_exists_index, and_imp]
  intro r' r _
  split <;> intro h
  · cases h <;> rename_i h
    · rw [h]
      simp
    · left
      exact new_terminal_rules_terminals r' h
  · cases h <;> rename_i h
    · right
      rw [h]
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
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
  simp only [eliminate_unitRules, remove_unitRules, nonUnit_rules, List.mem_toFinset,
    List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists, ne_eq,
    forall_exists_index, and_imp]
  intro r _ _ _ _ h'
  rw [←h']
  simp only [List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some, forall_exists_index, and_imp]
  intro r' hrin' hr'
  split
  · intro; contradiction
  · simp only [Option.some.injEq]
    intro heq
    rw [←heq]
    simp only
    apply hne _ hrin'

lemma eliminate_empty_nonempty : ∀ r ∈ g.eliminate_empty.rules, r.output ≠ [] := by
  simp only [ne_eq, eliminate_empty]
  intro r hrin
  exact in_remove_not_epsilon hrin

lemma eliminate_unitRules_nonUnit : ∀ r ∈ g.eliminate_unitRules.rules, NonUnit r.output := by
  unfold eliminate_unitRules remove_unitRules nonUnit_rules
  simp only [eliminate_unitRules, remove_unitRules, nonUnit_rules, List.mem_toFinset,
    List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists, forall_exists_index, and_imp]
  intro r l nt1 nt2 _ h hrin
  rw [←h] at hrin
  simp only [List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some] at hrin
  obtain ⟨r', _, heq, hr'⟩ := hrin
  revert hr'
  split
  · simp
  · simp only [Option.some.injEq]
    intro heq
    rw [←heq]
    rename_i h
    simp only
    unfold NonUnit
    split
    · apply h
      assumption
    · constructor

theorem toChomskyNormalForm_correct : g.language \ {[]} = g.toChomskyNormalForm.language := by
  unfold toChomskyNormalForm
  rw [eliminate_empty_correct, eliminate_unitRules_correct, restrict_terminals_correct]
  rw [restrict_length_correct (e := (id (id (id (id instDecidableEqSum)))))]
  intro r hrin
  match h : r.output with
  | [] =>
    exfalso
    exact terminal_restriction_nonempty (eliminate_unitRules_nonempty eliminate_empty_nonempty) _
      hrin h
  | [Symbol.terminal _] =>
    cases r; simp only at h; rw [h]
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
      simp only [List.mem_cons, forall_eq_or_imp] at hrin
      obtain ⟨nt1, hnt1⟩ := hrin.1
      obtain ⟨nt2, hnt2⟩ := hrin.2.1
      simp only at h
      rw [h, hnt1, hnt2]
      constructor
      simp only [List.length_cons, Nat.le_add_left]
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
