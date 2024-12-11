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

variable {N : Type uN}

/-- Translation of `ChomskyNormalFormRule` to `ContextFreeRule` -/
def toCFGRule (r : ChomskyNormalFormRule T N) : ContextFreeRule T N :=
  match r with
  | leaf n t => { input := n, output := [Symbol.terminal t] }
  | node nᵢ n₁ n₂ => { input := nᵢ, output := [Symbol.nonterminal n₁, Symbol.nonterminal n₂] }

lemma Rewrites.toCFGRule_match {u v : List (Symbol T N)} {r : ChomskyNormalFormRule T N}
    (huv : r.Rewrites u v) :
    r.toCFGRule.Rewrites u v := by
  induction huv <;> tauto

lemma Rewrites.match_toCFGRule {u v : List (Symbol T N)} {r : ChomskyNormalFormRule T N}
    (huv : r.toCFGRule.Rewrites u v) :
    r.Rewrites u v := by
  induction huv with
  | head => cases r <;> tauto
  | cons s _ ih => exact Rewrites.cons r s ih

end ChomskyNormalFormRule

namespace ChomskyNormalFormGrammar

variable [DecidableEq T]

/-- Translation of `ChomskyNormalFormGrammar` to `ContextFreeGrammar` -/
noncomputable def toCFG (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] :
    ContextFreeGrammar T where
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
  | tail _ hp ih =>
    apply ih.trans_produces
    exact Produces.toCFG_match hp

lemma Generates.toCFG_match {u : List (Symbol T g.NT)} (hu : g.Generates u) : g.toCFG.Generates u :=
  Derives.toCFG_match hu

lemma Produces.match_toCFG {u v : List (Symbol T g.NT)} (huv : g.toCFG.Produces u v) :
    g.Produces u v := by
  rcases huv with ⟨r, hrg, huv⟩
  simp only [toCFG, List.mem_map] at hrg
  rw [List.mem_toFinset] at hrg
  obtain ⟨r', hrg', rfl⟩ := List.mem_map.1 hrg
  exact ⟨r', Finset.mem_toList.1 hrg', ChomskyNormalFormRule.Rewrites.match_toCFGRule huv⟩

lemma Derives.match_toCFG {u v : List (Symbol T g.NT)} (huv : g.toCFG.Derives u v) :
    g.Derives u v := by
  induction huv with
  | refl => rfl
  | tail _ hp ih => exact ih.trans_produces (Produces.match_toCFG hp)

lemma Generates.match_toCFG {u : List (Symbol T g.NT)} (hu : g.toCFG.Generates u) : g.Generates u :=
  Derives.match_toCFG hu

theorem toCFG_correct {u : List (Symbol T g.NT)} : g.Generates u ↔ g.toCFG.Generates u :=
  ⟨Generates.toCFG_match, Generates.match_toCFG⟩

end ChomskyNormalFormGrammar

namespace ContextFreeGrammar

/-- Translation of `ContextFreeGrammar` to `ChomskyNormalFormGrammar`, composing the individual
 translation passes -/
noncomputable def toCNF [DecidableEq T] (g : ContextFreeGrammar T) [DecidableEq g.NT]
    : ChomskyNormalFormGrammar T :=
  g.eliminateEmpty.eliminateUnitRules.restrictTerminals.restrictLength (e := instDecidableEqSum)

variable {g : ContextFreeGrammar T}

lemma newTerminalRules_terminal_output {r : ContextFreeRule T g.NT} :
    ∀ r' ∈ newTerminalRules r, ∃ t, r'.output = [Symbol.terminal t] := by
  simp only [newTerminalRules, List.mem_filterMap, forall_exists_index, and_imp]
  intro r' s hs
  split <;> intro h <;> simp only [reduceCtorEq, Option.some.injEq] at h
  rw [← h]
  simp

variable [DecidableEq g.NT] [DecidableEq T]

lemma restrictTerminals_nonUnit_output (hrₒ : ∀ r ∈ g.rules, NonUnit r.output) :
    ∀ r' ∈ g.restrictTerminals.rules, NonUnit r'.output := by
  simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule, newTerminalRules,
    List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and,
    List.mem_cons, List.mem_filterMap, forall_exists_index, and_imp]
  intro r' r hrg h
  cases h with
  | inl h =>
    revert h
    split <;> intro h <;> rw [h]
    · constructor
    · simp only
      apply rightEmbed_string_nonUnit (hrₒ _ hrg)
      assumption
  | inr h =>
    obtain ⟨s, ⟨_ₒ, hsr⟩⟩ := h
    cases s <;> simp [reduceCtorEq, Option.some.injEq] at hsr
    rw [← hsr]
    exact True.intro

lemma restrictTerminals_not_empty_output (hne : ∀ r ∈ g.rules, r.output ≠ []) :
    ∀ r' ∈ g.restrictTerminals.rules, r'.output ≠ [] := by
  simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule, newTerminalRules,
    List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and,
    List.mem_cons, List.mem_filterMap, ne_eq, forall_exists_index, and_imp]
  intro r' r hrg h'
  cases h' <;> rename_i h
  · revert h
    split <;> intro h <;> rw [h]
    · simp
    · simp only [List.map_eq_nil_iff, ne_eq]
      exact hne _ hrg
  · obtain ⟨s, ⟨_, hsr⟩⟩ := h
    cases s <;> simp [reduceCtorEq, Option.some.injEq] at hsr
    · rw [← hsr]
      simp

lemma restrictTerminals_terminal_or_nonterminals :
    ∀ r ∈ g.restrictTerminals.rules, (∃ t, r.output = [Symbol.terminal t])
      ∨ (∀ s ∈ r.output, ∃ nt, s = Symbol.nonterminal nt) := by
  simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule, List.mem_toFinset,
    List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and, List.mem_cons,
    Sum.exists, forall_exists_index, and_imp]
  intro r' r _
  split <;> intro h
  · cases h with
    | inl hr =>
      rw [hr]
      simp
    | inr hr =>
      left
      exact newTerminalRules_terminal_output r' hr
  · cases h with
    | inl hr =>
      right
      rw [hr]
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro s hs
      cases s <;> tauto
    | inr hr =>
      left
      exact newTerminalRules_terminal_output r' hr

lemma eliminateUnitRules_not_empty_output (hne : ∀ r ∈ g.rules, r.output ≠ []) :
    ∀ r' ∈ g.eliminateUnitRules.rules, r'.output ≠ [] := by
  simp only [eliminateUnitRules, removeUnitRules, computeUnitPairRules, List.mem_toFinset,
    List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists, ne_eq,
    forall_exists_index, and_imp]
  intro r _ _ _ _ h'
  rw [← h']
  simp only [List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some,
    forall_exists_index, and_imp]
  intro _ hrg _
  split
  · intro; contradiction
  · simp only [Option.some.injEq]
    intro hr
    rw [← hr]
    simp only
    apply hne _ hrg

lemma eliminateEmpty_not_empty_output : ∀ r ∈ g.eliminateEmpty.rules, r.output ≠ [] := by
  simp only [ne_eq, eliminateEmpty]
  intro r hrg
  exact output_mem_removeNullables hrg

lemma eliminateUnitRules_output_nonUnit : ∀ r ∈ g.eliminateUnitRules.rules, NonUnit r.output := by
  simp only [eliminateUnitRules, removeUnitRules, computeUnitPairRules, List.mem_toFinset,
    List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists, forall_exists_index, and_imp]
  intro r l n₁ n₂ _ h hrl
  rw [← h] at hrl
  simp only [List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some] at hrl
  obtain ⟨_, _, _, hr⟩ := hrl
  revert hr
  split
  · simp
  · simp only [Option.some.injEq]
    intro hr
    rw [← hr]
    rename_i h
    simp only
    unfold NonUnit
    split <;> tauto

theorem toCNF_correct : g.language \ {[]} = g.toCNF.language := by
  unfold toCNF
  rw [eliminateEmpty_correct, eliminateUnitRules_correct, restrictTerminals_correct,
    restrictLength_correct (e := (id (id (id (id instDecidableEqSum)))))]
  intro r hrg
  match hrₒ : r.output with
  | [] =>
    exfalso
    exact restrictTerminals_not_empty_output (eliminateUnitRules_not_empty_output eliminateEmpty_not_empty_output) _
      hrg hrₒ
  | [Symbol.terminal _] =>
    cases r; simp only at hrₒ; rw [hrₒ]
    constructor
  | [Symbol.nonterminal _] =>
    exfalso
    apply restrictTerminals_nonUnit_output at hrg
    · rw [hrₒ] at hrg
      contradiction
    · exact eliminateUnitRules_output_nonUnit
  | _ :: _ :: _ =>
    cases r
    apply restrictTerminals_terminal_or_nonterminals at hrg
    cases hrg <;> rename_i hrg
    · obtain ⟨t, ht⟩ := hrg
      rw [ht] at hrₒ
      simp at hrₒ
    · rw [hrₒ] at hrg
      simp only [List.mem_cons, forall_eq_or_imp] at hrg
      obtain ⟨n₁, hn₁⟩ := hrg.1
      obtain ⟨n₂, hn₂⟩ := hrg.2.1
      simp only at hrₒ
      rw [hrₒ, hn₁, hn₂]
      constructor
      simp only [List.length_cons, Nat.le_add_left]
      intro s hs
      cases hs with
      | head => constructor
      | tail _ hs =>
        cases hs with
        | head => constructor
        | tail _ hs =>
          obtain ⟨_, hs⟩ := hrg.2.2 s hs
          rw [hs]
          constructor

end ContextFreeGrammar
