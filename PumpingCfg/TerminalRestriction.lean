/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.Utils
import PumpingCfg.EpsilonElimination
import PumpingCfg.UnitElimination

universe uN uT
variable {T : Type uT}

section EmbedProject

variable {N : Type uN}

/-- Intuitive embedding of symbols of the original grammar into symbols of the new grammar's type -/
def embedSymbol (s : Symbol T N) : Symbol T (N ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

/-- Intuitive embedding of strings of the original grammar into strings of the new grammar's type -/
abbrev embedString (u : List (Symbol T N)) : List (Symbol T (N ⊕ T)) := u.map embedSymbol

/-- Embedding of symbols of the original grammar into nonterminals of the new grammar -/
def rightEmbedSymbol (s : Symbol T N) : Symbol T (N ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.nonterminal (Sum.inr t)
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

/-- Embedding of strings of the original grammar into nonterminal (symbol) strings of the new
 grammar -/
abbrev rightEmbedString (w : List (Symbol T N)) := w.map rightEmbedSymbol

/-- Projection from symbols of the new grammars type into symbols of the original grammar -/
def projectSymbol (s : Symbol T (N ⊕ T)) : Symbol T N :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal (Sum.inl nt) => Symbol.nonterminal nt
  | Symbol.nonterminal (Sum.inr t) => Symbol.terminal t

/-- Projection from strings of the new grammars type into strings of the original grammar -/
def projectString (u : List (Symbol T (N ⊕ T))) : List (Symbol T N) := u.map projectSymbol

lemma embedSymbol_nonterminal_eq {nt : N} :
    embedSymbol (Symbol.nonterminal nt) = (@Symbol.nonterminal T (N ⊕ T)) (Sum.inl nt) := by
  rfl

lemma projectString_rightEmbedString_id {u : List (Symbol T N)} :
    projectString (rightEmbedString u) = u := by
  induction u with
  | nil => rfl
  | cons a =>
    simp only [rightEmbedString, projectString, List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · cases a <;> rfl
    · rwa [← List.map_map]

lemma projectString_terminals {u : List T} :
    projectString (List.map (@Symbol.terminal T (N ⊕ T)) u) = (List.map Symbol.terminal u) := by
  induction u with
  | nil => rfl
  | cons _ _ ih =>
    simp only [projectString, List.map_map, List.map_inj_left, Function.comp_apply, List.map_cons,
      List.cons.injEq] at ih ⊢
    exact ⟨rfl, ih⟩

lemma projectSymbol_nonterminal {n : N} :
    projectSymbol (@Symbol.nonterminal T (N ⊕ T) (Sum.inl n)) = Symbol.nonterminal n := rfl

lemma embedString_preserves_nonempty {u : List (Symbol T N)} (hu: u ≠ []): embedString u ≠ [] := by
  cases u <;> repeat first | contradiction | intro

lemma embedString_terminals {u : List T} :
    embedString (List.map (@Symbol.terminal T N) u) = List.map Symbol.terminal u := by
  induction u with
  | nil => rfl
  | cons => simp [embedString, embedSymbol]

lemma embedString_append {u v : List (Symbol T N)} :
  embedString (u ++ v) = embedString u ++ embedString v := List.map_append embedSymbol u v

lemma rightEmbed_string_nonUnit {u : List (Symbol T N)} (hu : ContextFreeGrammar.NonUnit u)
    (hut : ∀ t, u ≠ [Symbol.terminal t]) :
    ContextFreeGrammar.NonUnit (rightEmbedString u) := by
  match u with
  | [] => constructor
  | [Symbol.nonterminal _] => contradiction
  | [Symbol.terminal t] =>
    specialize hut t
    contradiction
  | _ :: _ :: _ => simp [List.map_cons, ContextFreeGrammar.NonUnit]

end EmbedProject

namespace ContextFreeGrammar
-- *********************************************************************************************** --
-- ********************************** Terminal Rule Restriction ********************************** --
-- *********************************************************************************************** --

section RestrictTerminals

/-- Computes rules r' : T -> t, for all terminals t occuring in `r.output`-/
def newTerminalRules {N : Type*} (r : ContextFreeRule T N) : List (ContextFreeRule T (N ⊕ T)) :=
  let terminal_rule (s : Symbol T N) : Option (ContextFreeRule T (N ⊕ T)) :=
    match s with
    | Symbol.terminal t => some (ContextFreeRule.mk (Sum.inr t) [Symbol.terminal t])
    | Symbol.nonterminal _ => none
  r.output.filterMap terminal_rule

/-- If `r.output` is a single terminal, we lift the rule to the new grammar, otherwise add new rules
 for each terminal symbol in `r.output` and right-lift the rule, i.e., replace all terminals with
 nonterminals -/
def restrictTerminalRule {N : Type*} (r : ContextFreeRule T N) : List (ContextFreeRule T (N ⊕ T)) :=
  (match r.output with
  | [Symbol.terminal t] => ContextFreeRule.mk (Sum.inl r.input) ([Symbol.terminal t])
  | _ => (ContextFreeRule.mk (Sum.inl r.input) (rightEmbedString r.output))) :: newTerminalRules r

/-- Compute all lifted rules -/
noncomputable def restrictTerminalRules {N : Type*} [DecidableEq T] [DecidableEq N]
  (l : List (ContextFreeRule T N)) : Finset (ContextFreeRule T (N ⊕ T)) :=
  (l.map restrictTerminalRule).flatten.toFinset

/-- Construct new grammar, using the lifted rules. Each rule's output is either a single terminal
 or only nonterminals -/
noncomputable def restrictTerminals (g : ContextFreeGrammar.{uN, uT} T) [DecidableEq T]
    [DecidableEq g.NT] :=
  ContextFreeGrammar.mk (g.NT ⊕ T) (Sum.inl g.initial) (restrictTerminalRules g.rules.toList)

end RestrictTerminals

-- *********************************************************************** --
-- Only If direction of the main correctness theorem of restrict_terminals --
-- *********************************************************************** --

section CorrectnessProof

variable {g : ContextFreeGrammar.{uN, uT} T}

lemma restrictTerminalRule_right_terminal_output {t : T} {r : ContextFreeRule T g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hrr : r' ∈ restrictTerminalRule r)
    (hrt : r'.input = Sum.inr t) :
    r'.output = [Symbol.terminal t] := by
  simp only [restrictTerminalRule, List.mem_cons] at hrr
  cases hrr <;> rename_i hrr
  · revert hrr
    split <;> intro h <;> rw [h] at hrt <;> simp at hrt
  · unfold newTerminalRules at hrr
    simp only [List.mem_filterMap] at hrr
    obtain ⟨s, _, hsr⟩ := hrr
    cases s <;> simp only [Option.some.injEq, reduceCtorEq] at hsr
    rw [←hsr] at hrt ⊢
    simp only [Sum.inr.injEq, List.cons.injEq, Symbol.terminal.injEq, and_true] at hrt ⊢
    exact hrt

lemma restrictTerminalRules_right_terminal_output [DecidableEq T] [DecidableEq g.NT] {t : T}
    {r : ContextFreeRule T (g.NT ⊕ T)} (hrg : r ∈ restrictTerminalRules g.rules.toList)
    (hrt : r.input = Sum.inr t) :
    r.output = [Symbol.terminal t] := by
  simp only [restrictTerminalRules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, exists_exists_and_eq_and] at hrg
  obtain ⟨_, _, hr⟩ := hrg
  exact restrictTerminalRule_right_terminal_output hr hrt

lemma restrictTerminalRule_left {n : g.NT} {r : ContextFreeRule T g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hrr : r' ∈ restrictTerminalRule r)
    (hrn : r'.input = Sum.inl n) :
    r.input = n ∧ r.output = projectString r'.output := by
  simp only [restrictTerminalRule, List.mem_cons] at hrr
  cases hrr <;> rename_i hrr
  · revert hrr
    split <;> intro hrr <;> rw [hrr] at hrn ⊢ <;> simp only [Sum.inl.injEq] at hrn ⊢
    · rename_i hrt
      simp only [projectString, projectSymbol, List.map_cons, List.map_nil]
      exact ⟨hrn, hrt⟩
    · rw [projectString_rightEmbedString_id]
      exact ⟨hrn, rfl⟩
  · simp only [newTerminalRules, List.mem_filterMap] at hrr
    obtain ⟨r'', _, hrr⟩ := hrr
    cases r'' <;> simp only [Option.some.injEq, reduceCtorEq] at hrr
    rw [← hrr] at hrn
    contradiction

variable [DecidableEq T] [eq : DecidableEq g.NT]

lemma restrictTerminalsRules_left {n : g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hrg : r' ∈ restrictTerminalRules g.rules.toList)
    (hrn : r'.input = Sum.inl n) :
    ∃ r ∈ g.rules, r.input = n ∧ r.output = projectString r'.output := by
  unfold restrictTerminalRules at hrg
  simp only [restrictTerminalRules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, exists_exists_and_eq_and] at hrg
  obtain ⟨r, hrg, hrr⟩ := hrg
  exact ⟨r, hrg, restrictTerminalRule_left hrr hrn⟩

lemma restrictTerminals_produces_derives_projectString {u v : List (Symbol T (g.NT ⊕ T))}
    (huv : (restrictTerminals g).Produces u v) :
    g.Derives (projectString u) (projectString v) := by
  obtain ⟨r', hrg', huv⟩ := huv
  obtain ⟨_, _, hu, hv⟩ := huv.exists_parts
  cases h : r'.input with
  | inl =>
    obtain ⟨r, hrg, hrᵢ, hrₒ⟩ := restrictTerminalsRules_left hrg' h
    rw [hu, hv, h]
    unfold projectString at hrₒ ⊢
    repeat rw [List.map_append]
    apply Produces.single
    apply Produces.append_right
    apply Produces.append_left
    use r
    constructor
    · exact hrg
    · rw [← hrₒ, ← hrᵢ]
      simp only [projectSymbol, List.map_cons, List.map_nil]
      exact ContextFreeRule.Rewrites.input_output
  | inr =>
    rw [hu, hv, h, restrictTerminalRules_right_terminal_output hrg' h]
    simp [projectString, projectSymbol, List.append_assoc, List.singleton_append,
      List.map_append, List.map_cons]
    rfl

lemma restrictTerminals_derives_derives_projectString {u v : List (Symbol T (g.NT ⊕ T))}
    (huv : (restrictTerminals g).Derives u v) :
    g.Derives (projectString u) (projectString v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih => exact Derives.trans (restrictTerminals_produces_derives_projectString hp) ih

-- ****************************************************************** --
-- If direction of the main correctness theorem of restrict_terminals --
-- ****************************************************************** --

omit [DecidableEq T] [DecidableEq g.NT] in
lemma terminal_mem_newTerminalRules {t : T} {r : ContextFreeRule T g.NT}
    (htr : (Symbol.terminal t) ∈ r.output) :
    ContextFreeRule.mk (Sum.inr t) ([Symbol.terminal t]) ∈ newTerminalRules r := by
  rw [newTerminalRules, List.mem_filterMap]
  use (Symbol.terminal t)

lemma restrictTerminals_derives_rightEmbedString_embedString {u : List (Symbol T g.NT)}
    (hu : ∀ t, (Symbol.terminal t) ∈ u → ∃ r ∈ g.rules, (Symbol.terminal t) ∈ r.output) :
    (restrictTerminals g).Derives (rightEmbedString u) (embedString u) := by
  induction u with
  | nil => rfl
  | cons a _ ih =>
    simp only [List.mem_cons, List.map_cons] at hu ⊢
    rw [←List.singleton_append, ← @List.singleton_append _ (embedSymbol a)]
    apply Derives.append_left_trans
    · apply ih
      intro t h'
      exact hu t (Or.inr h')
    · cases a with
      | nonterminal => rfl
      | terminal t =>
        specialize hu t
        simp only [true_or, forall_const] at hu
        obtain ⟨r, hrg, htr⟩ := hu
        apply Produces.single
        constructor
        constructor
        · apply List.subset_def.1; swap
          · exact terminal_mem_newTerminalRules htr
          · simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule]
            intro r' hrr
            simp only [List.mem_dedup, List.mem_flatten, List.mem_map, Finset.mem_toList,
              exists_exists_and_eq_and]
            exact ⟨r, hrg, by right; exact hrr⟩
        · unfold rightEmbedSymbol embedSymbol
          exact ContextFreeRule.Rewrites.input_output

lemma derives_restrictTerminals_derives_embedString {u v : List (Symbol T g.NT)} (huv : g.Derives u v) :
    (restrictTerminals g).Derives (embedString u) (embedString v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    obtain ⟨r, hrg, hr⟩ := hp
    apply Derives.trans _ ih
    obtain ⟨_,_,heq₁,heq₂⟩ := hr.exists_parts
    rw [heq₁, heq₂]
    repeat rw [embedString_append]
    apply Derives.append_right
    apply Derives.append_left
    by_cases hrt : ∃ t, r.output = [Symbol.terminal t]
    · obtain ⟨t,hrt⟩ := hrt
      apply Produces.single
      use ContextFreeRule.mk (Sum.inl r.input) [Symbol.terminal t]
      constructor
      · unfold restrictTerminals restrictTerminalRules restrictTerminalRule
        simp only [List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList,
          exists_exists_and_eq_and, List.mem_cons]
        use r
        constructor
        · exact hrg
        · rw [hrt]
          simp
      · rw [hrt]
        simp only [List.map_cons, List.map_nil]
        exact ContextFreeRule.Rewrites.input_output
    · apply Produces.trans_derives
      · use ContextFreeRule.mk (Sum.inl r.input) (rightEmbedString r.output)
        constructor
        · simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule,
            List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList,
            exists_exists_and_eq_and, List.mem_cons]
          use r
          constructor
          · exact hrg
          · split <;> rename_i heq
            · rename_i t'
              exfalso
              apply hrt
              use t'
            · simp
        · unfold embedString embedSymbol
          simp only [List.map_cons, List.map_nil]
          exact ContextFreeRule.Rewrites.input_output
      · apply restrictTerminals_derives_rightEmbedString_embedString
        intros t ht
        use r

theorem restrictTerminals_correct : g.language = g.restrictTerminals.language := by
  apply Set.eq_of_subset_of_subset
  · intro w h
    simp only [language, Set.mem_setOf_eq] at h ⊢
    unfold Generates at h ⊢
    apply derives_restrictTerminals_derives_embedString at h
    rw [embedString_terminals] at h
    unfold embedString at h
    unfold restrictTerminals
    simp [List.map_cons, List.map_nil] at h ⊢
    exact h
  · intro w h
    simp only [language, Set.mem_setOf_eq] at h ⊢
    unfold Generates at h ⊢
    apply restrictTerminals_derives_derives_projectString at h
    rw [projectString_terminals] at h
    unfold restrictTerminals projectString at h
    simp only [List.map_cons, List.map_nil] at h
    rw [projectSymbol_nonterminal] at h
    exact h

end CorrectnessProof

end ContextFreeGrammar
