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

def embed_symbol (s : Symbol T N) : Symbol T (N ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

abbrev embed_string (u : List (Symbol T N)) : List (Symbol T (N ⊕ T)) := u.map embed_symbol

def right_embed_symbol (s : Symbol T N) : Symbol T (N ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.nonterminal (Sum.inr t)
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

abbrev right_embed_string (w : List (Symbol T N)) := w.map right_embed_symbol

def project_symbol (s : Symbol T (N ⊕ T)) : Symbol T N :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal (Sum.inl nt) => Symbol.nonterminal nt
  | Symbol.nonterminal (Sum.inr t) => Symbol.terminal t

def project_string (u : List (Symbol T (N ⊕ T))) : List (Symbol T N) := u.map project_symbol

lemma embed_nonterminal_eq {nt : N} :
    embed_symbol (Symbol.nonterminal nt) = (@Symbol.nonterminal T (N ⊕ T)) (Sum.inl nt) := by
  rfl

lemma project_right_project_eq {u : List (Symbol T N)} :
    project_string (right_embed_string u) = u := by
  induction u with
  | nil => rfl
  | cons a =>
    simp only [right_embed_string, project_string, List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · cases a <;> rfl
    · rwa [← List.map_map]

lemma project_string_terminals {u : List T} :
    project_string (List.map (@Symbol.terminal T (N ⊕ T)) u) = (List.map Symbol.terminal u) := by
  induction u with
  | nil => rfl
  | cons _ _ ih =>
    simp only [project_string, List.map_map, List.map_inj_left, Function.comp_apply, List.map_cons,
      List.cons.injEq] at ih ⊢
    exact ⟨rfl, ih⟩

lemma project_symbol_nonterminal {n : N} :
    project_symbol (@Symbol.nonterminal T (N ⊕ T) (Sum.inl n)) = Symbol.nonterminal n := rfl

lemma embed_string_nonempty {u : List (Symbol T N)} (hu: u ≠ []): embed_string u ≠ [] := by
  cases u <;> repeat first | contradiction | intro

lemma embed_string_terminals {u : List T} :
    embed_string (List.map (@Symbol.terminal T N) u) = List.map Symbol.terminal u := by
  induction u with
  | nil => rfl
  | cons => simp [embed_string, embed_symbol]

lemma embed_string_append {u v : List (Symbol T N)} :
  embed_string (u ++ v) = embed_string u ++ embed_string v := List.map_append embed_symbol u v

lemma right_embed_string_nonUnit {u : List (Symbol T N)} (hu : ContextFreeGrammar.NonUnit u)
    (hut : ∀ t, u ≠ [Symbol.terminal t]) :
    ContextFreeGrammar.NonUnit (right_embed_string u) := by
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

def new_terminal_rules {N : Type*} (r : ContextFreeRule T N) : List (ContextFreeRule T (N ⊕ T)) :=
  let terminal_rule (s : Symbol T N) : Option (ContextFreeRule T (N ⊕ T)) :=
    match s with
    | Symbol.terminal t => some (ContextFreeRule.mk (Sum.inr t) [Symbol.terminal t])
    | Symbol.nonterminal _ => none
  r.output.filterMap terminal_rule

def restrict_terminal_rule {N : Type*} (r : ContextFreeRule T N) : List (ContextFreeRule T (N ⊕ T)) :=
  (match r.output with
  | [Symbol.terminal t] => ContextFreeRule.mk (Sum.inl r.input) ([Symbol.terminal t])
  | _ => (ContextFreeRule.mk (Sum.inl r.input) (right_embed_string r.output))) :: new_terminal_rules r

noncomputable def restrict_terminal_rules {N : Type*} [DecidableEq T] [DecidableEq N]
  (l : List (ContextFreeRule T N)) : Finset (ContextFreeRule T (N ⊕ T)) :=
  (l.map restrict_terminal_rule).flatten.toFinset

noncomputable def restrict_terminals (g : ContextFreeGrammar.{uN, uT} T) [DecidableEq T]
    [DecidableEq g.NT] :=
  ContextFreeGrammar.mk (g.NT ⊕ T) (Sum.inl g.initial) (restrict_terminal_rules g.rules.toList)

end RestrictTerminals

-- *********************************************************************** --
-- Only If direction of the main correctness theorem of restrict_terminals --
-- *********************************************************************** --

section CorrectnessProof

variable {g : ContextFreeGrammar.{uN, uT} T}

lemma restrict_terminal_rule_right {t : T} {r : ContextFreeRule T g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hrr : r' ∈ restrict_terminal_rule r)
    (hrt : r'.input = Sum.inr t) :
    r'.output = [Symbol.terminal t] := by
  simp only [restrict_terminal_rule, List.mem_cons] at hrr
  cases hrr <;> rename_i hrr
  · revert hrr
    split <;> intro h <;> rw [h] at hrt <;> simp at hrt
  · unfold new_terminal_rules at hrr
    simp only [List.mem_filterMap] at hrr
    obtain ⟨s, _, hsr⟩ := hrr
    cases s <;> simp only [Option.some.injEq, reduceCtorEq] at hsr
    rw [←hsr] at hrt ⊢
    simp only [Sum.inr.injEq, List.cons.injEq, Symbol.terminal.injEq, and_true] at hrt ⊢
    exact hrt

lemma restrict_terminals_rule_right [DecidableEq T] [DecidableEq g.NT] {t : T}
    {r : ContextFreeRule T (g.NT ⊕ T)} (hrg : r ∈ restrict_terminal_rules g.rules.toList)
    (hrt : r.input = Sum.inr t) :
    r.output = [Symbol.terminal t] := by
  simp only [restrict_terminal_rules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, exists_exists_and_eq_and] at hrg
  obtain ⟨_, _, hr⟩ := hrg
  exact restrict_terminal_rule_right hr hrt

lemma restrict_terminal_rule_left {n : g.NT} {r : ContextFreeRule T g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hrr : r' ∈ restrict_terminal_rule r)
    (hrn : r'.input = Sum.inl n) :
    r.input = n ∧ r.output = project_string r'.output := by
  simp only [restrict_terminal_rule, List.mem_cons] at hrr
  cases hrr <;> rename_i hrr
  · revert hrr
    split <;> intro hrr <;> rw [hrr] at hrn ⊢ <;> simp only [Sum.inl.injEq] at hrn ⊢
    · rename_i hrt
      simp only [project_string, project_symbol, List.map_cons, List.map_nil]
      exact ⟨hrn, hrt⟩
    · rw [project_right_project_eq]
      exact ⟨hrn, rfl⟩
  · simp only [new_terminal_rules, List.mem_filterMap] at hrr
    obtain ⟨r'', _, hrr⟩ := hrr
    cases r'' <;> simp only [Option.some.injEq, reduceCtorEq] at hrr
    rw [← hrr] at hrn
    contradiction

variable [DecidableEq T] [eq : DecidableEq g.NT]

lemma restrict_terminals_rules_left {n : g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hrg : r' ∈ restrict_terminal_rules g.rules.toList)
    (hrn : r'.input = Sum.inl n) :
    ∃ r ∈ g.rules, r.input = n ∧ r.output = project_string r'.output := by
  unfold restrict_terminal_rules at hrg
  simp only [restrict_terminal_rules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, exists_exists_and_eq_and] at hrg
  obtain ⟨r, hrg, hrr⟩ := hrg
  exact ⟨r, hrg, restrict_terminal_rule_left hrr hrn⟩

lemma restrict_terminals_produces_derives {u v : List (Symbol T (g.NT ⊕ T))}
    (huv : (restrict_terminals g).Produces u v) :
    g.Derives (project_string u) (project_string v) := by
  obtain ⟨r', hrg', huv⟩ := huv
  obtain ⟨_, _, hu, hv⟩ := huv.exists_parts
  cases h : r'.input with
  | inl =>
    obtain ⟨r, hrg, hrᵢ, hrₒ⟩ := restrict_terminals_rules_left hrg' h
    rw [hu, hv, h]
    unfold project_string at hrₒ ⊢
    repeat rw [List.map_append]
    apply Produces.single
    apply Produces.append_right
    apply Produces.append_left
    use r
    constructor
    · exact hrg
    · rw [← hrₒ, ← hrᵢ]
      simp only [project_symbol, List.map_cons, List.map_nil]
      exact ContextFreeRule.Rewrites.input_output
  | inr =>
    rw [hu, hv, h, restrict_terminals_rule_right hrg' h]
    simp [project_string, project_symbol, List.append_assoc, List.singleton_append,
      List.map_append, List.map_cons]
    rfl

lemma restrict_terminals_implies {u v : List (Symbol T (g.NT ⊕ T))}
    (huv : (restrict_terminals g).Derives u v) :
    g.Derives (project_string u) (project_string v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih => exact Derives.trans (restrict_terminals_produces_derives hp) ih

-- ****************************************************************** --
-- If direction of the main correctness theorem of restrict_terminals --
-- ****************************************************************** --

omit [DecidableEq T] [DecidableEq g.NT] in
lemma new_terminal_rules_in {t : T} {r : ContextFreeRule T g.NT}
    (htr : (Symbol.terminal t) ∈ r.output) :
    ContextFreeRule.mk (Sum.inr t) ([Symbol.terminal t]) ∈ new_terminal_rules r := by
  rw [new_terminal_rules, List.mem_filterMap]
  use (Symbol.terminal t)

lemma restrict_terminals_right_embed_derives {u : List (Symbol T g.NT)}
    (hu : ∀ t, (Symbol.terminal t) ∈ u → ∃ r ∈ g.rules, (Symbol.terminal t) ∈ r.output) :
    (restrict_terminals g).Derives (right_embed_string u) (embed_string u) := by
  induction u with
  | nil => rfl
  | cons a _ ih =>
    simp only [List.mem_cons, List.map_cons] at hu ⊢
    rw [←List.singleton_append, ← @List.singleton_append _ (embed_symbol a)]
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
          · exact new_terminal_rules_in htr
          · simp only [restrict_terminals, restrict_terminal_rules, restrict_terminal_rule]
            intro r' hrr
            simp only [List.mem_dedup, List.mem_flatten, List.mem_map, Finset.mem_toList,
              exists_exists_and_eq_and]
            exact ⟨r, hrg, by right; exact hrr⟩
        · unfold right_embed_symbol embed_symbol
          exact ContextFreeRule.Rewrites.input_output

lemma implies_restrict_terminals {u v : List (Symbol T g.NT)} (huv : g.Derives u v) :
    (restrict_terminals g).Derives (embed_string u) (embed_string v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    obtain ⟨r, hrg, hr⟩ := hp
    apply Derives.trans _ ih
    obtain ⟨_,_,heq₁,heq₂⟩ := hr.exists_parts
    rw [heq₁, heq₂]
    repeat rw [embed_string_append]
    apply Derives.append_right
    apply Derives.append_left
    by_cases hrt : ∃ t, r.output = [Symbol.terminal t]
    · obtain ⟨t,hrt⟩ := hrt
      apply Produces.single
      use ContextFreeRule.mk (Sum.inl r.input) [Symbol.terminal t]
      constructor
      · unfold restrict_terminals restrict_terminal_rules restrict_terminal_rule
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
      · use ContextFreeRule.mk (Sum.inl r.input) (right_embed_string r.output)
        constructor
        · simp only [restrict_terminals, restrict_terminal_rules, restrict_terminal_rule,
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
        · unfold embed_string embed_symbol
          simp only [List.map_cons, List.map_nil]
          exact ContextFreeRule.Rewrites.input_output
      · apply restrict_terminals_right_embed_derives
        intros t ht
        use r

theorem restrict_terminals_correct : g.language = g.restrict_terminals.language := by
  apply Set.eq_of_subset_of_subset
  · intro w h
    simp only [language, Set.mem_setOf_eq] at h ⊢
    unfold Generates at h ⊢
    apply implies_restrict_terminals at h
    rw [embed_string_terminals] at h
    unfold embed_string at h
    unfold restrict_terminals
    simp [List.map_cons, List.map_nil] at h ⊢
    exact h
  · intro w h
    simp only [language, Set.mem_setOf_eq] at h ⊢
    unfold Generates at h ⊢
    apply restrict_terminals_implies at h
    rw [project_string_terminals] at h
    unfold restrict_terminals project_string at h
    simp only [List.map_cons, List.map_nil] at h
    rw [project_symbol_nonterminal] at h
    exact h

end CorrectnessProof

end ContextFreeGrammar
