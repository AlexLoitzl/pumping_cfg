/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.EpsilonElimination
import PumpingCfg.UnitElimination

universe uN uT
variable {T : Type uT}
namespace ContextFreeGrammar

-- theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
--   {u : List (Symbol T g.NT)} (h : g.Derives u v)
--   (refl : P v (Derives.refl v))
--   (step : ∀ {u w} (h' : g.Produces u w) (h : g.Derives w v), P w h → P u (h.head h')) : P u h :=
--   Relation.ReflTransGen.head_induction_on h refl step

end ContextFreeGrammar

section EmbedProject

variable {NT : Type uN}

def embed_symbol (s : Symbol T NT) : Symbol T (NT ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

abbrev embed_string (u : List (Symbol T NT)) : List (Symbol T (NT ⊕ T)) := u.map embed_symbol

def right_embed_symbol (s : Symbol T NT) : Symbol T (NT ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.nonterminal (Sum.inr t)
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

abbrev right_embed_string (w : List (Symbol T NT)) := w.map right_embed_symbol

def project_symbol (s : Symbol T (NT ⊕ T)) : Symbol T NT :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal (Sum.inl nt) => Symbol.nonterminal nt
  | Symbol.nonterminal (Sum.inr t) => Symbol.terminal t

def project_string (w : List (Symbol T (NT ⊕ T))) : List (Symbol T NT) := w.map project_symbol

lemma embed_nonterminal_eq {nt : NT} :
    embed_symbol (Symbol.nonterminal nt) = (@Symbol.nonterminal T (NT ⊕ T)) (Sum.inl nt) := by
  unfold embed_symbol
  rfl

lemma project_right_project_eq {w : List (Symbol T NT)} :
    project_string (right_embed_string w) = w := by
  induction w with
  | nil => rfl
  | cons hd tl ih =>
    unfold right_embed_string project_string at *
    simp
    constructor
    · unfold project_symbol right_embed_symbol
      cases hd <;> rfl
    · simp at ih
      exact ih

lemma project_string_terminals {w : List T} :
    project_string (List.map (@Symbol.terminal T (NT ⊕ T)) w) = (List.map Symbol.terminal w) := by
  induction w with
  | nil => rfl
  | cons hd tl ih =>
    unfold project_string at ih ⊢
    simp at ih ⊢
    constructor
    · unfold project_symbol
      rfl
    · exact ih

lemma project_symbol_nonterminal {nt : NT} :
    project_symbol (@Symbol.nonterminal T (NT ⊕ T) (Sum.inl nt)) = Symbol.nonterminal nt := by
  unfold project_symbol
  rfl

lemma embed_string_nonempty {w : List (Symbol T NT)} (h: w ≠ []): embed_string w ≠ [] := by
  cases w
  contradiction
  intro
  contradiction

lemma embed_string_terminals {w : List T} :
    embed_string (List.map (@Symbol.terminal T NT) w) = List.map Symbol.terminal w := by
  induction w with
  | nil => rfl
  | cons =>
    unfold embed_string embed_symbol
    simp

lemma embed_string_append {u v : List (Symbol T NT)} :
  embed_string (u ++ v) = embed_string u ++ embed_string v := List.map_append embed_symbol u v

lemma right_embed_string_nonUnit {u : List (Symbol T NT)} (h : ContextFreeGrammar.NonUnit u)
    (h' : ∀ t, u ≠ [Symbol.terminal t]) :
    ContextFreeGrammar.NonUnit (right_embed_string u) := by
  match u with
  | [] => constructor
  | [Symbol.nonterminal _] => contradiction
  | [Symbol.terminal t] =>
    specialize h' t
    contradiction
  | _ :: _ :: _ =>
    simp
    unfold ContextFreeGrammar.NonUnit
    simp

end EmbedProject

namespace ContextFreeGrammar
-- *********************************************************************************************** --
-- ********************************** Terminal Rule Restriction ********************************** --
-- *********************************************************************************************** --

section RestrictTerminals

def new_terminal_rules {NT : Type*} (r : ContextFreeRule T NT) : List (ContextFreeRule T (NT ⊕ T)) :=
  let terminal_rule (s : Symbol T NT) : Option (ContextFreeRule T (NT ⊕ T)) :=
    match s with
    | Symbol.terminal t => some (ContextFreeRule.mk (Sum.inr t) [Symbol.terminal t])
    | Symbol.nonterminal _ => none
  r.output.filterMap terminal_rule

def restrict_terminal_rule {NT : Type*} (r : ContextFreeRule T NT) : List (ContextFreeRule T (NT ⊕ T)) :=
  (match r.output with
  | [Symbol.terminal t] => ContextFreeRule.mk (Sum.inl r.input) ([Symbol.terminal t])
  | _ => (ContextFreeRule.mk (Sum.inl r.input) (right_embed_string r.output))) :: new_terminal_rules r

noncomputable def restrict_terminal_rules {NT : Type*} [DecidableEq T] [DecidableEq NT]
  (rs : List (ContextFreeRule T NT)) : Finset (ContextFreeRule T (NT ⊕ T)) :=
  (rs.map restrict_terminal_rule).flatten.toFinset

noncomputable def restrict_terminals (g : ContextFreeGrammar.{uN, uT} T) [DecidableEq T] [DecidableEq g.NT] :=
  ContextFreeGrammar.mk (g.NT ⊕ T) (Sum.inl g.initial) (restrict_terminal_rules g.rules.toList)

end RestrictTerminals

-- *********************************************************************** --
-- Only If direction of the main correctness theorem of restrict_terminals --
-- *********************************************************************** --

section CorrectnessProof

variable {g : ContextFreeGrammar.{uN, uT} T}

lemma restrict_terminal_rule_right {t : T} {r : ContextFreeRule T g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hmem : r' ∈ restrict_terminal_rule r)
    (heq : r'.input = Sum.inr t) :
    r'.output = [Symbol.terminal t] := by
  unfold restrict_terminal_rule at hmem
  simp at hmem
  cases hmem <;> rename_i hmem
  · revert hmem
    split <;> intro h <;> rw [h] at heq <;> simp at heq
  · unfold new_terminal_rules at hmem
    simp at hmem
    obtain ⟨s, hsin, h⟩ := hmem
    cases s <;> simp at h
    rw [←h] at heq ⊢
    simp at heq ⊢
    exact heq

lemma restrict_terminals_rule_right [DecidableEq T] [DecidableEq g.NT] {t : T}
    {r : ContextFreeRule T (g.NT ⊕ T)} (hmem : r ∈ restrict_terminal_rules g.rules.toList)
    (heq : r.input = Sum.inr t) :
    r.output = [Symbol.terminal t] := by
  unfold restrict_terminal_rules at hmem
  simp at hmem
  obtain ⟨r, _, h⟩ := hmem
  exact restrict_terminal_rule_right h heq

lemma restrict_terminal_rule_left {nt : g.NT} {r : ContextFreeRule T g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hmem : r' ∈ restrict_terminal_rule r)
    (heq : r'.input = Sum.inl nt) :
    r.input = nt ∧ r.output = project_string r'.output := by
  unfold restrict_terminal_rule at hmem
  simp at hmem
  cases hmem <;> rename_i hmem
  · revert hmem
    split <;> intro hmem <;> rw [hmem] at heq ⊢ <;> simp at heq ⊢
    · rename_i heq'
      constructor
      exact heq
      unfold project_string project_symbol
      simp
      exact heq'
    · constructor
      exact heq
      rw [project_right_project_eq]
  · unfold new_terminal_rules at hmem
    simp at hmem
    obtain ⟨r'', hrin, h⟩ := hmem
    cases r'' <;> simp at h
    rw [← h] at heq
    simp at heq

variable [DecidableEq T] [DecidableEq g.NT]

lemma restrict_terminals_rules_left {nt : g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hmem : r' ∈ restrict_terminal_rules g.rules.toList)
    (heq : r'.input = Sum.inl nt) :
    ∃ r ∈ g.rules, r.input = nt ∧ r.output = project_string r'.output := by
  unfold restrict_terminal_rules at hmem
  simp at hmem
  obtain ⟨r, hrin, hr⟩ := hmem
  apply restrict_terminal_rule_left at hr
  use r
  constructor
  exact hrin
  exact hr heq

lemma restrict_terminals_produces_derives {u v : List (Symbol T (g.NT ⊕ T))}
    (huv : (restrict_terminals g).Produces u v) :
    g.Derives (project_string u) (project_string v) := by
  obtain ⟨r', hrin', hr'⟩ := huv
  obtain ⟨p, q, hu', hv'⟩ := hr'.exists_parts
  cases h : r'.input with
  | inl nt =>
    obtain ⟨r, hrin, hri, hro⟩ := restrict_terminals_rules_left hrin' h
    rw [hu', hv', h]
    unfold project_string at hro ⊢
    repeat rw [List.map_append]
    apply Produces.single
    apply Produces.append_right
    apply Produces.append_left
    use r
    constructor
    · exact hrin
    · rw [← hro]
      unfold project_symbol
      simp
      rw [←hri]
      exact ContextFreeRule.Rewrites.input_output
  | inr t =>
    rw [hu', hv', h]
    rw [restrict_terminals_rule_right hrin' h]
    unfold project_string project_symbol
    simp
    rfl

lemma restrict_terminals_implies {u v : List (Symbol T (g.NT ⊕ T))}
    (huv : (restrict_terminals g).Derives u v) :
    g.Derives (project_string u) (project_string v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | step hp _ ih =>
    exact Derives.trans (restrict_terminals_produces_derives hp) ih

-- ****************************************************************** --
-- If direction of the main correctness theorem of restrict_terminals --
-- ****************************************************************** --

omit [DecidableEq T] [DecidableEq g.NT] in
lemma new_terminal_rules_in {t : T} {r : ContextFreeRule T g.NT}
    (hmem : (Symbol.terminal t) ∈ r.output) :
    ContextFreeRule.mk (Sum.inr t) ([Symbol.terminal t]) ∈ new_terminal_rules r := by
  unfold new_terminal_rules
  simp
  use (Symbol.terminal t)

lemma restrict_terminals_right_embed_derives {u : List (Symbol T g.NT)}
    (h : ∀ t, (Symbol.terminal t) ∈ u → ∃ r ∈ g.rules, (Symbol.terminal t) ∈ r.output) :
    (restrict_terminals g).Derives (right_embed_string u) (embed_string u) := by
  induction u with
  | nil => rfl
  | cons hd tl ih =>
    simp at h ⊢
    rw [←List.singleton_append, ← @List.singleton_append _ (embed_symbol hd)]
    apply Derives.append_left_trans
    · apply ih
      intro  t h'
      apply h
      right
      exact h'
    · cases hd with
      | nonterminal =>
        unfold embed_symbol right_embed_symbol
        rfl
      | terminal t =>
        specialize h t
        simp at h
        obtain ⟨r, hrin, hr⟩ := h
        apply Produces.single
        use (ContextFreeRule.mk (Sum.inr t) ([Symbol.terminal t]))
        constructor
        · apply List.subset_def.1; swap
          · apply new_terminal_rules_in
            exact hr
          · unfold restrict_terminals restrict_terminal_rules restrict_terminal_rule
            simp
            intro r' hrin'
            simp
            use r
            constructor
            · exact hrin
            · right
              exact hrin'
        · unfold right_embed_symbol embed_symbol
          simp
          exact ContextFreeRule.Rewrites.input_output

lemma implies_restrict_terminals {u v : List (Symbol T g.NT)} (huv : g.Derives u v) :
    (restrict_terminals g).Derives (embed_string u) (embed_string v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | @step u w hp _ ih =>
    obtain ⟨r, hrin, hr⟩ := hp
    apply Derives.trans _ ih
    obtain ⟨p,q,hu,hw⟩ := hr.exists_parts
    rw [hu, hw]
    repeat rw [embed_string_append]
    apply Derives.append_right
    apply Derives.append_left
    by_cases h' : ∃ t, r.output = [Symbol.terminal t]
    · obtain ⟨t,ht⟩ := h'
      apply Produces.single
      use ContextFreeRule.mk (Sum.inl r.input) [Symbol.terminal t]
      constructor
      · unfold restrict_terminals restrict_terminal_rules restrict_terminal_rule
        simp
        use r
        constructor
        · exact hrin
        · rw [ht]
          simp
      · unfold embed_string embed_symbol
        rw [ht]
        simp
        exact ContextFreeRule.Rewrites.input_output
    · apply Produces.trans_derives
      · use ContextFreeRule.mk (Sum.inl r.input) (right_embed_string r.output)
        constructor
        · unfold restrict_terminals restrict_terminal_rules restrict_terminal_rule
          simp
          use r
          constructor
          · exact hrin
          · split <;> rename_i heq
            · rename_i t'
              exfalso
              apply h'
              use t'
            · simp
        · unfold embed_string embed_symbol
          simp
          exact ContextFreeRule.Rewrites.input_output
      · apply restrict_terminals_right_embed_derives
        intros t ht
        use r

theorem restrict_terminals_correct : g.language = g.restrict_terminals.language := by
  unfold language
  apply Set.eq_of_subset_of_subset
  · intro w h
    simp at h ⊢
    unfold Generates at h ⊢
    apply implies_restrict_terminals at h
    rw [embed_string_terminals] at h
    unfold embed_string at h
    unfold restrict_terminals
    simp at h ⊢
    exact h
  · intro w h
    simp at h ⊢
    unfold Generates at h ⊢
    apply restrict_terminals_implies at h
    rw [project_string_terminals] at h
    unfold restrict_terminals project_string at h
    simp at h
    rw [project_symbol_nonterminal] at h
    exact h

end CorrectnessProof

end ContextFreeGrammar
