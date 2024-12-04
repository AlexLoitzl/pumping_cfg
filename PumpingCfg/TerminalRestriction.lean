/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.EpsilonElimination
import PumpingCfg.UnitElimination

variable {T : Type}
namespace ContextFreeGrammar

-- General Props of `Derives`
section Stuff

variable {T : Type}
variable {g : ContextFreeGrammar T}

-- theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
--   {u : List (Symbol T g.NT)} (h : g.Derives u v)
--   (refl : P v (Derives.refl v))
--   (step : ∀ {u w} (h' : g.Produces u w) (h : g.Derives w v), P w h → P u (h.head h')) : P u h :=
--   Relation.ReflTransGen.head_induction_on h refl step

lemma rewrites_rule {r : ContextFreeRule T g.NT} : r.Rewrites [Symbol.nonterminal r.input] r.output := by
  rw [← r.output.append_nil, ← r.output.nil_append]
  rw [← [Symbol.nonterminal r.input].append_nil, ← [Symbol.nonterminal r.input].nil_append]
  exact r.rewrites_of_exists_parts [] []

lemma derives_exists_rule {s : Symbol T g.NT} {u v : List (Symbol T g.NT)} (h : g.Derives u v) (hnin : s ∉ u)
  (hin : s ∈ v) :
  ∃ r ∈ g.rules, s ∈ r.output := by
  induction h using Derives.head_induction_on with
  | refl => contradiction
  | @step u w hp _ ih =>
    obtain ⟨r, hrin, hr⟩ := hp
    obtain ⟨p,q,hp,hq⟩ := hr.exists_parts
    by_cases h : s ∈ r.output
    · use r
    · apply ih
      rw [hq]
      rw [hp] at hnin
      simp at hnin ⊢
      exact ⟨hnin.1, h, hnin.2.2⟩

end Stuff

end ContextFreeGrammar
-- TODO Name this embedd and project
section Lifts

variable {NT : Type}

def lift_symbol (s : Symbol T NT) : Symbol T (NT ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

abbrev lift_string (w : List (Symbol T NT)) : List (Symbol T (NT ⊕ T)) := w.map lift_symbol

def right_lift_symbol (s : Symbol T NT) : Symbol T (NT ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.nonterminal (Sum.inr t)
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

abbrev right_lift_string (w : List (Symbol T NT)) : List (Symbol T (NT ⊕ T)) := w.map right_lift_symbol

def unlift_symbol (s : Symbol T (NT ⊕ T)) : Symbol T NT :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal (Sum.inl nt) => Symbol.nonterminal nt
  | Symbol.nonterminal (Sum.inr t) => Symbol.terminal t

def unlift_string (w : List (Symbol T (NT ⊕ T))) : List (Symbol T NT) := w.map unlift_symbol

lemma lift_nonterminal_eq {nt : NT} :
  lift_symbol (Symbol.nonterminal nt) = (@Symbol.nonterminal T (NT ⊕ T)) (Sum.inl nt) := by
  unfold lift_symbol
  rfl

lemma unlift_right_lift_eq {w : List (Symbol T NT)} : unlift_string (right_lift_string w) = w := by
  induction w with
  | nil => rfl
  | cons hd tl ih =>
    unfold right_lift_string unlift_string at *
    simp
    constructor
    · unfold unlift_symbol right_lift_symbol
      cases hd <;> rfl
    · simp at ih
      exact ih

lemma unlift_string_terminals {w : List T} :
  unlift_string (List.map (@Symbol.terminal T (NT ⊕ T)) w) = (List.map (@Symbol.terminal T NT) w) := by
  induction w with
  | nil => rfl
  | cons hd tl ih =>
    unfold unlift_string at ih ⊢
    simp at ih ⊢
    constructor
    · unfold unlift_symbol
      rfl
    · exact ih

lemma unlift_symbol_nonterminal {nt : NT} :
  unlift_symbol (@Symbol.nonterminal T (NT ⊕ T) (Sum.inl nt)) = Symbol.nonterminal nt := by
  unfold unlift_symbol
  rfl

lemma lift_string_nonempty {w : List (Symbol T NT)} (h: w ≠ []): lift_string w ≠ [] := by
  cases w
  contradiction
  intro
  contradiction

lemma lift_string_terminals {w : List T} : lift_string (List.map (@Symbol.terminal T NT) w) = List.map Symbol.terminal w := by
  induction w with
  | nil => rfl
  | cons =>
    unfold lift_string lift_symbol
    simp

lemma lift_string_append {u v : List (Symbol T NT)} : lift_string (u ++ v) = lift_string u ++ lift_string v := List.map_append lift_symbol u v

lemma lift_string_nonUnit {u : List (Symbol T NT)} (h : ContextFreeGrammar.NonUnit u) (h' : ∀ t, u ≠ [Symbol.terminal t]) : ContextFreeGrammar.NonUnit (right_lift_string u) := by
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

end Lifts

namespace ContextFreeGrammar
-- *********************************************************************************************** --
-- ********************************** Terminal Rule Restriction ********************************** --
-- *********************************************************************************************** --

section RestrictTerminals

def new_terminal_rules {NT : Type} (r : ContextFreeRule T NT) : List (ContextFreeRule T (NT ⊕ T)) :=
  let terminal_rule (s : Symbol T NT) : Option (ContextFreeRule T (NT ⊕ T)) :=
    match s with
    | Symbol.terminal t => some (ContextFreeRule.mk (Sum.inr t) [Symbol.terminal t])
    | Symbol.nonterminal _ => none
  r.output.filterMap terminal_rule

def restrict_terminal_rule {NT : Type} (r : ContextFreeRule T NT) : List (ContextFreeRule T (NT ⊕ T)) :=
  (match r.output with
  | [Symbol.terminal t] => ContextFreeRule.mk (Sum.inl r.input) ([Symbol.terminal t])
  | _ => (ContextFreeRule.mk (Sum.inl r.input) (right_lift_string r.output))) :: new_terminal_rules r

noncomputable def restrict_terminal_rules {NT : Type} [DecidableEq T] [DecidableEq NT]
  (rs : List (ContextFreeRule T NT)) : Finset (ContextFreeRule T (NT ⊕ T)) :=
  (rs.map restrict_terminal_rule).flatten.toFinset

noncomputable def restrict_terminals (g : ContextFreeGrammar.{0,0} T) [DecidableEq T] [DecidableEq g.NT] :=
  ContextFreeGrammar.mk (g.NT ⊕ T) (Sum.inl g.initial) (restrict_terminal_rules g.rules.toList)

end RestrictTerminals

-- *********************************************************************** --
-- Only If direction of the main correctness theorem of restrict_terminals --
-- *********************************************************************** --

section CorrectnessProof

variable {g : ContextFreeGrammar.{0,0} T}

lemma restrict_terminal_rule_right {t : T} {r : ContextFreeRule T g.NT}
  {r' : ContextFreeRule T (g.NT ⊕ T)} (h : r' ∈ restrict_terminal_rule r) (h' : r'.input = Sum.inr t) :
  r'.output = [Symbol.terminal t] := by
  unfold restrict_terminal_rule at h
  simp at h
  cases h <;> rename_i h
  · revert h
    split <;> intro h <;> rw [h] at h' <;> simp at h'
  · unfold new_terminal_rules at h
    simp at h
    obtain ⟨s, hsin, h⟩ := h
    cases s <;> simp at h
    rw [←h] at h' ⊢
    simp at h' ⊢
    exact h'

lemma restrict_terminals_rule_right [DecidableEq T] [DecidableEq g.NT] {t : T}
  {r' : ContextFreeRule T (g.NT ⊕ T)} (h : r' ∈ restrict_terminal_rules g.rules.toList)
  (h' : r'.input = Sum.inr t) : r'.output = [Symbol.terminal t] := by
  unfold restrict_terminal_rules at h
  simp at h
  obtain ⟨r, _, h⟩ := h
  exact restrict_terminal_rule_right h h'

lemma restrict_terminal_rule_left {nt : g.NT} {r : ContextFreeRule T g.NT}
  {r' : ContextFreeRule T (g.NT ⊕ T)} (h : r' ∈ restrict_terminal_rule r) (h' : r'.input = Sum.inl nt) :
  r.input = nt ∧ r.output = unlift_string r'.output := by
  unfold restrict_terminal_rule at h
  simp at h
  cases h <;> rename_i h
  · revert h
    split <;> intro h <;> rw [h] at h' ⊢ <;> simp at h' ⊢
    · rename_i heq
      constructor
      exact h'
      unfold unlift_string unlift_symbol
      simp
      exact heq
    · constructor
      exact h'
      rw [unlift_right_lift_eq]
  · unfold new_terminal_rules at h
    simp at h
    obtain ⟨r'', hrin, h⟩ := h
    cases r'' <;> simp at h
    rw [← h] at h'
    simp at h'

lemma restrict_terminals_rules_left [DecidableEq T] [DecidableEq g.NT] {nt : g.NT} {r' : ContextFreeRule T (g.NT ⊕ T)}
  (h : r' ∈ restrict_terminal_rules g.rules.toList) (h' : r'.input = Sum.inl nt) :
  ∃ r ∈ g.rules, r.input = nt ∧ r.output = unlift_string r'.output := by
  unfold restrict_terminal_rules at h
  simp at h
  obtain ⟨r, hrin, hr⟩ := h
  apply restrict_terminal_rule_left at hr
  use r
  constructor
  exact hrin
  exact hr h'

lemma restrict_terminals_produces_derives [DecidableEq T] [DecidableEq g.NT]
  {u' v' : List (Symbol T (g.NT ⊕ T))} (h : (restrict_terminals g).Produces u' v') :
  g.Derives (unlift_string u') (unlift_string v') := by
  obtain ⟨r', hrin', hr'⟩ := h
  obtain ⟨p, q, hu', hv'⟩ := hr'.exists_parts
  cases h : r'.input with
  | inl nt =>
    obtain ⟨r, hrin, hri, hro⟩ := restrict_terminals_rules_left hrin' h
    rw [hu', hv', h]
    unfold unlift_string at hro ⊢
    repeat rw [List.map_append]
    apply Produces.single
    apply Produces.append_right
    apply Produces.append_left
    use r
    constructor
    · exact hrin
    · rw [← hro]
      unfold unlift_symbol
      simp
      rw [←hri]
      exact rewrites_rule
  | inr t =>
    rw [hu', hv', h]
    rw [restrict_terminals_rule_right hrin' h]
    unfold unlift_string unlift_symbol
    simp
    rfl

lemma restrict_terminals_implies [DecidableEq T] [DecidableEq g.NT] {u' v' : List (Symbol T (g.NT ⊕ T))}
  (h : (restrict_terminals g).Derives u' v') : g.Derives (unlift_string u') (unlift_string v') := by
  induction h using Derives.head_induction_on with
  | refl => rfl
  | step hp _ ih =>
    exact Derives.trans (restrict_terminals_produces_derives hp) ih

-- ****************************************************************** --
-- If direction of the main correctness theorem of restrict_terminals --
-- ****************************************************************** --

lemma new_terminal_rules_in {t : T} {r : ContextFreeRule T g.NT} (h : (Symbol.terminal t) ∈ r.output) :
  ContextFreeRule.mk (Sum.inr t) ([Symbol.terminal t]) ∈ new_terminal_rules r := by
  unfold new_terminal_rules
  simp
  use (Symbol.terminal t)

lemma restrict_terminals_right_lift_derives [DecidableEq T] [DecidableEq g.NT] {v : List (Symbol T g.NT)} (h : ∀ t, (Symbol.terminal t) ∈ v → ∃ r ∈ g.rules, (Symbol.terminal t) ∈ r.output) :
  (restrict_terminals g).Derives (right_lift_string v) (lift_string v) := by
  induction v with
  | nil => rfl
  | cons hd tl ih =>
    simp at h ⊢
    rw [←List.singleton_append, ← @List.singleton_append _ (lift_symbol hd)]
    apply Derives.append_left_trans
    · apply ih
      intro  t h'
      apply h
      right
      exact h'
    · cases hd with
      | nonterminal =>
        unfold lift_symbol right_lift_symbol
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
        · unfold right_lift_symbol lift_symbol
          simp
          exact rewrites_rule

lemma implies_restrict_terminals [DecidableEq T] [DecidableEq g.NT] {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
  (restrict_terminals g).Derives (lift_string u) (lift_string v) := by
  induction h using Derives.head_induction_on with
  | refl => rfl
  | @step u w hp _ ih =>
    obtain ⟨r, hrin, hr⟩ := hp
    apply Derives.trans _ ih
    obtain ⟨p,q,hu,hw⟩ := hr.exists_parts
    rw [hu, hw]
    repeat rw [lift_string_append]
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
      · unfold lift_string lift_symbol
        rw [ht]
        simp
        exact rewrites_rule
    · apply Produces.trans_derives
      · use ContextFreeRule.mk (Sum.inl r.input) (right_lift_string r.output)
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
        · unfold lift_string lift_symbol
          simp
          exact rewrites_rule
      · apply restrict_terminals_right_lift_derives
        intros t ht
        use r

theorem restrict_terminals_correct [DecidableEq T] [DecidableEq g.NT] :
  g.language = g.restrict_terminals.language := by
  unfold language
  apply Set.eq_of_subset_of_subset
  · intro w h
    simp at h ⊢
    unfold Generates at h ⊢
    apply implies_restrict_terminals at h
    rw [lift_string_terminals] at h
    unfold lift_string at h
    unfold restrict_terminals
    simp at h ⊢
    exact h
  · intro w h
    simp at h ⊢
    unfold Generates at h ⊢
    apply restrict_terminals_implies at h
    rw [unlift_string_terminals] at h
    unfold restrict_terminals unlift_string at h
    simp at h
    rw [unlift_symbol_nonterminal] at h
    exact h

end CorrectnessProof

end ContextFreeGrammar
