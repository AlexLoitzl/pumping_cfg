/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.CountingSteps
import PumpingCfg.EpsilonElimination

namespace ContextFreeGrammar

variable {T : Type}

-- General Props of `Derives`
section Stuff

variable {g : ContextFreeGrammar T}

theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
  {u : List (Symbol T g.NT)} (h : g.Derives u v)
  (refl : P v (Derives.refl v))
  (step : ∀ {u w} (h' : g.Produces u w) (h : g.Derives w v), P w h → P u (h.head h')) : P u h :=
  Relation.ReflTransGen.head_induction_on h refl step

lemma rewrites_rule {r : ContextFreeRule T g.NT} : r.Rewrites [Symbol.nonterminal r.input] r.output := by
  rw [← r.output.append_nil, ← r.output.nil_append]
  rw [← [Symbol.nonterminal r.input].append_nil, ← [Symbol.nonterminal r.input].nil_append]
  exact r.rewrites_of_exists_parts [] []

lemma derives_exists_rule {s : Symbol T g.NT} {u v : List (Symbol T g.NT)} (h : g.Derives u v) (hnin : s ∉ u)
  (hin : s ∈ v) :
  ∃ r ∈ g.rules, s ∈ r.output := by
  induction h using Derives.head_induction_on with
  | refl => sorry
  | step => sorry

end Stuff



section TerminalRelated

variable {NT : Type}

inductive SymbolsRelated : (s : Symbol T NT) → (s' : Symbol T (NT ⊕ T)) → Prop :=
  | term {t : T} : SymbolsRelated (Symbol.terminal t) (Symbol.terminal t)
  | nterm_left {nt : NT} : SymbolsRelated (Symbol.nonterminal nt) (Symbol.nonterminal (Sum.inl nt))
  | nterm_right {t : T} : SymbolsRelated (Symbol.terminal t) (Symbol.nonterminal (Sum.inr t))

abbrev TerminalRelated : List (Symbol T NT) → List (Symbol T (NT ⊕ T)) → Prop :=
  List.Forall₂ SymbolsRelated

def lift_symbol (s : Symbol T NT) : Symbol T (NT ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.nonterminal (Sum.inr t)
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

def lift_string (w : List (Symbol T NT)) : List (Symbol T (NT ⊕ T)) := w.map lift_symbol

def left_lift_symbol (s : Symbol T NT) : Symbol T (NT ⊕ T) :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

def left_lift_string (w : List (Symbol T NT)) : List (Symbol T (NT ⊕ T)) := w.map left_lift_symbol

def unlift_symbol (s : Symbol T (NT ⊕ T)) : Symbol T NT :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal (Sum.inl nt) => Symbol.nonterminal nt
  | Symbol.nonterminal (Sum.inr t) => Symbol.terminal t

def unlift_string (w : List (Symbol T (NT ⊕ T))) : List (Symbol T NT) := w.map unlift_symbol

lemma unlift_symbol_SymbolsRelated {s' : Symbol T (NT ⊕ T)} : SymbolsRelated (unlift_symbol s') s' := by
  unfold unlift_symbol
  split <;> constructor

lemma unlift_string_terminalRelated {w' : List (Symbol T (NT ⊕ T))} : TerminalRelated (unlift_string w') w' := by
  induction w' with
  | nil => constructor
  | cons s' w' ih =>
    constructor
    exact unlift_symbol_SymbolsRelated
    exact ih

-- lemma word_terminal_related_eq {w1 w2 : List T}
--   (h : @TerminalRelated T NT (List.map Symbol.terminal w1) (List.map Symbol.terminal w2)) : w1 = w2 := by
--   match w1, w2 with
--   | [], []  => rfl
--   | s1 :: w1, s2 :: w2 =>
--     simp at h ⊢
--     constructor
--     · cases h.1
--       rfl
--     · apply word_terminal_related_eq
--       simp
--       exact h.2

lemma nonterminal_terminal_related_eq {v : NT} {u : List (Symbol T (NT ⊕ T))}
  (h : TerminalRelated [Symbol.nonterminal v] u) : u = [Symbol.nonterminal (Sum.inl v)] := by
  cases h with
  | cons h1 h2 =>
    cases h2
    cases h1
    rfl

lemma left_lift_terminals_eq {w : List T} :
  left_lift_string (List.map (@Symbol.terminal T NT) w) = List.map Symbol.terminal w := by
  induction w with
  | nil => rfl
  | cons t w ih => sorry

lemma unlift_lift_eq {w : List (Symbol T NT)} : unlift_string (lift_string w) = w := by
  induction w with
  | nil => rfl
  | cons hd tl ih =>
    unfold lift_string unlift_string at *
    simp
    constructor
    · unfold unlift_symbol lift_symbol
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

end TerminalRelated

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
  (ContextFreeRule.mk (Sum.inl r.input) (lift_string r.output)) :: new_terminal_rules r

def restrict_terminal_rules {NT : Type} (rs : List (ContextFreeRule T NT)) : List (ContextFreeRule T (NT ⊕ T)) :=
  (rs.map restrict_terminal_rule).join

def restrict_terminals (g : ContextFreeGrammar.{0,0} T) : (ContextFreeGrammar T) :=
  ContextFreeGrammar.mk (g.NT ⊕ T) (Sum.inl g.initial) (restrict_terminal_rules g.rules)

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
  · rw [h] at h'
    simp at h'
  · unfold new_terminal_rules at h
    simp at h
    obtain ⟨s, hsin, h⟩ := h
    cases s <;> simp at h
    rw [←h] at h' ⊢
    simp at h' ⊢
    exact h'

lemma restrict_terminals_rule_right {t : T} {r' : ContextFreeRule T (g.NT ⊕ T)}
  (h : r' ∈ restrict_terminal_rules g.rules) (h' : r'.input = Sum.inr t) : r'.output = [Symbol.terminal t] := by
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
  · rw [h] at h' ⊢
    simp at h' ⊢
    constructor
    · exact h'
    · rw [unlift_lift_eq]
  · unfold new_terminal_rules at h
    simp at h
    obtain ⟨r'', hrin, h⟩ := h
    cases r'' <;> simp at h
    rw [← h] at h'
    simp at h'

lemma restrict_terminals_rules_left {nt : g.NT} {r' : ContextFreeRule T (g.NT ⊕ T)}
  (h : r' ∈ restrict_terminal_rules g.rules) (h' : r'.input = Sum.inl nt) :
  ∃ r ∈ g.rules, r.input = nt ∧ r.output = unlift_string r'.output := by
  unfold restrict_terminal_rules at h
  simp at h
  obtain ⟨r, hrin, hr⟩ := h
  apply restrict_terminal_rule_left at hr
  use r
  constructor
  exact hrin
  exact hr h'

lemma restrict_terminals_produces_derives {u' v' : List (Symbol T (g.NT ⊕ T))}
  (h : (restrict_terminals g).Produces u' v') : g.Derives (unlift_string u') (unlift_string v') := by
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

lemma restrict_terminals_implies' {u' v' : List (Symbol T (g.NT ⊕ T))}
  (h : (restrict_terminals g).Derives u' v') : g.Derives (unlift_string u') (unlift_string v') := by
  induction h using Derives.head_induction_on with
  | refl => rfl
  | step hp _ ih =>
    exact Derives.trans (restrict_terminals_produces_derives hp) ih

lemma restrict_terminals_implies {u' v' : List (Symbol T (g.NT ⊕ T))} (h : (restrict_terminals g).Derives u' v') :
  ∃ u v, TerminalRelated u u' ∧ TerminalRelated v v' ∧ g.Derives u v := by
  induction h using Derives.head_induction_on with
  | refl =>
    use (unlift_string v'), (unlift_string v')
    repeat first | constructor | rfl | apply unlift_string_terminalRelated
  | @step u' w' hp hd ih =>
    sorry

-- ****************************************************************** --
-- If direction of the main correctness theorem of restrict_terminals --
-- ****************************************************************** --

lemma implies_restrict_terminals {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
  ∃ u' v' : List (Symbol T (g.NT ⊕ T)), TerminalRelated u u' ∧ TerminalRelated v v' ∧
    (restrict_terminals g).Derives u' v' := by sorry

lemma produces_terminal {r : ContextFreeRule T g.NT} {t : T} (hrin : r ∈ g.rules) (h : Symbol.terminal t ∈ r.output) :
  g.restrict_terminals.Produces [Symbol.nonterminal (Sum.inr t)] [Symbol.terminal t] := by
  use ContextFreeRule.mk (Sum.inr t) [Symbol.terminal t]
  constructor
  · unfold restrict_terminals restrict_terminal_rules restrict_terminal_rule new_terminal_rules
    simp
    use r
    constructor
    exact hrin
    use (Symbol.terminal t)
  · exact rewrites_rule

lemma restrict_terminals_lift_derives {v : List T} (h : ∀ t ∈ v, ∃ r ∈ g.rules, (Symbol.terminal t) ∈ r.output) :
  (restrict_terminals g).Derives (lift_string (List.map Symbol.terminal v)) (List.map Symbol.terminal v) := by
  induction v with
  | nil =>
    unfold lift_string
    rfl
  | cons hd tl ih =>
    simp at h
    unfold lift_string at ih ⊢
    simp at ih ⊢
    rw [← List.singleton_append]
    nth_rewrite 2 [← List.singleton_append]
    apply Derives.append_left_trans
    · exact ih h.2
    · unfold lift_symbol
      simp
      apply Produces.single
      obtain ⟨r, hrin, hr⟩ := h.1
      exact produces_terminal hrin hr

lemma implies_restrict_terminals' {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
  (restrict_terminals g).Derives (lift_string u) (lift_string v) := by
  sorry

theorem restrict_terminals_correct:
  g.language = (restrict_terminals g).language := by
  unfold language
  apply Set.eq_of_subset_of_subset
  · intro w h
    simp at h ⊢
    unfold Generates at h ⊢
    have h' : [Symbol.nonterminal g.restrict_terminals.initial] = lift_string [Symbol.nonterminal g.initial] := by
      unfold restrict_terminals lift_string lift_symbol
      rfl
    rw [h']
    apply Derives.trans
    exact implies_restrict_terminals' h
    apply restrict_terminals_lift_derives
    intro t ht
    apply derives_exists_rule h <;> simp
    exact ht
  · intro w h
    simp at h ⊢
    unfold Generates at h ⊢
    apply restrict_terminals_implies' at h
    rw [unlift_string_terminals] at h
    unfold restrict_terminals unlift_string at h
    simp at h
    rw [unlift_symbol_nonterminal] at h
    exact h

-- theorem eliminate_empty_correct :
--   g.language = (restrict_terminals g).language := by
--   unfold language
--   apply Set.eq_of_subset_of_subset
--   · intro w h
--     simp at h ⊢
--     unfold Generates at h ⊢
--     obtain ⟨u', v', h1, h2, h3⟩ := implies_restrict_terminals h
--     rw [nonterminal_terminal_related_eq h1] at h3
--     apply Derives.trans h3

--     sorry
--   · intro w h
--     simp at h ⊢
--     unfold Generates at h ⊢
--     apply restrict_terminals_implies' at h
--     rw [unlift_string_terminals] at h
--     unfold restrict_terminals unlift_string at h
--     simp at h
--     rw [unlift_symbol_nonterminal] at h
--     exact h

end CorrectnessProof

end ContextFreeGrammar
