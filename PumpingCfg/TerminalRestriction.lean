/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.CountingSteps

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

lemma lift_terminals {w : List T} :
  lift_string (List.map (@Symbol.terminal T NT) w) = List.map Symbol.terminal w := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    unfold lift_string
    simp
    constructor
    · unfold lift_symbol
      simp
      sorry
    · sorry

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
  (ContextFreeRule.mk (Sum.inl r.input) (r.output.map lift_symbol)) :: new_terminal_rules r

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

lemma restrict_terminals_implies' {u' v' : List (Symbol T (g.NT ⊕ T))} (h : (restrict_terminals g).Derives u' v') :
  g.Derives (unlift_string u') (unlift_string v') := by sorry

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

lemma restrict_terminals_derivs_lift : (restrict_terminals g).Derives ()

lemma implies_restrict_terminals {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
  ∃ u' v' : List (Symbol T (g.NT ⊕ T)), TerminalRelated u u' ∧ TerminalRelated v v' ∧
    (restrict_terminals g).Derives u' v' := by sorry

lemma implies_restrict_terminals' {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
  (restrict_terminals g).Derives (lift_string u) (lift_string v) := by sorry

theorem eliminate_empty_correct' :
  g.language = (restrict_terminals g).language := by
  unfold language
  apply Set.eq_of_subset_of_subset
  · intro w h
    simp at h ⊢
    unfold Generates at h ⊢
    apply implies_restrict_terminals' at h
    rw [lift_terminals] at h
    unfold lift_string lift_symbol at h
    simp at h

    exact h
  · sorry

theorem eliminate_empty_correct :
  g.language = (restrict_terminals g).language := by
  unfold language
  apply Set.eq_of_subset_of_subset
  · intro w h
    simp at h ⊢
    unfold Generates at h ⊢
    obtain ⟨u', v', h1, h2, h3⟩ := implies_restrict_terminals h
    rw [nonterminal_terminal_related_eq h1] at h3
    apply Derives.trans h3

    sorry
  · sorry

end CorrectnessProof

end ContextFreeGrammar
