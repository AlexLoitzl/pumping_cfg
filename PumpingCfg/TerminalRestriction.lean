/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.CountingSteps

namespace ContextFreeGrammar

variable {T : Type}

section TerminalRelated

variable {g : ContextFreeGrammar T}

inductive SymbolsRelated : (s : Symbol T g.NT) → (s' : Symbol T (g.NT ⊕ T)) → Prop :=
  | term {t : T} : SymbolsRelated (Symbol.terminal t) (Symbol.terminal t)
  | nterm_left {nt : g.NT} : SymbolsRelated (Symbol.nonterminal nt) (Symbol.nonterminal (Sum.inl nt))
  | nterm_right {t : T} : SymbolsRelated (Symbol.terminal t) (Symbol.nonterminal (Sum.inr t))

abbrev TerminalRelated : List (Symbol T g.NT) → List (Symbol T (g.NT ⊕ T)) → Prop :=
  List.Forall₂ SymbolsRelated

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
  let lift_terminal (s : Symbol T NT) : Symbol T (NT ⊕ T) :=
    match s with
    | Symbol.terminal t => Symbol.nonterminal (Sum.inr t)
    | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)
  (ContextFreeRule.mk (Sum.inl r.input) (r.output.map lift_terminal)) :: new_terminal_rules r

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

lemma restrict_terminals_implies {u' v' : List (Symbol T (g.NT ⊕ T))} (h : (restrict_terminals g).Derives u' v') :
  ∃ u v, TerminalRelated u u' ∧ TerminalRelated v v' ∧ g.Derives u v := by sorry

-- ****************************************************************** --
-- If direction of the main correctness theorem of restrict_terminals --
-- ****************************************************************** --

lemma implies_restrict_terminals {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
  ∃ u' v' : List (Symbol T (g.NT ⊕ T)), TerminalRelated u u' ∧ TerminalRelated v v' ∧
    (restrict_terminals g).Derives u' v' := by sorry

theorem eliminate_empty_correct :
  g.language = (restrict_terminals g).language := by sorry

end CorrectnessProof

end ContextFreeGrammar
