/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.ChomskyNormalForm

variable {T : Type}

namespace ContextFreeRule
def well_formed {g : ContextFreeGrammar T} (r : ContextFreeRule T g.NT) : Prop :=
  match r.output with
  | [Symbol.terminal _] => True
  | [Symbol.nonterminal _] => False -- Unit Elimination
  | [] => False -- Epsilon Elimination
  | _ => ∀ s ∈ r.output, match s with | Symbol.nonterminal _ => True | _ => False
end ContextFreeRule

namespace ContextFreeGrammar
-- **************************************************************************************** --
-- ********************************** Length Restriction ********************************** --
-- **************************************************************************************** --
section RestrictLength

variable {g : ContextFreeGrammar T}

abbrev NT'2 : Type := g.NT ⊕ Σ r : {x | x ∈ g.rules}, Fin (r.1.output.length - 2)
abbrev NT' : Type := g.NT ⊕ Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)

def compute_rules_rec (r : ContextFreeRule T g.NT) (i : Fin (r.output.length - 2)) : List (CNFRule T (g.NT')) :=
  match i with
  | ⟨0, p⟩ => match r.output.get ⟨r.output.length - 2, by omega⟩, r.output.get ⟨r.output.length - 1, by omega⟩ with
             | Symbol.nonterminal nt1, Symbol.nonterminal nt2 => [(CNFRule.node (Sum.inr ⟨r, ⟨0, p⟩⟩) (Sum.inl nt1) (Sum.inl nt2))]
             | _, _ => []
  | ⟨n + 1, p⟩ => match r.output.get ⟨r.output.length - 2 - i.val, by omega⟩ with
                 | Symbol.nonterminal nt => (CNFRule.node (Sum.inr ⟨r, ⟨i.val,by omega⟩⟩) (Sum.inl nt) (Sum.inr ⟨r, ⟨n,by omega⟩⟩))
                   :: compute_rules_rec r ⟨n, by omega⟩
                 | _ => []

def compute_rules (r : ContextFreeRule T g.NT) : List (CNFRule T (g.NT')) :=
  match h : r.output with
  | [Symbol.nonterminal nt1, Symbol.nonterminal nt2] => [CNFRule.node (Sum.inl r.input) (Sum.inl nt1) (Sum.inl nt2)]
  | [Symbol.terminal t] => [CNFRule.leaf (Sum.inl r.input) t]
  | Symbol.nonterminal nt :: _ :: _ :: _ => (CNFRule.node (Sum.inl r.input) (Sum.inl nt) (Sum.inr ⟨r, ⟨r.output.length - 3, by rw [h]; simp⟩⟩))
                                            :: compute_rules_rec r ⟨r.output.length - 3, by rw [h]; simp⟩
  | _ => []

def restrict_length_rules (rs : List (ContextFreeRule T g.NT)) : List (CNFRule T (g.NT')) :=
  (rs.map compute_rules).join

end RestrictLength

def restrict_length (g : ContextFreeGrammar.{0,0} T) : (CNF T) :=
  CNF.mk g.NT' (Sum.inl g.initial) (restrict_length_rules g.rules)

def well_formed (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, r.well_formed

section Lifts

variable {g : ContextFreeGrammar T}

def lift_symbol (s : Symbol T g.NT) : Symbol T g.NT' :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal nt => Symbol.nonterminal (Sum.inl nt)

def lift_string (w : List (Symbol T g.NT)) : List (Symbol T g.NT') := w.map lift_symbol

def unlift_symbol (s : Symbol T g.NT') : List (Symbol T g.NT) :=
  match s with
  | Symbol.terminal t => [Symbol.terminal t]
  | Symbol.nonterminal (Sum.inl nt) => [Symbol.nonterminal nt]
  | Symbol.nonterminal (Sum.inr ⟨r, ⟨i, _⟩⟩) => List.drop (r.output.length - 2 - i) r.output

def unlift_string (w : List (Symbol T g.NT')) : List (Symbol T g.NT) := (w.map unlift_symbol).join

end Lifts

-- ******************************************************************** --
-- Only If direction of the main correctness theorem of restrict_length --
-- ******************************************************************** --

section CorrectnessProof

variable {g : ContextFreeGrammar.{0,0} T}

lemma restrict_terminals_implies {u' v' : List (Symbol T g.NT')}
  (h : (restrict_length g).Derives u' v') : ∃ u v, g.Derives u v := by sorry

-- *************************************************************** --
-- If direction of the main correctness theorem of restrict_length --
-- *************************************************************** --

lemma implies_restrict_terminals {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
  (restrict_length g).Derives (lift_string u) (lift_string v) := by sorry

theorem restrict_terminals_correct:
  g.language = (restrict_length g).language := by sorry

end CorrectnessProof

end ContextFreeGrammar
