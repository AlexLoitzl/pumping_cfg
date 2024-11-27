/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.ChomskyNormalForm
import PumpingCfg.TerminalRestriction
import PumpingCfg.EpsilonElimination

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

abbrev unlift_string (w : List (Symbol T g.NT')) : List (Symbol T g.NT) := (w.map unlift_symbol).join

def unlift_string_append {u v : List (Symbol T g.NT')} :
  unlift_string (u ++ v) = unlift_string u ++ unlift_string v := by
  unfold unlift_string
  rw [List.map_append, List.join_append]

lemma unlift_lift_eq {w : List (Symbol T g.NT)} : unlift_string (lift_string w) = w := by
  unfold unlift_string lift_string
  induction w with
  | nil => rfl
  | cons hd tl ih =>
    simp at ih ⊢
    rw [← List.singleton_append, ih]
    congr
    unfold unlift_symbol lift_symbol
    cases hd <;> rfl

end Lifts

-- ******************************************************************** --
-- Only If direction of the main correctness theorem of restrict_length --
-- ******************************************************************** --

section CorrectnessProof

variable {g : ContextFreeGrammar.{0,0} T}

-- lemma compute_rules_rec_derives {r : ContextFreeRule T g.NT} {i : Fin (r.output.length - 2)}
--   {initial : g.NT'} {rules} (h: compute_rules_rec r i ⊆ rules) :
--   (CNF.mk g.NT' initial rules).Derives [Symbol.nonterminal (Sum.inr ⟨r, i⟩)]
--     (lift_string (List.drop (r.output.length - 2 - i) r.output)) := by sorry

-- lemma compute_rules_stuff {r : ContextFreeRule T g.NT} {initial : g.NT'} {rules}
--   (h: compute_rules r ⊆ rules) : (CNF.mk g.NT' initial rules).Derives [Symbol.nonterminal (Sum.inl r.input)]
--     (lift_string r.output) := by sorry
-- set_option trace.Elab.definition true
-- set_option pp.explicit true

lemma compute_rules_rec_unlift {r : ContextFreeRule T g.NT} {i : Fin (r.output.length - 2)}
  {r' : CNFRule T g.NT'} (h : r' ∈ compute_rules_rec r i) :
  unlift_string r'.output = unlift_string [Symbol.nonterminal r'.input] := by
  obtain ⟨val, p⟩ := i
  induction val with
  | zero =>
    unfold compute_rules_rec at h
    simp at h
    revert h
    split <;> intro h <;> simp at h
    · rename_i nt1 nt2 heq1 heq2
      rw [h]
      simp
      unfold unlift_string unlift_symbol
      simp
      rw [List.drop_eq_getElem_cons, List.drop_eq_getElem_cons]
      simp
      constructor
      exact heq1.symm
      constructor
      rw [←heq2]
      congr
      omega
  | succ n ih =>
    unfold compute_rules_rec at h
    simp at h
    revert h
    split <;> intro h <;> simp at h
    cases h <;> rename_i heq h
    · rw [h]
      simp
      unfold unlift_string unlift_symbol
      simp
      nth_rewrite 2 [List.drop_eq_getElem_cons]
      congr
      exact heq.symm
      omega
    · apply ih
      exact h

lemma compute_rules_rec_inl {nt : g.NT} {r : ContextFreeRule T g.NT} {r' : CNFRule T g.NT'}
  {i : Fin (r.output.length - 2)} (h' : r'.input = Sum.inl nt) : r' ∉ compute_rules_rec r i := by
  obtain ⟨val, p⟩ := i
  induction val with
  | zero =>
    unfold compute_rules_rec
    split
    · simp
      intro h
      rw [h] at h'
      simp at h'
    · exact List.not_mem_nil r'
  | succ n ih =>
    unfold compute_rules_rec
    split
    · simp
      constructor
      · intro h
        rw [h] at h'
        simp at h'
      · apply ih
    · exact List.not_mem_nil r'

lemma compute_rules_inr_length {nt : Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)}
  {r : ContextFreeRule T g.NT} {r' : CNFRule T g.NT'} (h : r' ∈ compute_rules r) (h' : r'.input = Sum.inr nt) :
  3 ≤ r.output.length := by
  unfold compute_rules at h
  revert h
  split <;> intro h <;> simp at h
  · rw [h] at h'; simp at h'
  · rw [h] at h'; simp at h'
  · cases h <;> rename_i heq h
    · rw [h] at h'; simp at h'
    · rw [heq]
      simp

lemma compute_rules_inr_in_rec {nt : Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)}
  {r : ContextFreeRule T g.NT} {r' : CNFRule T g.NT'} {p : r.output.length - 3 < r.output.length - 2}
  (h : r' ∈ compute_rules r) (h' : r'.input = Sum.inr nt) :
  r' ∈ compute_rules_rec r ⟨r.output.length - 3, p⟩ := by
  unfold compute_rules at h
  revert h
  split <;> intro h <;> simp at h
  · rw [h] at h'; simp at h'
  · rw [h] at h'; simp at h'
  · cases h <;> rename_i h
    · rw [h] at h'; simp at h'
    · exact h

lemma compute_rules_inl {nt : g.NT} {r : ContextFreeRule T g.NT} {r' : CNFRule T g.NT'}
  (h : r' ∈ compute_rules r) (h' : r'.input = Sum.inl nt) : unlift_string r'.output = r.output ∧ nt = r.input := by
  unfold compute_rules at h
  revert h
  split <;> intro h
  · unfold unlift_string unlift_symbol
    rename_i nt1 nt2 heq
    simp at h
    rw [h, heq]
    rw[h] at h'
    simp at h' ⊢
    exact h'.symm
  · unfold unlift_string unlift_symbol
    rename_i t heq
    simp at h
    rw [h, heq]
    rw[h] at h'
    simp at h' ⊢
    exact h'.symm
  · simp at h
    cases h <;> rename_i heq h
    · constructor
      · rw [h]
        simp
        rw [← List.singleton_append]
        rw [unlift_string_append]
        unfold unlift_string unlift_symbol
        simp
        rw [heq]
        congr
        simp
      · rw [h] at h'
        simp at h'
        exact h'.symm
    · exfalso
      exact compute_rules_rec_inl h' h
  · contradiction

lemma restrict_length_produces_implies {u' v' : List (Symbol T g.NT')}
  (h : (restrict_length g).Produces u' v') : g.Derives (unlift_string u') (unlift_string v') := by
  obtain ⟨r', hrin', hr'⟩ := h
  obtain ⟨p, q, hu', hv'⟩ := hr'.exists_parts
  unfold restrict_length at *
  simp at r' hrin' p q
  rw [hu', hv']
  repeat rw[unlift_string_append]
  apply Derives.append_right
  apply Derives.append_left
  unfold restrict_length_rules at hrin'
  simp at hrin'
  obtain ⟨r, hrin, hrin'⟩ := hrin'

  cases h : r'.input with
  | inl nt =>
    obtain ⟨heqo, heqi⟩ := compute_rules_inl hrin' h
    rw [heqo, heqi]
    unfold unlift_string unlift_symbol
    simp
    exact Produces.single (rewrites_produces hrin)
  | inr =>
    rw [compute_rules_rec_unlift, h]
    apply compute_rules_inr_in_rec hrin' h
    apply Nat.sub_lt_sub_left
    apply compute_rules_inr_length hrin' h
    exact Nat.lt_add_one 2

  -- unfold compute_rules at hrin'
  -- revert hrin'
  -- split <;> intro hrin'
  -- · rename_i nt1 nt2 heq
  --   simp at hrin'
  --   rw [hrin']
  --   unfold unlift_string unlift_symbol
  --   simp
  --   rw [←heq]
  --   exact Produces.single (rewrites_produces hrin)
  -- · rename_i t heq
  --   simp at hrin'
  --   rw [hrin']
  --   unfold unlift_string unlift_symbol
  --   simp
  --   rw[← heq]
  --   exact Produces.single (rewrites_produces hrin)
  -- · rename_i nt x1 x2 xs heq
  --   cases r'.input with
  --   | inl nt =>

  --     sorry
  --   | inr => sorry
  -- · contradiction

lemma restrict_length_implies {u' v' : List (Symbol T g.NT')}
  (h : (restrict_length g).Derives u' v') : g.Derives (unlift_string u') (unlift_string v') := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head u' w' hp hd ih =>

    sorry

-- *************************************************************** --
-- If direction of the main correctness theorem of restrict_length --
-- *************************************************************** --

lemma implies_restrict_length {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
  (restrict_length g).Derives (lift_string u) (lift_string v) := by sorry

theorem restrict_length_correct:
  g.language = (restrict_length g).language := by sorry

end CorrectnessProof

end ContextFreeGrammar
