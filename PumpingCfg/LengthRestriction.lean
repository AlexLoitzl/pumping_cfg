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
variable {NT : Type}
def wellformed  (r : ContextFreeRule T NT) : Prop :=
  match r.output with
  | [Symbol.terminal _] => True
  | [Symbol.nonterminal _] => False -- Unit Elimination
  | [] => False -- Epsilon Elimination
  | _ => ∀ s ∈ r.output, match s with | Symbol.nonterminal _ => True | _ => False

lemma wellformed_nonterminal {r : ContextFreeRule T NT} (i : Fin r.output.length) (h : r.wellformed)
  (h' : 2 ≤ r.output.length):
  ∃ nt, r.output[i] = Symbol.nonterminal nt := by
  revert h
  unfold wellformed
  split <;> intro h <;> try contradiction
  · rename_i heq
    rw [heq] at h'
    contradiction
  · specialize h (r.output[i]'i.2) (r.output.get_mem i)
    cases h' : r.output[i] with
    | nonterminal nt => use nt
    | terminal _ =>
      rw [h'] at h
      simp at h

end ContextFreeRule

namespace ContextFreeGrammar

namespace CNF
variable {NT : Type}

lemma rewrites_rule {r : CNFRule T NT} : r.Rewrites [Symbol.nonterminal r.input] r.output := by
  rw [← r.output.append_nil, ← r.output.nil_append]
  rw [← [Symbol.nonterminal r.input].append_nil, ← [Symbol.nonterminal r.input].nil_append]
  exact r.rewrites_of_exists_parts [] []
end CNF

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

def restrict_length_rules [DecidableEq T] [DecidableEq g.NT] (rs : List (ContextFreeRule T g.NT)) :=
  (rs.map compute_rules).flatten.toFinset

end RestrictLength

noncomputable def restrict_length (g : ContextFreeGrammar.{0,0} T) [DecidableEq T] [DecidableEq g.NT] :=
  CNF.mk g.NT' (Sum.inl g.initial) (restrict_length_rules g.rules.toList)

def wellformed (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, r.wellformed

section Lifts

variable {g : ContextFreeGrammar T}

def lift_symbol (s : Symbol T g.NT) : Symbol T g.NT' :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal nt => Symbol.nonterminal (Sum.inl nt)

lemma lift_symbol_nonterminal {nt : g.NT} : lift_symbol (Symbol.nonterminal nt) = Symbol.nonterminal (Sum.inl nt) := by rfl

lemma lift_symbol_terminal {t : T} : lift_symbol (Symbol.terminal t) = (@Symbol.terminal T g.NT') t := by rfl

abbrev lift_string (w : List (Symbol T g.NT)) : List (Symbol T g.NT') := w.map lift_symbol

lemma lift_string_nonterminal {nt : g.NT} :
  lift_string [Symbol.nonterminal nt] = [Symbol.nonterminal (Sum.inl nt)] := by rfl

lemma lift_string_terminals {w : List T} :
  lift_string (List.map Symbol.terminal w) = List.map (@Symbol.terminal T g.NT') w := by
  induction w with
  | nil => rfl
  | cons hd tl ih =>
    simp at ih ⊢
    constructor
    · unfold lift_symbol
      rfl
    · exact ih

def lift_string_append {u v : List (Symbol T g.NT)} :
  lift_string (u ++ v) = lift_string u ++ lift_string v := List.map_append lift_symbol u v

def unlift_symbol (s : Symbol T g.NT') : List (Symbol T g.NT) :=
  match s with
  | Symbol.terminal t => [Symbol.terminal t]
  | Symbol.nonterminal (Sum.inl nt) => [Symbol.nonterminal nt]
  | Symbol.nonterminal (Sum.inr ⟨r, ⟨i, _⟩⟩) => List.drop (r.output.length - 2 - i) r.output

abbrev unlift_string (w : List (Symbol T g.NT')) : List (Symbol T g.NT) := (w.map unlift_symbol).flatten

def unlift_string_append {u v : List (Symbol T g.NT')} :
  unlift_string (u ++ v) = unlift_string u ++ unlift_string v := by
  unfold unlift_string
  rw [List.map_append, List.flatten_append]

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

lemma unlift_string_nonterminal {nt : g.NT} :
  unlift_string [Symbol.nonterminal (Sum.inl nt)] = [Symbol.nonterminal nt] := by
  unfold unlift_string unlift_symbol
  simp

lemma unlift_symbol_terminal {t : T} :
  unlift_symbol (@Symbol.terminal T g.NT' t) = [Symbol.terminal t] := by
  unfold unlift_symbol
  simp

lemma unlift_string_terminals {w : List T} :
  unlift_string (List.map (@Symbol.terminal T g.NT') w) = List.map Symbol.terminal w := by
  induction w with
  | nil => rfl
  | cons hd tl ih =>
    rw [←List.singleton_append, List.map_append, List.map_append, unlift_string_append]
    congr

end Lifts

-- ******************************************************************** --
-- Only If direction of the main correctness theorem of restrict_length --
-- ******************************************************************** --

section CorrectnessProof

variable {g : ContextFreeGrammar.{0,0} T}

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
      swap
      omega
      swap
      omega
      congr
      · rw [← heq1]
      · rw [← heq2]
        congr
        omega
      · simp
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

lemma restrict_length_produces_implies {u' v' : List (Symbol T g.NT')} [DecidableEq T] [DecidableEq g.NT]
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

lemma restrict_length_implies {u' v' : List (Symbol T g.NT')} [DecidableEq T] [DecidableEq g.NT]
  (h : (restrict_length g).Derives u' v') : g.Derives (unlift_string u') (unlift_string v') := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head u' w' hp _ ih => exact Derives.trans (restrict_length_produces_implies hp) ih

-- *************************************************************** --
-- If direction of the main correctness theorem of restrict_length --
-- *************************************************************** --

lemma compute_rules_rec_derives [DecidableEq T] [DecidableEq g.NT] {r : ContextFreeRule T g.NT}
  {i : Fin (r.output.length - 2)} {initial : g.NT'} {rules} (h: compute_rules_rec r i ⊆ rules)
  (h' : r.wellformed) :
  (CNF.mk g.NT' initial rules.toFinset).Derives [Symbol.nonterminal (Sum.inr ⟨r, i⟩)]
    (lift_string (List.drop (r.output.length - 2 - i) r.output)) := by
  obtain ⟨n, p⟩ := i
  induction n with
  | zero =>
    unfold compute_rules_rec at h
    simp at h ⊢
    revert h
    split <;> intro h
    · rename_i nt1 nt2 heq1 heq2
      have heq : (List.drop (r.output.length - 2) (List.map lift_symbol r.output)) = lift_string [Symbol.nonterminal nt1, Symbol.nonterminal nt2] := by
        have h1 : r.output.length - 2 + 1 + 1 = r.output.length := by omega
        rw [← List.map_drop, ← List.getElem_cons_drop_succ_eq_drop, ← List.getElem_cons_drop_succ_eq_drop]
        rw [h1, List.drop_length, heq1]
        simp
        congr
        rw [← heq2]
        congr
        omega
        omega
      rw [heq]
      simp
      rw [lift_symbol_nonterminal, lift_symbol_nonterminal]
      apply CNF.Produces.single
      constructor
      · constructor
        · simp at h ⊢
          exact h
        · exact CNF.rewrites_rule
    · rename_i hn
      exfalso
      obtain ⟨nt1, h1⟩ := r.wellformed_nonterminal ⟨r.output.length - 2, by omega⟩ h' (by omega)
      obtain ⟨nt2, h2⟩ := r.wellformed_nonterminal ⟨r.output.length - 1, by omega⟩ h' (by omega)
      apply hn
      exact h1
      exact h2
  | succ n ih =>
    unfold compute_rules_rec at h
    revert h
    split <;> intro h
    · rename_i nt heq
      simp at h heq
      obtain ⟨h1, h2⟩ := h
      rw [← List.getElem_cons_drop_succ_eq_drop, heq]
      apply CNF.Produces.trans_derives
      · constructor
        · constructor
          · simp
            exact h1
          · exact CNF.rewrites_rule
      · simp
        rw [← List.singleton_append, ← List.singleton_append, lift_symbol_nonterminal, ← List.map_drop]
        apply CNF.Derives.append_left
        have h : r.output.length - 2 - (n + 1) +1 = r.output.length - 2 - n := by omega
        rw [h]
        apply ih
        exact h2
    · rename_i hn
      obtain ⟨nt1, h1⟩ := r.wellformed_nonterminal ⟨r.output.length - 2 - (n + 1), by omega⟩ h' (by omega)
      simp at h1 ⊢
      exfalso
      apply hn
      exact h1

lemma compute_rules_stuff [DecidableEq T] [DecidableEq g.NT] {r : ContextFreeRule T g.NT} {initial : g.NT'} {rules}
  (h: compute_rules r ⊆ rules) (h' : r.wellformed) : (CNF.mk g.NT' initial rules.toFinset).Derives [Symbol.nonterminal (Sum.inl r.input)]
    (lift_string r.output) := by
  unfold compute_rules at h
  revert h
  split <;> intro h <;> rename_i heq
  · rename_i nt1 nt2
    simp at h
    apply CNF.Produces.single
    constructor
    · constructor
      · simp
        exact h
      · rw [heq]
        unfold lift_string
        simp
        rw [lift_symbol_nonterminal, lift_symbol_nonterminal]
        exact CNF.rewrites_rule
  · rename_i t
    simp at h
    apply CNF.Produces.single
    constructor
    · constructor
      · simp
        exact h
      · rw [heq]
        unfold lift_string
        simp
        rw [lift_symbol_terminal]
        exact CNF.rewrites_rule
  · rename_i nt x1 x2 xs
    simp at h
    obtain ⟨h1, h2⟩ := h
    apply CNF.Produces.trans_derives
    · constructor
      · constructor
        · simp
          exact h1
        · exact CNF.rewrites_rule
    · nth_rewrite 4 [heq]
      simp
      rw [← List.singleton_append, ← (@List.singleton_append _ (lift_symbol _)), lift_symbol_nonterminal]
      apply CNF.Derives.append_left
      have heq' : (lift_symbol x1 :: lift_symbol x2 :: List.map lift_symbol xs = lift_string (List.drop (r.output.length - 2 - (r.output.length - 3)) r.output)) := by
        change (lift_string (x1 :: x2 :: xs) = _)
        congr
        rw [heq]
        simp
      rw [heq']
      apply compute_rules_rec_derives h2 h'
  · rename_i h1 h2
    unfold ContextFreeRule.wellformed at h'
    match h : r.output with
    | [] => rw [h] at h'; simp at h'
    | [Symbol.terminal _ ] => exfalso; apply h2; exact h
    | [Symbol.nonterminal _ ] => rw [h] at h'; simp at h'
    | [Symbol.nonterminal _ , Symbol.nonterminal _] => exfalso; apply h1; exact h
    | [Symbol.nonterminal _ , Symbol.terminal _] => rw [h] at h'; simp at h'
    | Symbol.terminal _ :: x1 :: xs  => rw [h] at h'; simp at h'
    | Symbol.nonterminal _ :: x1 :: x2 :: xs  =>
      exfalso
      apply heq
      exact h

lemma restrict_length_produces_derives [DecidableEq T] [DecidableEq g.NT] {u v : List (Symbol T g.NT)} (h : g.Produces u v) (h' : g.wellformed):
  (restrict_length g).Derives (lift_string u) (lift_string v) := by
  obtain ⟨r, hrin, hr⟩ := h
  obtain ⟨p,q, hu, hv⟩ := hr.exists_parts
  rw[hu, hv]
  repeat rw [lift_string_append]
  apply CNF.Derives.append_right
  apply CNF.Derives.append_left
  rw [lift_string_nonterminal]
  apply compute_rules_stuff
  intro r' hrin'
  simp
  use r
  apply h'
  exact hrin

lemma implies_restrict_length [DecidableEq T] [DecidableEq g.NT] {u v : List (Symbol T g.NT)}
  (h : g.Derives u v) (h' : g.wellformed): (restrict_length g).Derives (lift_string u) (lift_string v) := by
  induction h using Derives.head_induction_on with
  | refl => rfl
  | step hp _ ih =>
    exact CNF.Derives.trans (restrict_length_produces_derives hp h') ih

theorem restrict_length_correct [DecidableEq T] [DecidableEq g.NT] (h : g.wellformed) :
  g.language = (restrict_length g).language := by
  unfold language CNF.language
  apply Set.eq_of_subset_of_subset
  · intro w h'
    unfold Generates at h'
    unfold CNF.Generates
    apply implies_restrict_length at h'
    rw [lift_string_nonterminal, lift_string_terminals] at h'
    exact h' h
  · intro w h
    unfold Generates
    unfold CNF.Generates at h
    simp at h ⊢
    apply restrict_length_implies at h
    unfold restrict_length at h
    simp at h
    rw [unlift_string_nonterminal, unlift_string_terminals] at h
    exact h

end CorrectnessProof

end ContextFreeGrammar
