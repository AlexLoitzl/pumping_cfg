/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.ChomskyNormalForm
import PumpingCfg.TerminalRestriction
import PumpingCfg.EpsilonElimination

universe uN uT
variable {T : Type uT}

namespace ContextFreeRule
variable {N : Type*}

/- `Wellformed r` holds if the rule's output is not a single nonterminal (`UnitRule`), not empty,
 or if the output is more than one symbol, it is only nonterminals -/
inductive Wellformed : (ContextFreeRule T N) → Prop where
  /- Rule rewriting to a single terminal is wellformed -/
  | terminal {nt : N} {t : T} : Wellformed (ContextFreeRule.mk nt [Symbol.terminal t])
  /- Rule rewriting to mulitple nonterminals is wellformed -/
  | nonterminals {nt: N} (u : List (Symbol T N)) (h1 : 2 ≤ u.length)
      (h2 : ∀ s ∈ u, match s with | Symbol.nonterminal _ => True | _ => False) :
      Wellformed (ContextFreeRule.mk nt u)

-- def Wellformed  (r : ContextFreeRule T NT) : Prop :=
--   match r.output with
--   | [Symbol.terminal _] => True
--   | [Symbol.nonterminal _] => False -- Unit Elimination
--   | [] => False -- Epsilon Elimination
--   | _ => ∀ s ∈ r.output, match s with | Symbol.nonterminal _ => True | _ => False

lemma only_nonterminals {u : List (Symbol T N)}
    (h : ∀ s ∈ u, match s with | Symbol.nonterminal _ => True | _ => False) :
    ∃ v : List N, v.map Symbol.nonterminal = u := by
  induction u with
  | nil => use []; rfl
  | cons u1 u ih =>
    simp at h
    obtain ⟨u', heq1⟩ := ih h.2
    cases u1
    · simp at h
    · rename_i n
      use n :: u'
      simp
      exact heq1

lemma Wellformed.mem_nonterminal {r : ContextFreeRule T N} (hr : r.Wellformed)
    (i : Fin r.output.length) (h : 2 ≤ r.output.length) :
    ∃ nt, r.output[i] = Symbol.nonterminal nt := by
  induction hr with
  | terminal => simp at h
  | nonterminals u h1 h2 =>
    simp at i ⊢
    specialize h2 (u[i]'i.2) (u.get_mem i)
    revert h2; split <;> rename_i n he <;> intro
    · use n
      exact he
    · contradiction

lemma Wellformed.cases {r : ContextFreeRule T N} (h : r.Wellformed) :
    (∃ t : T, r.output = [Symbol.terminal t])
    ∨ (∃ (nt1 nt2 : N) (nts : List N), r.output = Symbol.nonterminal nt1 :: Symbol.nonterminal nt2
      :: nts.map Symbol.nonterminal) := by
  induction h with
  | @terminal _ t => left; use t
  | nonterminals u h1 h2 =>
    match u with
    | [] => contradiction
    | [x] => contradiction
    | .terminal t :: _ :: _ => specialize h2 (Symbol.terminal t); simp at h2
    | _ :: .terminal t :: _ => specialize h2 (Symbol.terminal t); simp at h2
    | .nonterminal nt1 :: .nonterminal nt2 :: u =>
      right
      simp at h2
      obtain ⟨u', heq⟩ := only_nonterminals h2
      use nt1, nt2, u'
      simp
      exact heq.symm

end ContextFreeRule

namespace ContextFreeGrammar

-- **************************************************************************************** --
-- ********************************** Length Restriction ********************************** --
-- **************************************************************************************** --
section RestrictLength

variable {g : ContextFreeGrammar.{uN, uT} T}

abbrev NT' := g.NT ⊕ Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)

def compute_rules_rec (r : ContextFreeRule T g.NT) (i : Fin (r.output.length - 2)) :
    List (CNFRule T g.NT') :=
  match i with
  | ⟨0, p⟩ => match r.output.get ⟨r.output.length - 2, by omega⟩,
               r.output.get ⟨r.output.length - 1, by omega⟩ with
             | Symbol.nonterminal nt1, Symbol.nonterminal nt2 =>
               [(CNFRule.node (Sum.inr ⟨r, ⟨0, p⟩⟩) (Sum.inl nt1) (Sum.inl nt2))]
             | _, _ => []
  | ⟨n + 1, p⟩ => match r.output.get ⟨r.output.length - 2 - i.val, by omega⟩ with
                 | Symbol.nonterminal nt =>
                   (CNFRule.node (Sum.inr ⟨r, ⟨i.val,by omega⟩⟩) (Sum.inl nt)
                     (Sum.inr ⟨r, ⟨n,by omega⟩⟩))
                   :: compute_rules_rec r ⟨n, by omega⟩
                 | _ => []

def compute_rules (r : ContextFreeRule T g.NT) : List (CNFRule T g.NT') :=
  match h : r.output with
  | [Symbol.nonterminal nt1, Symbol.nonterminal nt2] =>
      [CNFRule.node (Sum.inl r.input) (Sum.inl nt1) (Sum.inl nt2)]
  | [Symbol.terminal t] => [CNFRule.leaf (Sum.inl r.input) t]
  | Symbol.nonterminal nt :: _ :: _ :: _ =>
    (CNFRule.node (Sum.inl r.input) (Sum.inl nt) (Sum.inr ⟨r, ⟨r.output.length - 3, by rw [h]; simp⟩⟩))
      :: compute_rules_rec r ⟨r.output.length - 3, by rw [h]; simp⟩
  | _ => []

def restrict_length_rules [DecidableEq T] [DecidableEq g.NT] (rs : List (ContextFreeRule T g.NT)) :=
  (rs.map compute_rules).flatten.toFinset

end RestrictLength

noncomputable def restrict_length (g : ContextFreeGrammar.{uN,uT} T) [DecidableEq T]
    [eq : DecidableEq g.NT] :=
  CNF.mk g.NT' (Sum.inl g.initial) (restrict_length_rules g.rules.toList)

def Wellformed (g : ContextFreeGrammar T) : Prop := ∀ r ∈ g.rules, r.Wellformed

section EmbedProject

variable {g : ContextFreeGrammar.{uN, uT} T}

def embed_symbol (s : Symbol T g.NT) : Symbol T g.NT' :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal nt => Symbol.nonterminal (Sum.inl nt)

lemma embed_symbol_nonterminal {nt : g.NT} :
    embed_symbol (Symbol.nonterminal nt) = Symbol.nonterminal (Sum.inl nt) := by rfl

lemma embed_symbol_terminal {t : T} :
    embed_symbol (Symbol.terminal t) = (@Symbol.terminal T g.NT') t := by rfl

abbrev embed_string (u : List (Symbol T g.NT)) : List (Symbol T g.NT') := u.map embed_symbol

lemma embed_string_nonterminal {nt : g.NT} :
    embed_string [Symbol.nonterminal nt] = [Symbol.nonterminal (Sum.inl nt)] := by rfl

lemma embed_string_terminals {u : List T} :
    embed_string (List.map Symbol.terminal u) = List.map (@Symbol.terminal T g.NT') u := by
  induction u with
  | nil => rfl
  | cons hd tl ih =>
    simp at ih ⊢
    constructor
    · unfold embed_symbol
      rfl
    · exact ih

def embed_string_append {u v : List (Symbol T g.NT)} :
  embed_string (u ++ v) = embed_string u ++ embed_string v := List.map_append embed_symbol u v

def project_symbol (s : Symbol T g.NT') : List (Symbol T g.NT) :=
  match s with
  | Symbol.terminal t => [Symbol.terminal t]
  | Symbol.nonterminal (Sum.inl nt) => [Symbol.nonterminal nt]
  | Symbol.nonterminal (Sum.inr ⟨r, ⟨i, _⟩⟩) => List.drop (r.output.length - 2 - i) r.output

abbrev project_string (u : List (Symbol T g.NT')) : List (Symbol T g.NT) :=
  (u.map project_symbol).flatten

lemma project_string_append {u v : List (Symbol T g.NT')} :
    project_string (u ++ v) = project_string u ++ project_string v := by
  unfold project_string
  rw [List.map_append, List.flatten_append]

lemma project_embed_eq {u : List (Symbol T g.NT)} : project_string (embed_string u) = u := by
  unfold project_string embed_string
  induction u with
  | nil => rfl
  | cons hd tl ih =>
    simp at ih ⊢
    rw [← List.singleton_append, ih]
    congr
    unfold project_symbol embed_symbol
    cases hd <;> rfl

lemma project_string_nonterminal {nt : g.NT} :
    project_string [Symbol.nonterminal (Sum.inl nt)] = [Symbol.nonterminal nt] := by
  unfold project_string project_symbol
  simp

lemma project_symbol_terminal {t : T} :
    project_symbol (@Symbol.terminal T g.NT' t) = [Symbol.terminal t] := by
  unfold project_symbol
  simp

lemma project_string_terminals {u : List T} :
    project_string (List.map (@Symbol.terminal T g.NT') u) = List.map Symbol.terminal u := by
  induction u with
  | nil => rfl
  | cons hd tl ih =>
    rw [←List.singleton_append, List.map_append, List.map_append, project_string_append]
    congr

end EmbedProject

-- ******************************************************************** --
-- Only If direction of the main correctness theorem of restrict_length --
-- ******************************************************************** --

section CorrectnessProof

variable {g : ContextFreeGrammar.{uN, uT} T}

lemma compute_rules_rec_project {r : ContextFreeRule T g.NT} {i : Fin (r.output.length - 2)}
    {r' : CNFRule T g.NT'} (h : r' ∈ compute_rules_rec r i) :
    project_string r'.output = project_string [Symbol.nonterminal r'.input] := by
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
      unfold project_string project_symbol
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
      unfold project_string project_symbol
      simp
      nth_rewrite 2 [List.drop_eq_getElem_cons]
      congr
      exact heq.symm
      omega
    · apply ih
      exact h

lemma compute_rules_rec_inl {nt : g.NT} {r : ContextFreeRule T g.NT} {r' : CNFRule T g.NT'}
    {i : Fin (r.output.length - 2)} (heq : r'.input = Sum.inl nt) :
    r' ∉ compute_rules_rec r i := by
  obtain ⟨val, p⟩ := i
  induction val with
  | zero =>
    unfold compute_rules_rec
    split
    · simp
      intro h
      rw [h] at heq
      simp at heq
    · exact List.not_mem_nil r'
  | succ n ih =>
    unfold compute_rules_rec
    split
    · simp
      constructor
      · intro h
        rw [h] at heq
        simp at heq
      · apply ih
    · exact List.not_mem_nil r'

lemma compute_rules_inr_length {nt : Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)}
    {r : ContextFreeRule T g.NT} {r' : CNFRule T g.NT'} (hmem : r' ∈ compute_rules r)
    (heq : r'.input = Sum.inr nt) :
    3 ≤ r.output.length := by
  unfold compute_rules at hmem
  revert hmem
  split <;> intro h <;> simp at h
  · rw [h] at heq; simp at heq
  · rw [h] at heq; simp at heq
  · cases h <;> rename_i heq h
    · rw[heq]; simp
    · rw [heq]
      simp

lemma compute_rules_inr_in_rec {nt : Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)}
    {r : ContextFreeRule T g.NT} {r' : CNFRule T g.NT'}
    {p : r.output.length - 3 < r.output.length - 2} (hmem : r' ∈ compute_rules r)
    (heq : r'.input = Sum.inr nt) :
    r' ∈ compute_rules_rec r ⟨r.output.length - 3, p⟩ := by
  unfold compute_rules at hmem
  revert hmem
  split <;> intro hmem <;> simp at hmem
  · rw [hmem] at heq; simp at heq
  · rw [hmem] at heq; simp at heq
  · cases hmem <;> rename_i hmem
    · rw [hmem] at heq; simp at heq
    · exact hmem

lemma compute_rules_inl {nt : g.NT} {r : ContextFreeRule T g.NT} {r' : CNFRule T g.NT'}
    (hmem : r' ∈ compute_rules r) (heq : r'.input = Sum.inl nt) :
    project_string r'.output = r.output ∧ nt = r.input := by
  unfold compute_rules at hmem
  revert hmem
  split <;> intro hmem
  · unfold project_string project_symbol
    rename_i nt1 nt2 heq2
    simp at hmem
    rw [hmem, heq2]
    rw[hmem] at heq
    simp at heq ⊢
    exact heq.symm
  · unfold project_string project_symbol
    rename_i t heq2
    simp at hmem
    rw [hmem, heq2]
    rw[hmem] at heq
    simp at heq ⊢
    exact heq.symm
  · simp at hmem
    cases hmem <;> rename_i heq2 hmem
    · constructor
      · rw [hmem]
        simp
        rw [← List.singleton_append]
        rw [project_string_append]
        unfold project_string project_symbol
        simp
        rw [heq2]
        congr
        simp
      · rw [hmem] at heq
        simp at heq
        exact heq.symm
    · exfalso
      exact compute_rules_rec_inl heq hmem
  · contradiction

lemma restrict_length_produces_implies {u v : List (Symbol T g.NT')} [DecidableEq T] [DecidableEq g.NT]
    (huv : (restrict_length g).Produces u v) :
    g.Derives (project_string u) (project_string v) := by
  obtain ⟨r, hrin, hr⟩ := huv
  obtain ⟨p, q, hu, hv⟩ := hr.exists_parts
  unfold restrict_length at *
  simp at r hrin p q
  rw [hu, hv]
  repeat rw[project_string_append]
  apply Derives.append_right
  apply Derives.append_left
  unfold restrict_length_rules at hrin
  simp at hrin
  obtain ⟨r', hrin, hrin'⟩ := hrin
  cases h : r.input with
  | inl nt =>
    obtain ⟨heqo, heqi⟩ := compute_rules_inl hrin' h
    rw [heqo, heqi]
    unfold project_string project_symbol
    simp
    exact Produces.single (rewrites_produces hrin)
  | inr =>
    rw [compute_rules_rec_project, h]
    apply compute_rules_inr_in_rec hrin' h
    apply Nat.sub_lt_sub_left
    apply compute_rules_inr_length hrin' h
    exact Nat.lt_add_one 2

lemma restrict_length_implies {u v : List (Symbol T g.NT')} [DecidableEq T] [DecidableEq g.NT]
    (huv : (restrict_length g).Derives u v) :
    g.Derives (project_string u) (project_string v) := by
  induction huv using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head u' w' hp _ ih => exact Derives.trans (restrict_length_produces_implies hp) ih

-- *************************************************************** --
-- If direction of the main correctness theorem of restrict_length --
-- *************************************************************** --

lemma compute_rules_rec_derives [DecidableEq T] [DecidableEq g.NT] {r : ContextFreeRule T g.NT}
    {i : Fin (r.output.length - 2)} {initial : g.NT'} {rules} (hsub : compute_rules_rec r i ⊆ rules)
    (hr : r.Wellformed) :
    (CNF.mk g.NT' initial rules.toFinset).Derives [Symbol.nonterminal (Sum.inr ⟨r, i⟩)]
      (embed_string (List.drop (r.output.length - 2 - i) r.output)) := by
  obtain ⟨n, p⟩ := i
  induction n with
  | zero =>
    unfold compute_rules_rec at hsub
    simp at hsub ⊢
    revert hsub
    split <;> intro hsub
    · rename_i nt1 nt2 heq1 heq2
      have heq : (List.drop (r.output.length - 2) (List.map embed_symbol r.output))
          = embed_string [Symbol.nonterminal nt1, Symbol.nonterminal nt2] := by
        have h1 : r.output.length - 2 + 1 + 1 = r.output.length := by omega
        rw [← List.map_drop, ← List.getElem_cons_drop_succ_eq_drop,
          ← List.getElem_cons_drop_succ_eq_drop]
        rw [h1, List.drop_length, heq1]
        simp
        congr
        rw [← heq2]
        congr
        omega
        omega
      rw [heq]
      simp
      rw [embed_symbol_nonterminal, embed_symbol_nonterminal]
      apply CNF.Produces.single
      constructor
      · constructor
        · simp at hsub ⊢
          exact hsub
        · exact CNFRule.Rewrites.input_output
    · rename_i hn
      exfalso
      obtain ⟨nt1, h1⟩ := hr.mem_nonterminal ⟨r.output.length - 2, by omega⟩ (by omega)
      obtain ⟨nt2, h2⟩ := hr.mem_nonterminal ⟨r.output.length - 1, by omega⟩ (by omega)
      apply hn
      exact h1
      exact h2
  | succ n ih =>
    unfold compute_rules_rec at hsub
    revert hsub
    split <;> intro hsub
    · rename_i nt heq
      simp at hsub heq
      obtain ⟨h1, h2⟩ := hsub
      rw [← List.getElem_cons_drop_succ_eq_drop, heq]
      apply CNF.Produces.trans_derives
      · constructor
        · constructor
          · simp
            exact h1
          · exact CNFRule.Rewrites.input_output
      · simp
        rw [← List.singleton_append, ← List.singleton_append, embed_symbol_nonterminal, ← List.map_drop]
        apply CNF.Derives.append_left
        have h : r.output.length - 2 - (n + 1) +1 = r.output.length - 2 - n := by omega
        rw [h]
        apply ih
        exact h2
    · rename_i hn
      obtain ⟨nt1, h1⟩ := hr.mem_nonterminal ⟨r.output.length - 2 - (n + 1), by omega⟩ (by omega)
      simp at h1 ⊢
      exfalso
      apply hn
      exact h1

lemma compute_rules_derives_embed_output [DecidableEq T] [DecidableEq g.NT]
    {r : ContextFreeRule T g.NT} {initial : g.NT'} {rules} (hsub : compute_rules r ⊆ rules)
    (hr : r.Wellformed) :
    (CNF.mk g.NT' initial rules.toFinset).Derives [Symbol.nonterminal (Sum.inl r.input)]
      (embed_string r.output) := by
  unfold compute_rules at hsub
  revert hsub
  split <;> intro hsub <;> rename_i heq
  · rename_i nt1 nt2
    simp at hsub
    apply CNF.Produces.single
    constructor
    · constructor
      · simp
        exact hsub
      · rw [heq]
        unfold embed_string
        simp
        rw [embed_symbol_nonterminal, embed_symbol_nonterminal]
        exact CNFRule.Rewrites.input_output
  · rename_i t
    simp at hsub
    apply CNF.Produces.single
    constructor
    · constructor
      · simp
        exact hsub
      · rw [heq]
        unfold embed_string
        simp
        rw [embed_symbol_terminal]
        exact CNFRule.Rewrites.input_output
  · rename_i nt x1 x2 xs
    simp at hsub
    obtain ⟨h1, h2⟩ := hsub
    apply CNF.Produces.trans_derives
    · constructor
      · constructor
        · simp
          exact h1
        · exact CNFRule.Rewrites.input_output
    · nth_rewrite 4 [heq]
      simp
      rw [← List.singleton_append, ← (@List.singleton_append _ (embed_symbol _)),
           embed_symbol_nonterminal]
      apply CNF.Derives.append_left
      have heq' :
        (embed_symbol x1 :: embed_symbol x2 :: List.map embed_symbol xs =
          embed_string (List.drop (r.output.length - 2 - (r.output.length - 3)) r.output)) := by
        change (embed_string (x1 :: x2 :: xs) = _)
        congr
        rw [heq]
        simp
      rw [heq']
      apply compute_rules_rec_derives h2 hr
  · rename_i h1 h2
    obtain (⟨t, heq⟩ | ⟨nt1, nt2, nts, h⟩) := hr.cases
    · exfalso; exact h2 t heq
    · exfalso
      cases nts
      · exfalso; exact h1 nt1 nt2 h
      · exfalso
        apply heq
        exact h

lemma restrict_length_produces_derives [DecidableEq T] [DecidableEq g.NT]
    {u v : List (Symbol T g.NT)} (huv : g.Produces u v) (hg : g.Wellformed) :
    (restrict_length g).Derives (embed_string u) (embed_string v) := by
  obtain ⟨r, hrin, hr⟩ := huv
  obtain ⟨p,q, hu, hv⟩ := hr.exists_parts
  rw[hu, hv]
  repeat rw [embed_string_append]
  apply CNF.Derives.append_right
  apply CNF.Derives.append_left
  rw [embed_string_nonterminal]
  apply compute_rules_derives_embed_output
  intro r' hrin'
  simp
  use r
  apply hg
  exact hrin

lemma implies_restrict_length [DecidableEq T] [DecidableEq g.NT] {u v : List (Symbol T g.NT)}
    (huv : g.Derives u v) (hg : g.Wellformed) :
    (restrict_length g).Derives (embed_string u) (embed_string v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | step hp _ ih =>
    exact CNF.Derives.trans (restrict_length_produces_derives hp hg) ih

theorem restrict_length_correct [DecidableEq T] [eq : DecidableEq g.NT] (hg : g.Wellformed) :
    g.language = (restrict_length g).language := by
  unfold language CNF.language
  apply Set.eq_of_subset_of_subset
  · intro w h'
    unfold Generates at h'
    unfold CNF.Generates
    apply implies_restrict_length at h'
    rw [embed_string_nonterminal, embed_string_terminals] at h'
    exact h' hg
  · intro w h
    unfold Generates
    unfold CNF.Generates at h
    simp at h ⊢
    apply restrict_length_implies at h
    unfold restrict_length at h
    simp at h
    rw [project_string_nonterminal, project_string_terminals] at h
    exact h

end CorrectnessProof

end ContextFreeGrammar
