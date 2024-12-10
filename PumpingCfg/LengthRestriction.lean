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
  | terminal {n : N} {t : T} : Wellformed (ContextFreeRule.mk n [Symbol.terminal t])
  /- Rule rewriting to mulitple nonterminals is wellformed -/
  | nonterminals {n: N} (u : List (Symbol T N)) (hleu : 2 ≤ u.length)
      (hu : ∀ s ∈ u, match s with | Symbol.nonterminal _ => True | _ => False) :
      Wellformed (ContextFreeRule.mk n u)

lemma only_nonterminals {u : List (Symbol T N)}
    (hu : ∀ s ∈ u, match s with | Symbol.nonterminal _ => True | _ => False) :
    ∃ v : List N, v.map Symbol.nonterminal = u := by
  induction u with
  | nil => use []; rfl
  | cons a _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hu
    obtain ⟨u', hu'⟩ := ih hu.2
    cases a
    · simp at hu
    · rename_i n
      use n :: u'
      simp only [List.map_cons, List.cons.injEq, true_and]
      exact hu'

lemma Wellformed.mem_nonterminal {r : ContextFreeRule T N} (hr : r.Wellformed)
    (i : Fin r.output.length) (h : 2 ≤ r.output.length) :
    ∃ n, r.output[i] = Symbol.nonterminal n := by
  induction hr with
  | terminal => simp at h
  | nonterminals u _ hu =>
    simp only [Fin.getElem_fin] at i ⊢
    specialize hu (u[i]'i.2) (u.get_mem i)
    revert hu; split <;> rename_i n huin <;> intro
    · use n
      exact huin
    · contradiction

lemma Wellformed.cases {r : ContextFreeRule T N} (h : r.Wellformed) :
    (∃ t : T, r.output = [Symbol.terminal t])
    ∨ (∃ (n₁ n₂ : N) (u : List N), r.output = Symbol.nonterminal n₁ :: Symbol.nonterminal n₂
      :: u.map Symbol.nonterminal) := by
  induction h with
  | @terminal _ t => left; use t
  | nonterminals u _ hu =>
    match u with
    | [] => contradiction
    | [x] => contradiction
    | .terminal t :: _ :: _ => specialize hu (Symbol.terminal t); simp at hu
    | _ :: .terminal t :: _ => specialize hu (Symbol.terminal t); simp at hu
    | .nonterminal n₁ :: .nonterminal n₂ :: u =>
      right
      simp only [List.mem_cons, forall_eq_or_imp, true_and] at hu
      obtain ⟨u', huu⟩ := only_nonterminals hu
      use n₁, n₂, u'
      simp [huu.symm]

end ContextFreeRule

namespace ContextFreeGrammar

-- **************************************************************************************** --
-- ********************************** Length Restriction ********************************** --
-- **************************************************************************************** --
section RestrictLength

variable {g : ContextFreeGrammar.{uN, uT} T}

abbrev NT' := g.NT ⊕ Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)

def compute_rules_rec (r : ContextFreeRule T g.NT) (i : Fin (r.output.length - 2)) :
    List (ChomskyNormalFormRule T g.NT') :=
  match i with
  | ⟨0, p⟩ => match r.output.get ⟨r.output.length - 2, by omega⟩,
               r.output.get ⟨r.output.length - 1, by omega⟩ with
             | Symbol.nonterminal n₁, Symbol.nonterminal n₂ =>
               [(ChomskyNormalFormRule.node (Sum.inr ⟨r, ⟨0, p⟩⟩) (Sum.inl n₁) (Sum.inl n₂))]
             | _, _ => []
  | ⟨n + 1, p⟩ => match r.output.get ⟨r.output.length - 2 - i.val, by omega⟩ with
                 | Symbol.nonterminal nt =>
                   (ChomskyNormalFormRule.node (Sum.inr ⟨r, ⟨i.val,by omega⟩⟩) (Sum.inl nt)
                     (Sum.inr ⟨r, ⟨n,by omega⟩⟩))
                   :: compute_rules_rec r ⟨n, by omega⟩
                 | _ => []

def compute_rules (r : ContextFreeRule T g.NT) : List (ChomskyNormalFormRule T g.NT') :=
  match h : r.output with
  | [Symbol.nonterminal n₁, Symbol.nonterminal n₂] =>
      [ChomskyNormalFormRule.node (Sum.inl r.input) (Sum.inl n₁) (Sum.inl n₂)]
  | [Symbol.terminal t] => [ChomskyNormalFormRule.leaf (Sum.inl r.input) t]
  | Symbol.nonterminal n :: _ :: _ :: _ =>
    (ChomskyNormalFormRule.node (Sum.inl r.input) (Sum.inl n)
      (Sum.inr ⟨r, ⟨r.output.length - 3, by rw [h]; simp⟩⟩))
      :: compute_rules_rec r ⟨r.output.length - 3, by rw [h]; simp⟩
  | _ => []

def restrict_length_rules [DecidableEq T] [DecidableEq g.NT] (l : List (ContextFreeRule T g.NT)) :=
  (l.map compute_rules).flatten.toFinset

end RestrictLength

noncomputable def restrict_length (g : ContextFreeGrammar.{uN,uT} T) [DecidableEq T]
    [e : DecidableEq g.NT] :=
  ChomskyNormalFormGrammar.mk g.NT' (Sum.inl g.initial) (restrict_length_rules g.rules.toList)

def Wellformed (g : ContextFreeGrammar T) : Prop := ∀ r ∈ g.rules, r.Wellformed

section EmbedProject

variable {g : ContextFreeGrammar.{uN, uT} T}

def embed_symbol (s : Symbol T g.NT) : Symbol T g.NT' :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

lemma embed_symbol_nonterminal {n : g.NT} :
    embed_symbol (Symbol.nonterminal n) = Symbol.nonterminal (Sum.inl n) := by rfl

lemma embed_symbol_terminal {t : T} :
    embed_symbol (Symbol.terminal t) = (@Symbol.terminal T g.NT') t := by rfl

abbrev embed_string (u : List (Symbol T g.NT)) : List (Symbol T g.NT') := u.map embed_symbol

lemma embed_string_nonterminal {n : g.NT} :
    embed_string [Symbol.nonterminal n] = [Symbol.nonterminal (Sum.inl n)] := by rfl

lemma embed_string_terminals {u : List T} :
    embed_string (List.map Symbol.terminal u) = List.map (@Symbol.terminal T g.NT') u := by
  induction u with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.map_map, List.map_inj_left, Function.comp_apply, List.map_cons, List.cons.injEq]
      at ih ⊢
    exact ⟨rfl, ih⟩

def embed_string_append {u v : List (Symbol T g.NT)} :
  embed_string (u ++ v) = embed_string u ++ embed_string v := List.map_append embed_symbol u v

def project_symbol (s : Symbol T g.NT') : List (Symbol T g.NT) :=
  match s with
  | Symbol.terminal t => [Symbol.terminal t]
  | Symbol.nonterminal (Sum.inl n) => [Symbol.nonterminal n]
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
    simp only [List.map_map, List.map_cons, List.flatten_cons] at ih ⊢
    rw [← List.singleton_append, ih]
    congr
    cases hd <;> rfl

lemma project_string_nonterminal {n : g.NT} :
    project_string [Symbol.nonterminal (Sum.inl n)] = [Symbol.nonterminal n] := by
  simp [project_string, project_symbol]

@[simp]
lemma project_symbol_terminal {t : T} :
    project_symbol (@Symbol.terminal T g.NT' t) = [Symbol.terminal t] := by simp [project_symbol]

lemma project_string_terminals {u : List T} :
    project_string (List.map (@Symbol.terminal T g.NT') u) = List.map Symbol.terminal u := by
  induction u with
  | nil => rfl
  | cons =>
    rw [←List.singleton_append, List.map_append, List.map_append, project_string_append]
    congr

end EmbedProject

-- ******************************************************************** --
-- Only If direction of the main correctness theorem of restrict_length --
-- ******************************************************************** --

section CorrectnessProof

variable {g : ContextFreeGrammar.{uN, uT} T}

lemma compute_rules_rec_project {r : ContextFreeRule T g.NT} {i : Fin (r.output.length - 2)}
    {r' : ChomskyNormalFormRule T g.NT'} (hrri : r' ∈ compute_rules_rec r i) :
    project_string r'.output = project_string [Symbol.nonterminal r'.input] := by
  obtain ⟨m, _⟩ := i
  induction m with
  | zero =>
    simp only [compute_rules_rec, List.get_eq_getElem] at hrri
    revert hrri
    split <;> intro hrri <;> simp at hrri
    · rename_i n₁ n₂ hn₁ hn₂
      rw [hrri, ChomskyNormalFormRule.input, ChomskyNormalFormRule.output]
      simp only [project_string, project_symbol, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.singleton_append, Nat.sub_zero, List.append_nil]
      rw [List.drop_eq_getElem_cons, List.drop_eq_getElem_cons]
      swap; omega
      swap; omega
      congr
      · rw [← hn₁]
      · rw [← hn₂]
        congr
        omega
      · simp only [List.nil_eq, List.drop_eq_nil_iff]
        omega
  | succ _ ih =>
    simp only [compute_rules_rec, List.get_eq_getElem] at hrri
    revert hrri
    split <;> intro hrri <;>
      simp only [Nat.succ_eq_add_one, List.mem_cons, List.not_mem_nil] at hrri
    cases hrri <;> rename_i heq hrri
    · rw [hrri]
      simp only [ChomskyNormalFormRule.input, ChomskyNormalFormRule.output, project_string,
        project_symbol, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.singleton_append]
      nth_rewrite 2 [List.drop_eq_getElem_cons]
      congr
      exact heq.symm
      omega
    · exact ih _ hrri

lemma compute_rules_rec_inl {n : g.NT} {r : ContextFreeRule T g.NT}
    {r' : ChomskyNormalFormRule T g.NT'} {i : Fin (r.output.length - 2)}
    (hrn : r'.input = Sum.inl n) :
    r' ∉ compute_rules_rec r i := by
  obtain ⟨m, _⟩ := i
  induction m with
  | zero =>
    unfold compute_rules_rec
    split
    · simp only [List.mem_singleton, ne_eq]
      intro h
      rw [h] at hrn
      simp at hrn
    · exact List.not_mem_nil r'
  | succ _ ih =>
    unfold compute_rules_rec
    split
    · simp only [List.mem_cons, not_or, ne_eq]
      constructor
      · intro h
        rw [h] at hrn
        simp at hrn
      · apply ih
    · exact List.not_mem_nil r'

lemma compute_rules_inr_length {n : Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)}
    {r : ContextFreeRule T g.NT} {r' : ChomskyNormalFormRule T g.NT'} (hrr : r' ∈ compute_rules r)
    (hrn : r'.input = Sum.inr n) :
    3 ≤ r.output.length := by
  unfold compute_rules at hrr
  revert hrr
  split <;> intro hrr <;> simp at hrr
  · rw [hrr] at hrn; simp at hrn
  · rw [hrr] at hrn; simp at hrn
  · cases hrr <;> rename_i hrn _
    · rw[hrn]; simp
    · rw [hrn]; simp

lemma compute_rules_inr_in_rec {n : Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)}
    {r : ContextFreeRule T g.NT} {r' : ChomskyNormalFormRule T g.NT'}
    (hrₒ : r.output.length - 3 < r.output.length - 2) (hrr : r' ∈ compute_rules r)
    (hrn : r'.input = Sum.inr n) :
    r' ∈ compute_rules_rec r ⟨r.output.length - 3, hrₒ⟩ := by
  unfold compute_rules at hrr
  revert hrr
  split <;> intro hrr <;> simp at hrr
  · rw [hrr] at hrn; simp at hrn
  · rw [hrr] at hrn; simp at hrn
  · cases hrr <;> rename_i hrr
    · rw [hrr] at hrn; simp at hrn
    · exact hrr

lemma compute_rules_inl {n : g.NT} {r : ContextFreeRule T g.NT} {r' : ChomskyNormalFormRule T g.NT'}
    (hrr : r' ∈ compute_rules r) (hrn : r'.input = Sum.inl n) :
    project_string r'.output = r.output ∧ n = r.input := by
  unfold compute_rules at hrr
  revert hrr
  split <;> intro hrr
  · rename_i n₁ n₂ hrnn
    rw [List.mem_singleton] at hrr
    rw [hrr, hrnn]
    rw[hrr] at hrn
    simp only [project_string, project_symbol, ChomskyNormalFormRule.input, Sum.inl.injEq,
      ChomskyNormalFormRule.output, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.singleton_append, true_and] at hrn ⊢
    exact hrn.symm
  · rename_i t heq2
    rw [List.mem_singleton] at hrr
    rw [hrr, heq2]
    rw[hrr] at hrn
    simp only [project_string, project_symbol, ChomskyNormalFormRule.input, Sum.inl.injEq,
      ChomskyNormalFormRule.output, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.singleton_append, true_and] at hrn ⊢
    exact hrn.symm
  · rw [List.mem_cons] at hrr
    cases hrr <;> rename_i heq2 hrr
    · constructor
      · rw [hrr]
        simp only [ChomskyNormalFormRule.output]
        rw [← List.singleton_append, project_string_append]
        simp only [project_string, project_symbol, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.singleton_append, List.append_nil]
        rw [heq2]
        congr
        simp
      · rw [hrr] at hrn
        simp only [ChomskyNormalFormRule.input, Sum.inl.injEq] at hrn
        exact hrn.symm
    · exfalso
      exact compute_rules_rec_inl hrn hrr
  · contradiction

lemma restrict_length_produces_implies {u v : List (Symbol T g.NT')} [DecidableEq T]
    [DecidableEq g.NT] (huv : (restrict_length g).Produces u v) :
    g.Derives (project_string u) (project_string v) := by
  obtain ⟨r, hrg, huv⟩ := huv
  obtain ⟨_, _, hu, hv⟩ := huv.exists_parts
  simp only [restrict_length] at r hrg
  rw [hu, hv]
  repeat rw[project_string_append]
  apply Derives.append_right
  apply Derives.append_left
  simp only [restrict_length_rules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, exists_exists_and_eq_and] at hrg
  obtain ⟨r', hrg', hrr⟩ := hrg
  cases h : r.input with
  | inl nt =>
    obtain ⟨heqo, heqi⟩ := compute_rules_inl hrr h
    rw [heqo, heqi]
    simp only [project_string, project_symbol, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.singleton_append]
    exact Produces.single (rewrites_produces hrg')
  | inr =>
    rw [compute_rules_rec_project, h]
    exact compute_rules_inr_in_rec
      (Nat.sub_lt_sub_left (compute_rules_inr_length hrr h) (Nat.lt_add_one 2)) hrr h

lemma restrict_length_implies {u v : List (Symbol T g.NT')} [DecidableEq T] [DecidableEq g.NT]
    (huv : (restrict_length g).Derives u v) :
    g.Derives (project_string u) (project_string v) := by
  induction huv using ChomskyNormalFormGrammar.Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih => exact Derives.trans (restrict_length_produces_implies hp) ih

-- *************************************************************** --
-- If direction of the main correctness theorem of restrict_length --
-- *************************************************************** --

lemma compute_rules_rec_derives [DecidableEq T] [DecidableEq g.NT] {r : ContextFreeRule T g.NT}
    {i : Fin (r.output.length - 2)} {n : g.NT'} {x : List (ChomskyNormalFormRule T g.NT')}
    (hrix : compute_rules_rec r i ⊆ x) (hr : r.Wellformed) :
    (ChomskyNormalFormGrammar.mk g.NT' n x.toFinset).Derives
      [Symbol.nonterminal (Sum.inr ⟨r, i⟩)]
      (embed_string (List.drop (r.output.length - 2 - i) r.output)) := by
  obtain ⟨n, p⟩ := i
  induction n with
  | zero =>
    unfold compute_rules_rec at hrix
    simp only [List.get_eq_getElem, Nat.sub_zero, List.map_drop] at hrix ⊢
    revert hrix
    split <;> intro hrix
    · rename_i n₁ n₂ hrn₁ hrn₂
      have heq : (List.drop (r.output.length - 2) (List.map embed_symbol r.output))
          = embed_string [Symbol.nonterminal n₁, Symbol.nonterminal n₂] := by
        have hrₒ : r.output.length - 2 + 1 + 1 = r.output.length := by omega
        rw [← List.map_drop, ← List.getElem_cons_drop_succ_eq_drop,
          ← List.getElem_cons_drop_succ_eq_drop]
        rw [hrₒ, List.drop_length, hrn₁]
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, true_and]
        congr
        rw [← hrn₂]
        congr
        omega
        omega
      rw [heq]
      simp only [List.map_cons, List.map_nil]
      rw [embed_symbol_nonterminal, embed_symbol_nonterminal]
      apply ChomskyNormalFormGrammar.Produces.single
      constructor
      · constructor
        · simp only [List.cons_subset, List.nil_subset, and_true, List.mem_toFinset] at hrix ⊢
          exact hrix
        · exact ChomskyNormalFormRule.Rewrites.input_output
    · rename_i hn
      exfalso
      obtain ⟨n₁, h1⟩ := hr.mem_nonterminal ⟨r.output.length - 2, by omega⟩ (by omega)
      obtain ⟨n₂, h2⟩ := hr.mem_nonterminal ⟨r.output.length - 1, by omega⟩ (by omega)
      exact hn _ _ h1 h2
  | succ n ih =>
    unfold compute_rules_rec at hrix
    revert hrix
    split <;> intro hrix
    · rename_i _ hrn
      simp only [List.cons_subset, List.get_eq_getElem] at hrix hrn
      obtain ⟨hx₁, hx₂⟩ := hrix
      rw [← List.getElem_cons_drop_succ_eq_drop, hrn]
      apply ChomskyNormalFormGrammar.Produces.trans_derives
      · constructor
        · constructor
          · simp only [List.mem_toFinset]
            exact hx₁
          · exact ChomskyNormalFormRule.Rewrites.input_output
      · simp only [ChomskyNormalFormRule.output, List.map_cons, List.map_drop]
        rw [←List.singleton_append, ←List.singleton_append, embed_symbol_nonterminal, ←List.map_drop]
        apply ChomskyNormalFormGrammar.Derives.append_left
        have hrₒ : r.output.length - 2 - (n + 1) +1 = r.output.length - 2 - n := by omega
        rw [hrₒ]
        exact ih _ hx₂
    · rename_i hn
      obtain ⟨n₁, hn₁⟩ := hr.mem_nonterminal ⟨r.output.length - 2 - (n + 1), by omega⟩ (by omega)
      simp only [Fin.getElem_fin, List.map_drop] at hn₁ ⊢
      exfalso
      apply hn _ hn₁

lemma compute_rules_derives_embed_output [DecidableEq T] [DecidableEq g.NT]
    {r : ContextFreeRule T g.NT} {n : g.NT'} {x : List (ChomskyNormalFormRule T g.NT')}
    (hrx : compute_rules r ⊆ x) (hr : r.Wellformed) :
    (ChomskyNormalFormGrammar.mk g.NT' n x.toFinset).Derives [Symbol.nonterminal (Sum.inl r.input)]
      (embed_string r.output) := by
  unfold compute_rules at hrx
  revert hrx
  split <;> intro hrx <;> rename_i hrn
  · rename_i n₁ n₂
    simp only [List.cons_subset, List.nil_subset, and_true] at hrx
    apply ChomskyNormalFormGrammar.Produces.single
    constructor
    · constructor
      · rwa [List.mem_toFinset]
      · rw [hrn]
        unfold embed_string
        simp only [List.map_cons, List.map_nil]
        rw [embed_symbol_nonterminal, embed_symbol_nonterminal]
        exact ChomskyNormalFormRule.Rewrites.input_output
  · rename_i t
    simp only [List.cons_subset, List.nil_subset, and_true] at hrx
    apply ChomskyNormalFormGrammar.Produces.single
    constructor
    · constructor
      · rwa [List.mem_toFinset]
      · rw [hrn]
        simp only [embed_string, List.map_cons, List.map_nil]
        rw [embed_symbol_terminal]
        exact ChomskyNormalFormRule.Rewrites.input_output
  · rename_i n' s₁ s₂ u
    simp only [List.cons_subset] at hrx
    obtain ⟨hx₁, hx₂⟩ := hrx
    apply ChomskyNormalFormGrammar.Produces.trans_derives
    · constructor
      · constructor
        · rwa [List.mem_toFinset]
        · exact ChomskyNormalFormRule.Rewrites.input_output
    · nth_rewrite 4 [hrn]
      simp only [ChomskyNormalFormRule.output, List.map_cons]
      rw [← List.singleton_append, ← (@List.singleton_append _ (embed_symbol _)),
           embed_symbol_nonterminal]
      apply ChomskyNormalFormGrammar.Derives.append_left
      have heq :
        (embed_symbol s₁ :: embed_symbol s₂ :: List.map embed_symbol u =
          embed_string (List.drop (r.output.length - 2 - (r.output.length - 3)) r.output)) := by
        change (embed_string (s₁ :: s₂ :: u) = _)
        congr
        rw [hrn]
        simp
      rw [heq]
      exact compute_rules_rec_derives hx₂ hr
  · rename_i h1 h2
    obtain (⟨t, heq⟩ | ⟨n₁, n₂, u, h⟩) := hr.cases
    · exfalso; exact h2 t heq
    · exfalso
      cases u
      · exfalso; exact h1 n₁ n₂ h
      · exfalso
        exact hrn _ _ _ _ h

lemma restrict_length_produces_derives [DecidableEq T] [DecidableEq g.NT]
    {u v : List (Symbol T g.NT)} (huv : g.Produces u v) (hg : g.Wellformed) :
    (restrict_length g).Derives (embed_string u) (embed_string v) := by
  obtain ⟨r, hrg, hr⟩ := huv
  obtain ⟨_,_, hu, hv⟩ := hr.exists_parts
  rw[hu, hv]
  repeat rw [embed_string_append]
  apply ChomskyNormalFormGrammar.Derives.append_right
  apply ChomskyNormalFormGrammar.Derives.append_left
  rw [embed_string_nonterminal]
  apply compute_rules_derives_embed_output _ (hg _ hrg)
  intro r' hrin'
  simp only [List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and]
  use r

lemma implies_restrict_length [DecidableEq T] [DecidableEq g.NT] {u v : List (Symbol T g.NT)}
    (huv : g.Derives u v) (hg : g.Wellformed) :
    (restrict_length g).Derives (embed_string u) (embed_string v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    exact ChomskyNormalFormGrammar.Derives.trans (restrict_length_produces_derives hp hg) ih

theorem restrict_length_correct [DecidableEq T] [e : DecidableEq g.NT] (hg : g.Wellformed) :
    g.language = (restrict_length g).language := by
  apply Set.eq_of_subset_of_subset
  · intro w h'
    apply implies_restrict_length at h'
    rw [embed_string_nonterminal, embed_string_terminals] at h'
    exact h' hg
  · intro w h
    apply restrict_length_implies at h
    simp only [restrict_length] at h
    rw [project_string_nonterminal, project_string_terminals] at h
    exact h

end CorrectnessProof

end ContextFreeGrammar
