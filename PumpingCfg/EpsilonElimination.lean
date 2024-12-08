/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.Utils
import PumpingCfg.CountingSteps

namespace ContextFreeGrammar

universe uT uN
variable {T : Type uT}

/-! Properties of context-free transformations to the empty string -/
section NullableDerivations

variable {g : ContextFreeGrammar.{uN, uT} T}

abbrev NullableNonTerminal (v : g.NT) : Prop := g.Derives [Symbol.nonterminal v] []

abbrev NullableWord (w : List (Symbol T g.NT)) : Prop := g.Derives w []

private lemma DerivesIn.empty_of_append_left_aux {u v w : List (Symbol T g.NT)} {n : ℕ}
    (hwe : g.DerivesIn w [] n) (hw : w = u ++ v) :
    ∃ m ≤ n, g.DerivesIn u [] m := by
  induction hwe using DerivesIn.head_induction_on generalizing u v with
  | refl =>
    rw [List.nil_eq_append_iff] at hw
    rw [hw.left]
    exact ⟨0, Nat.le_refl 0, DerivesIn.zero_steps []⟩
  | head huv _ ih =>
    obtain ⟨r, hrg, hr⟩ := huv
    obtain ⟨p, q, heq₁, heq₂⟩ := ContextFreeRule.Rewrites.exists_parts hr
    rw [hw, List.append_assoc, List.append_eq_append_iff] at heq₁
    cases heq₁ with
    | inl hpv =>
      obtain ⟨x', hp, _⟩ := hpv
      obtain ⟨m, _, _⟩ := @ih u (x' ++ r.output ++ q) (by simp [heq₂, hp])
      use m
      tauto
    | inr huq =>
      obtain ⟨x', hu, hr⟩ := huq
      cases x' with
      | nil =>
        obtain ⟨m, _, _⟩ := @ih u (r.output ++ q) (by simp [heq₂, hu])
        use m
        tauto
      | cons h t =>
        obtain ⟨_, _⟩ := hr
        rw [List.append_eq, ←List.append_assoc] at heq₂
        obtain ⟨m, hm, hd⟩ := ih heq₂
        refine ⟨m.succ, Nat.succ_le_succ hm, Produces.trans_derivesIn ⟨r, hrg, ?_⟩ hd⟩
        rw [ContextFreeRule.rewrites_iff]
        exact ⟨p, t, List.append_assoc .. ▸ hu, rfl⟩

lemma DerivesIn.empty_of_append_left {n : ℕ} {u v : List (Symbol T g.NT)}
    (huv : g.DerivesIn (u ++ v) [] n) :
    ∃ m ≤ n, g.DerivesIn u [] m := by
  apply empty_of_append_left_aux <;> tauto

lemma DerivesIn.empty_of_append_right_aux {u v w : List (Symbol T g.NT)} {n : ℕ}
    (hwn : g.DerivesIn w [] n) (hw : w = u ++ v) :
    ∃ m ≤ n, g.DerivesIn v [] m := by
  induction hwn using DerivesIn.head_induction_on generalizing u v with
  | refl =>
    rw [List.nil_eq_append_iff] at hw
    rw [hw.right]
    exact ⟨0, Nat.le_refl 0, DerivesIn.zero_steps []⟩
  | head hp _ ih =>
    obtain ⟨r, hrg, hr⟩ := hp
    obtain ⟨p, q, heq₁, heq₂⟩ := hr.exists_parts
    rw [hw, List.append_assoc, List.append_eq_append_iff] at heq₁
    cases heq₁ with
    | inl hpv =>
      obtain ⟨y', heq₁ , hy⟩ := hpv
      rw [heq₁, List.append_assoc, List.append_assoc] at heq₂
      obtain ⟨m', hm, hd⟩ := ih heq₂
      refine ⟨m'.succ, Nat.succ_le_succ hm, ?_⟩
      apply Produces.trans_derivesIn
      · use r, hrg
        rw [ContextFreeRule.rewrites_iff]
        exact ⟨y', q, List.append_assoc .. ▸ hy, rfl⟩
      · simp [hd]
    | inr huq =>
      obtain ⟨q', _, hq⟩ := huq
      cases q' with
      | nil =>
        rw [List.append_assoc] at heq₂
        rw [List.singleton_append, List.nil_append] at hq
        obtain ⟨m', hm, hd⟩ := ih heq₂
        use m'.succ, Nat.succ_le_succ hm
        apply Produces.trans_derivesIn _ hd
        use r, hrg
        rw [ContextFreeRule.rewrites_iff]
        exact ⟨[], q, hq.symm, rfl⟩
      | cons _ t =>
        obtain ⟨_, _⟩ := hq
        rw [List.append_eq, List.append_assoc] at heq₂
        repeat rw [←List.append_assoc] at heq₂
        obtain ⟨m', hm, hd⟩ := ih heq₂
        exact ⟨m', Nat.le_succ_of_le hm, hd⟩

lemma DerivesIn.empty_of_append_right {n : ℕ} {u v : List (Symbol T g.NT)}
    (huv : g.DerivesIn (u ++ v) [] n) :
    ∃ m ≤ n, g.DerivesIn v [] m := by
  apply empty_of_append_right_aux <;> tauto

lemma DerivesIn.empty_of_append {u v w : List (Symbol T g.NT)} {n : ℕ}
    (huvwe : g.DerivesIn (u ++ v ++ w) [] n) :
    ∃ m ≤ n, g.DerivesIn v [] m := by
  obtain ⟨m₁, hm₁n, huve⟩ := huvwe.empty_of_append_left
  obtain ⟨m₂, hm₂n, hve⟩ := huve.empty_of_append_right
  exact ⟨m₂, Nat.le_trans hm₂n hm₁n, hve⟩

lemma NullableWord.empty_of_append {u v w : List (Symbol T g.NT)}
    (huvw : NullableWord (u ++ v ++ w)) :
    NullableWord v := by
  unfold NullableWord at *
  rw [derives_iff_derivesIn] at huvw ⊢
  obtain ⟨n, hn⟩ := huvw
  obtain ⟨m, _, _⟩ := hn.empty_of_append
  use m

lemma NullableWord.empty_of_append_left {u v : List (Symbol T g.NT)} (huv : NullableWord (u ++ v)) :
    NullableWord u :=
  @NullableWord.empty_of_append _ _ [] _ _ huv

lemma NullableWord.empty_of_append_right {u v : List (Symbol T g.NT)}
    (huv : NullableWord (u ++ v)): NullableWord v := by
  apply NullableWord.empty_of_append
  rw [List.append_nil]
  exact huv

lemma DerivesIn.mem_nullable {u : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ}
    (hu : g.DerivesIn u [] n) (hsu : s ∈ u) :
    ∃ m ≤ n, g.DerivesIn [s] [] m := by
  induction u generalizing n with
  | nil => contradiction
  | cons v t ih =>
    cases hsu with
    | head =>
      exact hu.empty_of_append_left
    | tail _ hs =>
      change g.DerivesIn ([v] ++ t) [] n at hu
      obtain ⟨m, hmn, hte⟩ := hu.empty_of_append_right
      obtain ⟨m', hmm, hse⟩ := ih hte hs
      exact ⟨m', hmm.trans hmn, hse⟩

lemma rewrites_empty_output {u : List (Symbol T g.NT)} {r : ContextFreeRule T g.NT}
    (hue : r.Rewrites u []) :
    r.output = [] := by
  obtain ⟨_, _, -, _⟩ := hue.exists_parts
  simp_all

lemma Derives.append_left_trans {u v w x: List (Symbol T g.NT)} (huv : g.Derives u v)
    (hwx : g.Derives w x) :
    g.Derives (w ++ u) (x ++ v) :=
  (huv.append_left _).trans (hwx.append_right _)

lemma rewrites_produces {r : ContextFreeRule T g.NT} (hrg : r ∈ g.rules) :
    g.Produces [.nonterminal r.input] r.output :=
  ⟨r, hrg, ContextFreeRule.Rewrites.input_output⟩

lemma nullable_not_terminal {t : T} {u : List (Symbol T g.NT)} :
    ¬ NullableWord (Symbol.terminal t :: u) := by
  by_contra htu
  change g.Derives ([Symbol.terminal t] ++ u) [] at htu
  cases (NullableWord.empty_of_append_left htu).eq_or_head with
  | inl => contradiction
  | inr hv =>
    obtain ⟨_, ⟨_, _, ht⟩, _⟩ := hv
    cases ht with
    | cons _ hts =>
      cases hts

lemma Derives.empty_empty {u : List (Symbol T g.NT)} (hu : g.Derives [] u) : u = [] := by
  induction hu with
  | refl => rfl
  | tail _ hp _ =>
    obtain ⟨r, _, hr⟩ := hp
    cases hr <;> contradiction

lemma symbols_nullable_nullableWord (u : List (Symbol T g.NT)) (hu : ∀ a ∈ u, g.Derives [a] []) :
    NullableWord u := by
  induction u with
  | nil => rfl
  | cons d l ih =>
    show g.Derives ([d] ++ l) []
    trans
    · apply Derives.append_right
      apply hu
      exact List.mem_cons_self d l
    · apply ih
      intro v hv
      apply hu
      right
      exact hv

lemma DerivesIn.nullable_mem_nonterminal {u : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ}
    (hu : g.DerivesIn u [] n) (hsu : s ∈ u) :
    ∃ v, s = Symbol.nonterminal v := by
  have ⟨m, _, hsm⟩ := hu.mem_nullable hsu
  cases m with
  | zero =>
    contradiction
  | succ m =>
    obtain ⟨u, hwu, _⟩ := hsm.head_of_succ
    obtain ⟨r, _, hsu⟩ := hwu
    obtain ⟨p, q, hs, -⟩ := hsu.exists_parts
    cases p <;> simp at hs
    cases q <;> simp at hs
    use r.input

lemma NullableWord.nullableNonTerminal {u : List (Symbol T g.NT)} {s : Symbol T g.NT}
    (hu : NullableWord u) (hsu : s ∈ u) :
    ∃ x, s = Symbol.nonterminal x ∧ NullableNonTerminal x := by
  induction u generalizing s with
  | nil => contradiction
  | cons a u ih =>
    cases hsu with
    | head =>
      cases a with
      | terminal => exact (nullable_not_terminal hu).elim
      | nonterminal n => exact ⟨n, rfl, hu.empty_of_append_left⟩
    | tail _ hsu =>
      apply ih _ hsu
      apply NullableWord.empty_of_append_right
      change NullableWord ([a] ++ u) at hu
      exact hu

end NullableDerivations


section NullableRelated

variable {g : ContextFreeGrammar.{uN, uT} T}

/-- `NullableRelated u v` means that `v` and `u` are equal up to interspersed nonterminals, each of
 which can be transformed to the empty string (i.e. for each additional nonterminal `nt`,
 `NullableNonterminal nt` holds) -/
inductive NullableRelated : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop where
  /- The empty string is `NullableRelated` to any `w`, s.t., `NullableWord w`-/
  | empty_left (u : List (Symbol T g.NT)) (hu : NullableWord u) : NullableRelated [] u
  /- A terminal symbol `t` needs to be matched exactly -/
  | cons_term {u v : List (Symbol T g.NT)} (huv : NullableRelated u v) (t : T) :
                      NullableRelated (Symbol.terminal t :: u) (Symbol.terminal t :: v)
  /- A nonterminal symbol `nt` can be matched exactly -/
  | cons_nterm_match {u v : List (Symbol T g.NT)} (huv : NullableRelated u v) (n : g.NT) :
                     NullableRelated (Symbol.nonterminal n :: u) (Symbol.nonterminal n :: v)
  /- A nonterminal symbol `nt`, s.t., `NullableNonterminal nt` on the right, need not be matched -/
  | cons_nterm_nullable {u v : List (Symbol T g.NT)} (huv : NullableRelated u v) {n : g.NT}
                        (hn : NullableNonTerminal n) : NullableRelated u (Symbol.nonterminal n :: v)

@[refl]
lemma NullableRelated.refl (u : List (Symbol T g.NT)) : NullableRelated u u := by
  induction u with
  | nil =>
    constructor
    rfl
  | cons hd tl ih =>
    cases hd <;> constructor <;> exact ih

lemma NullableRelated.derives {u v : List (Symbol T g.NT)} (huv : NullableRelated u v) :
    g.Derives v u := by
  induction huv with
  | empty_left _ hw => exact hw
  | cons_term _ t ih => exact List.singleton_append .. ▸ ih.append_left _
  | cons_nterm_match _ _ ih =>
    nth_rewrite 2 [← List.singleton_append]
    rw [← List.singleton_append]
    exact ih.append_left _
  | cons_nterm_nullable _ hnt ih =>
    rw [← List.singleton_append]
    exact Derives.append_left_trans ih hnt

lemma NullableRelated.empty_nullable {u : List (Symbol T g.NT)} (hu : NullableRelated [] u) :
    NullableWord u := by
  induction u with
  | nil => rfl
  | cons s w ih => cases hu with
    | empty_left _ hsw => exact hsw
    | cons_nterm_nullable hw hn => exact (Derives.append_right hn w).trans (ih hw)

lemma NullableRelated.empty_empty {u : List (Symbol T g.NT)} (hu : NullableRelated u []) :
    u = [] := by
  cases hu
  rfl

lemma NullableRelated.append_nullable' {u v w : List (Symbol T g.NT)}
    (hvu : NullableRelated v u) (hw : NullableWord w) :
    NullableRelated v (w ++ u) := by
  induction w generalizing u v with
  | nil => rwa [List.nil_append]
  | cons s w ih =>
    change NullableWord ([s] ++ w) at hw
    obtain ⟨_, rfl, hnt⟩ := hw.nullableNonTerminal (List.mem_cons_self s w)
    constructor
    · exact ih hvu (NullableWord.empty_of_append_right hw)
    · exact hnt

lemma NullableRelated.append_nullable_left {u v w: List (Symbol T g.NT)}
    (huv : NullableRelated u v) (hw : NullableWord w) :
    NullableRelated u (w ++ v) := by
  induction w generalizing u v with
  | nil => exact huv
  | cons s w ih =>
    change NullableWord ([s] ++ w) at hw
    obtain ⟨_, rfl, hnt⟩ := hw.nullableNonTerminal (List.mem_cons_self s w)
    constructor
    · exact ih huv (NullableWord.empty_of_append_right hw)
    · exact hnt

lemma NullableRelated.append {u₁ u₂ v₁ v₂ : List (Symbol T g.NT)}
    (hv : NullableRelated v₁ v₂) (hu : NullableRelated u₁ u₂) :
    NullableRelated (v₁ ++ u₁) (v₂ ++ u₂) := by
  induction hv with
  | empty_left v₂ hv => exact hu.append_nullable_left hv
  | cons_term _ t ih => exact cons_term ih t
  | cons_nterm_match _ n ih => exact cons_nterm_match ih n
  | cons_nterm_nullable _ hnt ih => exact NullableRelated.cons_nterm_nullable ih hnt

-- TODO ? maybe easier to do (h : u = w1 ++ w2) and then induction on h. This is quite tedious
lemma NullableRelated.append_split {u v w : List (Symbol T g.NT)}
    (huvw : NullableRelated u (v ++ w)) :
    ∃ v' w', u = v' ++ w' ∧ NullableRelated v' v ∧ NullableRelated w' w := by
  induction v generalizing u w with
  | nil =>
    exact ⟨[], u, rfl, refl [], huvw⟩
  | cons s v ih =>
    cases u with
    | nil =>
      use [], []
      constructor; rfl
      have hvw : NullableRelated [] (v ++ w) := by
        constructor
        apply NullableWord.empty_of_append_right
        change NullableRelated [] ([s] ++ (v ++ w)) at huvw
        exact huvw.empty_nullable
      obtain ⟨v', w', hv'w', _, hnw'w⟩ := ih hvw
      simp at hv'w'
      constructor
      · constructor
        cases huvw
        · apply NullableWord.empty_of_append_left
          assumption
        · change NullableWord ([Symbol.nonterminal _] ++ v)
          apply Derives.trans
          · apply Derives.append_right
            assumption
          · exact hvw.empty_nullable.empty_of_append_left
      · exact hv'w'.right ▸ hnw'w
    | cons sᵤ u =>
      cases huvw with
      | cons_term huvw t =>
        obtain ⟨v', w', huv'w', hv'v, hw'w⟩ := ih huvw
        use (Symbol.terminal t :: v'), w'
        exact ⟨List.cons_eq_cons.2 ⟨rfl, huv'w'⟩, ⟨NullableRelated.cons_term hv'v t, hw'w⟩⟩
      | cons_nterm_match huvw n =>
        obtain ⟨v', w', huv'w', hv'v, hw'w⟩ := ih huvw
        use (Symbol.nonterminal n :: v'), w'
        exact ⟨List.cons_eq_cons.2 ⟨rfl, huv'w'⟩, ⟨NullableRelated.cons_nterm_match hv'v n, hw'w⟩⟩
      | cons_nterm_nullable huvw hnt =>
        obtain ⟨v', w', huv'w', hv'v, hw'w⟩ := ih huvw
        exact ⟨v', w', huv'w', cons_nterm_nullable hv'v hnt, hw'w⟩

lemma NullableRelated.append_split_three {u v w x : List (Symbol T g.NT)}
    (huvwx : NullableRelated u (v ++ w ++ x)) :
    ∃ u₁ u₂ u₃ : List (Symbol T g.NT),
      u = u₁ ++ u₂ ++ u₃ ∧ NullableRelated u₁ v ∧ NullableRelated u₂ w ∧ NullableRelated u₃ x := by
  obtain ⟨u', u₃, huu'u₃, hu'vw, hu₃x⟩ := huvwx.append_split
  obtain ⟨u₁, u₂, hu'u₁u₂, hu₁v, hu₂w⟩ := hu'vw.append_split
  exact ⟨u₁, u₂, u₃, hu'u₁u₂ ▸ huu'u₃, hu₁v, hu₂w, hu₃x⟩

end NullableRelated

-- *********************************************************************************************** --
-- ************************************** Nullable Symbols *************************************** --
-- *********************************************************************************************** --
section ComputeNullables

variable {N : Type uN} [DecidableEq N]

def symbol_is_nullable (nullable : Finset N) (s : Symbol T N) : Bool :=
  match s with
  | Symbol.terminal _ => False
  | Symbol.nonterminal n => n ∈ nullable

def rule_is_nullable (nullable : Finset N) (r : ContextFreeRule T N) : Bool :=
  ∀ s ∈ r.output, symbol_is_nullable nullable s

def add_if_nullable (r : ContextFreeRule T N) (nullable : Finset N) : Finset N :=
  if rule_is_nullable nullable r then insert r.input nullable else nullable

lemma add_if_nullable_subset (r : ContextFreeRule T N) (nullable : Finset N) :
  nullable ⊆ (add_if_nullable r nullable) := by
  unfold add_if_nullable
  split <;> simp

variable {g : ContextFreeGrammar.{uN, uT} T} [DecidableEq g.NT]

/- `generators g` is the set of all nonterminals that appear in the left hand side of rules of g -/
noncomputable def generators (g : ContextFreeGrammar.{uN, uT} T) [DecidableEq g.NT] : Finset g.NT :=
  (g.rules.toList.map (fun r ↦ r.input)).toFinset

lemma input_in_generators {r : ContextFreeRule T g.NT} (hrg : r ∈ g.rules) :
  r.input ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at hrg
  revert hrg
  induction g.rules.toList with
  | nil => simp
  | cons hd tl ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw [c1]
    · right
      exact ih c2

lemma nonterminal_in_generators {v : g.NT} {r : ContextFreeRule T g.NT} (hrg : r ∈ g.rules)
    (hv : r.input = v) :
    v ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at hrg
  revert hrg
  induction g.rules.toList with
  | nil => simp
  | cons d l ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw [← hv, c1]
    · right
      exact ih c2

lemma add_if_nullable_subset_generators {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
    (hsub : nullable ⊆ g.generators) (hrg : r ∈ g.rules) :
    add_if_nullable r nullable ⊆ g.generators := by
  unfold add_if_nullable
  split
  · exact Finset.insert_subset (input_in_generators hrg) hsub
  · exact hsub

/- Single round of fixpoint iteration; adds `r.input` to the set of nullable symbols if all symbols in
 `r.output` are nullable -/
noncomputable def add_nullables (nullable : Finset g.NT) : Finset g.NT :=
  g.rules.toList.attach.foldr (fun ⟨r, _⟩ ↦ add_if_nullable r) nullable

lemma add_nullables_sub_generators (nullable : Finset g.NT) (hsub : nullable ⊆ g.generators) :
    add_nullables nullable ⊆ g.generators := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil => simpa using hsub
  | cons d l ih => exact add_if_nullable_subset_generators ih (Finset.mem_toList.1 d.2)

lemma nullable_sub_add_nullables (nullable : Finset g.NT) : nullable ⊆ (add_nullables nullable) := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil => simp
  | cons hd tl ih =>
    apply subset_trans ih
    apply add_if_nullable_subset hd.1

-- Proof of our termination measure shrinking
lemma generators_limits_nullable (nullable : Finset g.NT) (hsub : nullable ⊆ g.generators)
    (hne : nullable ≠ add_nullables nullable) :
    (g.generators).card - (add_nullables nullable).card < (g.generators).card - nullable.card := by
  have h := HasSubset.Subset.ssubset_of_ne (nullable_sub_add_nullables nullable) hne
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_lt_of_le
    · apply Finset.card_lt_card h
    · exact Finset.card_le_card (add_nullables_sub_generators nullable hsub)
  · apply Finset.card_lt_card h

/- Fixpoint iteration computing the set of nullable symbols of `g`. -/
noncomputable def add_nullables_iter (nullable : Finset g.NT) (hsub : nullable ⊆ g.generators) :=
  let nullable' := add_nullables nullable
  if nullable = nullable' then
    nullable
  else
    add_nullables_iter nullable' (add_nullables_sub_generators nullable hsub)
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable hsub h

noncomputable def compute_nullables (g : ContextFreeGrammar.{uN, uT} T) [DecidableEq g.NT] :=
  add_nullables_iter ∅ g.generators.empty_subset

-- ********************************************************************** --
-- Only If direction of the main correctness theorem of compute_nullables --
-- ********************************************************************** --

lemma rule_is_nullable_correct (nullable : Finset g.NT) (r : ContextFreeRule T g.NT)
    (hrg : r ∈ g.rules) (hn : ∀ v ∈ nullable, NullableNonTerminal v)
    (hr : rule_is_nullable nullable r) :
    NullableNonTerminal r.input := by
  unfold rule_is_nullable at hr
  unfold NullableNonTerminal
  have h1 : g.Produces [Symbol.nonterminal r.input] r.output := by
    use r, hrg
    rw [ContextFreeRule.rewrites_iff]
    use [], []
    simp
  apply Produces.trans_derives h1
  apply symbols_nullable_nullableWord
  intro v hvin
  rw [decide_eq_true_eq] at hr
  specialize hr v hvin
  cases v <;> simp [symbol_is_nullable] at hr
  exact hn _ hr

lemma add_nullables_nullable (nullable : Finset g.NT) (hn : ∀ v ∈ nullable, NullableNonTerminal v) :
    ∀ v ∈ add_nullables nullable, NullableNonTerminal v := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil =>
    exact hn
  | cons d l ih =>
    simp only [List.foldr_cons, Finset.mem_toList, List.foldr_subtype, add_if_nullable]
    split <;> rename_i hd
    · simp only [Finset.mem_insert, forall_eq_or_imp]
      constructor
      · apply rule_is_nullable_correct _ _ (Finset.mem_toList.1 d.2) ih
        simpa using hd
      · simpa using ih
    · simpa using ih

-- Main correctness result of the only if direction
lemma add_nullables_iter_only_nullable (nullable : Finset g.NT)
    (hsub : nullable ⊆ g.generators) (hn : ∀ v ∈ nullable, NullableNonTerminal v) :
    ∀ v ∈ (add_nullables_iter nullable hsub), NullableNonTerminal v:= by
  unfold add_nullables_iter
  intro
  simp only
  split
  · tauto
  · apply add_nullables_iter_only_nullable (add_nullables nullable)
          (add_nullables_sub_generators nullable hsub)
          (add_nullables_nullable nullable hn)
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable hsub h

-- ***************************************************************** --
-- If direction of the main correctness theorem of compute_nullables --
-- ***************************************************************** --

lemma subset_add_if_nullable_subset {r: ContextFreeRule T g.NT} {nullable nullable' : Finset g.NT}
    (hsub : nullable ⊆ nullable') :
    add_if_nullable r nullable ⊆ add_if_nullable r nullable' := by
  intro v hvin
  unfold add_if_nullable rule_is_nullable at hvin ⊢
  by_cases hsr : decide (∀ s ∈ r.output, symbol_is_nullable nullable s) = true <;>
    simp [hsr] at hvin; simp at hsr
  · split <;> rename_i hsr'; simp at hsr'
    · cases hvin with
      | inl hvr =>
        rw [hvr]
        exact Finset.mem_insert_self r.input nullable'
      | inr hv =>
        exact Finset.mem_insert_of_mem (hsub hv)
    · cases hvin with
      | inl h'' =>
        unfold symbol_is_nullable at hsr' hsr
        simp at hsr' hsr -- TODO
        obtain ⟨s, hsin, hs⟩ := hsr'
        specialize hsr s
        cases s <;> simp at hs hsr
        · contradiction
        · rename_i u
          apply hsr at hsin
          apply hsub at hsin
          contradiction
      | inr h =>
        exact hsub h
  · split
    · exact Finset.mem_insert_of_mem (hsub hvin)
    · exact hsub hvin

private lemma add_if_nullable_subset_rec {rules : List (ContextFreeRule T g.NT)}
    {nullable : Finset g.NT} :
    nullable ⊆ List.foldr add_if_nullable nullable rules := by
  induction rules with
  | nil => rfl
  | cons _ _ ih =>
    simp
    apply Finset.Subset.trans ih
    apply add_if_nullable_subset

lemma nullable_in_add_nullables {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
    (hr : rule_is_nullable nullable r) (hrg : r ∈ g.rules) :
    r.input ∈ add_nullables nullable := by
  unfold add_nullables
  have hrg := List.mem_attach g.rules.toList ⟨r, (Finset.mem_toList.2 hrg)⟩
  revert r nullable
  induction g.rules.toList.attach with
  | nil =>
    intro r nullable _ hrg
    simp
  | cons r t ih =>
    intro r' nullable h hr' hr''
    cases hr'' <;> simp at ih ⊢
    · apply Finset.mem_of_subset (subset_add_if_nullable_subset add_if_nullable_subset_rec)
      simp [add_if_nullable, h]
    · rename_i hr''
      exact Finset.mem_of_subset (add_if_nullable_subset _ _) (ih h hr' hr'')

lemma add_nullable_add_nullable_iter (nullable: Finset g.NT) (hsub : nullable ⊆ g.generators) :
    add_nullables_iter nullable hsub = add_nullables (add_nullables_iter nullable hsub) := by
  unfold add_nullables_iter
  dsimp only
  split
  · assumption
  · apply add_nullable_add_nullable_iter
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable hsub h

lemma nullable_in_compute_nullables (nullable : Finset g.NT) (hsub : nullable ⊆ g.generators)
    (v : g.NT) (n : ℕ) (hgvn : g.DerivesIn [Symbol.nonterminal v] [] n) :
    v ∈ add_nullables_iter nullable hsub := by
  cases n with
  | zero =>
    cases hgvn
  | succ n =>
    obtain ⟨u, hwu, hue⟩ := hgvn.head_of_succ
    obtain ⟨r, hrg, hwu⟩ := hwu
    have hr : rule_is_nullable (add_nullables_iter nullable hsub) r := by
      have hur : u = r.output := by
        obtain ⟨p, q, hv, hu⟩ := hwu.exists_parts
        cases p <;> simp at hv
        cases q <;> simp at hv
        simpa using hu
      unfold rule_is_nullable
      rw [decide_eq_true_eq]
      intro s hs
      rw [←hur] at hs
      obtain ⟨v', hv'⟩ := hue.nullable_mem_nonterminal hs
      unfold symbol_is_nullable
      rw [hv', decide_eq_true_eq]
      have ⟨_, _, _⟩ := hue.mem_nullable hs
      apply nullable_in_compute_nullables
      rwa [←hv']
    have hv : v = r.input := by
      obtain ⟨p, q, hu, _⟩ := hwu.exists_parts
      cases p <;> simp at hu
      cases q <;> simp at hu
      exact hu
    rw [add_nullable_add_nullable_iter, hv]
    exact nullable_in_add_nullables hr hrg

-- Main correctness theorem of computing all nullable symbols --
lemma compute_nullables_iff (v : g.NT) : v ∈ compute_nullables g ↔ NullableNonTerminal v := by
  constructor
  · intro hvg
    apply add_nullables_iter_only_nullable _ _ _ _ hvg
    tauto
  · intro hv
    obtain ⟨m, hgv⟩ := (derives_iff_derivesIn _ _ _).1 hv
    apply nullable_in_compute_nullables
    exact hgv

end ComputeNullables

-- *********************************************************************************************** --
-- ************************************* Epsilon Elimination ************************************* --
-- *********************************************************************************************** --

section EliminateEmpty

variable {N : Type uN} [DecidableEq N]

/- Compute all possible combinations of leaving out nullable nonterminals from output -/
def remove_nullable (nullable : Finset N) (output : List (Symbol T N)) :=
  match output with
  | [] => [[]]
  | x :: s =>
    match x with
    | Symbol.nonterminal n =>
      (if n ∈ nullable then remove_nullable nullable s else []) ++
        (remove_nullable nullable s).map (x :: ·)
    | Symbol.terminal _ => (remove_nullable nullable s).map (x :: ·)

def remove_nullable_rule (nullable : Finset N) (r: ContextFreeRule T N) :=
  let fltrmap : List (Symbol T N) → Option (ContextFreeRule T N)
    | [] => Option.none
    | h :: t => ContextFreeRule.mk r.input (h :: t)
  (remove_nullable nullable r.output).filterMap fltrmap

variable {g : ContextFreeGrammar.{uN, uT} T} [DecidableEq g.NT]

noncomputable def remove_nullables (nullable : Finset g.NT) [DecidableEq T] :=
  (g.rules.toList.map (remove_nullable_rule nullable)).flatten.toFinset

/- Given `g`, computes a new grammar g' in which all rules deriving `[]` are removed and all
 rules in `g` have a set of corresponding rules in g' in which some nullable symbols do not appear
 in the output. For example if `r: V -> ABC` is in `g` and `A` and `B` are nullable, the rules
 `r₁: V -> ABC`, `r₂: V -> BC`, `r₃: V -> AC`, and `r₄: V -> C` will be in `g'` -/
noncomputable def eliminate_empty (g : ContextFreeGrammar.{uN, uT} T) [DecidableEq g.NT]
    [DecidableEq T] :=
  ContextFreeGrammar.mk g.NT g.initial (remove_nullables g.compute_nullables)

-- ******************************************************************** --
-- Only If direction of the main correctness theorem of eliminate_empty --
-- ******************************************************************** --

lemma in_remove_nullable_rule {r r': ContextFreeRule T g.NT} {nullable : Finset g.NT}
    (hrr : r' ∈ remove_nullable_rule nullable r) :
    r'.output ≠ [] := by
  unfold remove_nullable_rule at hrr
  rw [List.mem_filterMap] at hrr
  obtain ⟨a, -, ha⟩ := hrr
  cases a <;> simp at ha
  rw [←ha]
  tauto

lemma in_remove_not_epsilon {r : ContextFreeRule T g.NT} {nullable : Finset g.NT} [DecidableEq T]
    (hr : r ∈ remove_nullables nullable) :
    r.output ≠ [] := by
  unfold remove_nullables at hr
  rw [List.mem_toFinset, List.mem_flatten] at hr
  obtain ⟨l, hl, hr⟩ := hr
  rw [List.mem_map] at hl
  obtain ⟨r', _, hr'⟩ := hl
  rw [←hr'] at hr
  exact in_remove_nullable_rule hr

lemma produces_not_epsilon {u v : List (Symbol T g.NT)} [DecidableEq T]
    (huv : (g.eliminate_empty).Produces u v) :
    v ≠ [] := by
  unfold Produces at huv
  change ∃ r ∈ (remove_nullables g.compute_nullables), r.Rewrites u v at huv
  obtain ⟨r, hrg, hr⟩ := huv
  intro hw
  rw [hw] at hr
  exact in_remove_not_epsilon hrg (rewrites_empty_output hr)

lemma derives_not_epsilon {u v : List (Symbol T g.NT)} [DecidableEq T]
    (huv : (g.eliminate_empty).Derives u v) (hune : u ≠ []) :
    v ≠ [] := by
  change List (Symbol T g.eliminate_empty.NT) at u v
  induction huv using Derives.head_induction_on with
  | refl => exact hune
  | head hp _ ih => exact ih (produces_not_epsilon (g := g) hp)

-- Main proof of the only if direction: If the eliminate_empty grammar derives a string,
-- it is derivable in the original grammar

lemma remove_nullable_related {u v: List (Symbol T g.NT)} (nullable : Finset g.NT)
    (hn : ∀ x ∈ nullable, NullableNonTerminal x) (huv : u ∈ (remove_nullable nullable v)) :
    NullableRelated u v := by
  induction v generalizing u with
  | nil =>
    simp only [remove_nullable, List.mem_singleton] at huv
    rw [huv]
  | cons s v ih =>
    cases s with
    | nonterminal n =>
      simp [remove_nullable] at huv -- TODO
      cases huv with
      | inl hnu =>
        by_cases hnn : n ∈ nullable <;> simp only [hnn, false_and, true_and] at hnu
        exact NullableRelated.cons_nterm_nullable (ih hnu) (hn _ hnn)
      | inr huv =>
        obtain ⟨u', hu', rfl⟩ := huv
        exact NullableRelated.cons_nterm_match (ih hu') n
    | terminal t =>
      rw [remove_nullable, List.mem_map] at huv
      obtain ⟨u', hu', rfl⟩ := huv
      exact NullableRelated.cons_term (ih hu') t

lemma remove_nullable_rule_related {r': ContextFreeRule T g.NT} [DecidableEq T]
    {r : ContextFreeRule T g.NT} {hrg : r ∈ remove_nullable_rule g.compute_nullables r'} :
    r.input = r'.input ∧ NullableRelated r.output r'.output := by
  rw [remove_nullable_rule, List.mem_filterMap] at hrg
  obtain ⟨o, ho, ho'⟩ := hrg
  cases o <;> simp at ho'
  rw [←ho']
  constructor; rfl
  apply remove_nullable_related
  intro
  apply (compute_nullables_iff _).1 -- TODO
  exact ho

lemma eliminate_empty_rules [DecidableEq T] (r : ContextFreeRule T g.NT)
    {hrg : r ∈ g.eliminate_empty.rules} :
    ∃ r' ∈ g.rules, r.input = r'.input ∧ NullableRelated r.output r'.output := by
  unfold eliminate_empty remove_nullables at hrg
  simp at hrg -- TODO
  obtain ⟨r', hgr', hr'⟩ := hrg
  use r', hgr'
  apply remove_nullable_rule_related
  exact hr'

lemma eliminate_empty_step_derives [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : g.eliminate_empty.Produces u v) :
    g.Derives u v := by
  obtain ⟨r, hrg, hr⟩ := huv
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  apply Derives.append_right
  apply Derives.append_left
  obtain ⟨r', hr', hrr', hnrr'⟩ := @eliminate_empty_rules _ g _ _ r hrg
  rw [hrr']
  exact (rewrites_produces hr').trans_derives hnrr'.derives

lemma eliminate_empty_implies [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : g.eliminate_empty.Derives u v) : g.Derives u v := by
  change (List (Symbol T g.eliminate_empty.NT)) at u v
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih => exact Derives.trans (eliminate_empty_step_derives hp) ih

-- *************************************************************** --
-- If direction of the main correctness theorem of eliminate_empty --
-- *************************************************************** --

lemma in_remove_nullable (nullable : Finset g.NT) (u : List (Symbol T g.NT)) :
    u ∈ remove_nullable nullable u := by
  induction u with
  | nil =>
    simp [remove_nullable]
  | cons s _ ih =>
    cases s with
    | terminal t => simpa [remove_nullable] using ih
    | nonterminal n => by_cases hn : n ∈ nullable <;> simp [remove_nullable, hn, ih]

lemma nullableRelated_in_remove_nullable {nullable : Finset g.NT} {u v : List (Symbol T g.NT)}
    (hvu : NullableRelated v u) (hn : ∀ s, s ∈ nullable ↔ NullableNonTerminal s) :
    v ∈ remove_nullable nullable u := by
  induction u generalizing v with
  | nil =>
    rw [hvu.empty_empty]
    exact List.mem_singleton.2 rfl
  | cons s u ih =>
    cases s with
    | terminal t =>
      simp [remove_nullable]
      cases hvu with
      | @empty_left _ hvu =>
        exfalso
        exact nullable_not_terminal hvu
      | cons_term hu =>
        constructor
        exact ⟨ih hu, rfl⟩
    | nonterminal n =>
      simp only [remove_nullable, List.mem_append, List.mem_ite_nil_right, List.mem_map]
      cases hvu with
      | empty_left _ hu =>
        left
        rw [←List.singleton_append] at hu
        rw [hn]
        exact ⟨hu.empty_of_append_left, ih (NullableRelated.empty_left u hu.empty_of_append_right)⟩
      | cons_nterm_match hu'u =>
        right
        constructor
        exact ⟨ih hu'u, rfl⟩
      | cons_nterm_nullable hvu hnn =>
        left
        rw [hn]
        exact ⟨hnn, ih hvu⟩

variable [DecidableEq T]

lemma in_remove_nullables (nullable : Finset g.NT) (r : ContextFreeRule T g.NT)
    (hrg : r ∈ g.rules) (hne : r.output ≠ []) :
    r ∈ remove_nullables nullable := by
  unfold remove_nullables
  rw [List.mem_toFinset, List.mem_flatten]
  use (remove_nullable_rule nullable r)
  constructor
  · simp
    use r
  · unfold remove_nullable_rule
    rw [List.mem_filterMap]
    use r.output
    constructor
    · apply in_remove_nullable
    · obtain ⟨_, rₒ⟩ := r
      cases rₒ
      · contradiction
      · rfl

lemma nullableRelated_rule_in_rules {r : ContextFreeRule T g.NT}
    {u : List (Symbol T g.NT)} (hrg : r ∈ g.rules) (h : NullableRelated u r.output)
    (hneq : u ≠ []) :
    { input := r.input, output := u } ∈ g.eliminate_empty.rules := by
  unfold eliminate_empty
  unfold remove_nullables
  rw [List.mem_toFinset, List.mem_flatten]
  use (remove_nullable_rule g.compute_nullables r)
  unfold remove_nullable_rule
  constructor
  · rw [List.mem_map]
    use r
    constructor
    · exact Finset.mem_toList.2 hrg
    · rfl
  · rw [List.mem_filterMap]
    use u
    constructor
    · exact nullableRelated_in_remove_nullable h compute_nullables_iff
    · cases u
      · contradiction
      · rfl

lemma empty_related_produces_derives {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hwv : NullableRelated w v) :
    ∃ u', NullableRelated u' u ∧ g.eliminate_empty.Derives u' w := by
  obtain ⟨r, hrg, hr⟩ := huv
  rw [r.rewrites_iff] at hr
  obtain ⟨p, q, hv, hw⟩ := hr
  rw [hw] at hwv
  obtain ⟨w₁, w₂, w₃, hw, hw₁, hw₂, hw₃⟩ := hwv.append_split_three
  cases w₂ with
  | nil =>
    refine ⟨w, ?_, by rfl⟩
    rw [hv, hw]
    apply (hw₁.append _).append hw₃
    apply NullableRelated.empty_left
    apply Produces.trans_derives
    apply rewrites_produces hrg
    exact hw₂.empty_nullable
  | cons d l =>
    use (w₁ ++ [Symbol.nonterminal r.input] ++ w₃)
    constructor
    · rw [hv]
      exact (hw₁.append (by rfl)).append hw₃
    · rw [hw]
      have hdl : (d :: l) ≠ [] := by simp
      have hrdl := nullableRelated_rule_in_rules hrg hw₂ hdl
      exact Produces.single ⟨⟨r.input, d :: l⟩, hrdl, ContextFreeRule.rewrites_of_exists_parts _ w₁ w₃⟩

lemma implies_eliminate_empty_related {u v : List (Symbol T g.NT)}
    (hv : v ≠ []) {n : ℕ} (huv : g.DerivesIn u v n) :
    ∃ u', NullableRelated u' u ∧ g.eliminate_empty.Derives u' v := by
  cases n with
  | zero =>
    cases huv
    use u
  | succ n =>
    obtain ⟨u, huv, hvw⟩ := huv.head_of_succ
    obtain ⟨u', hru', huw'⟩ := @implies_eliminate_empty_related _ _ hv _ hvw
    obtain ⟨v', hvrv', hpv'u'⟩ := empty_related_produces_derives huv hru'
    exact ⟨v', hvrv', hpv'u'.trans huw'⟩

lemma implies_eliminate_empty {w : List (Symbol T g.NT)} {n : g.NT} {hw : w ≠ []}
    {m : ℕ} (hntw : g.DerivesIn [Symbol.nonterminal n] w m) :
    g.eliminate_empty.Derives [Symbol.nonterminal n] w := by
  obtain ⟨w', hw', hww⟩ := implies_eliminate_empty_related hw hntw
  cases hw' with
  | empty_left =>
    obtain ⟨_, _⟩ := hww.eq_or_head
    · contradiction
    · apply Derives.empty_empty at hww
      contradiction
  | cons_nterm_match hx _ =>
    cases hx
    exact hww
  | cons_nterm_nullable hxy hn =>
  · rw [NullableRelated.empty_empty hxy] at hww
    have := hww.empty_empty
    contradiction

theorem eliminate_empty_correct : g.language \ {[]} = g.eliminate_empty.language := by
  unfold language Generates
  apply Set.eq_of_subset_of_subset
  · intro w hw
    rw [Set.mem_diff] at hw
    obtain ⟨hw', hw''⟩ := hw
    rw [Set.mem_setOf_eq, g.derives_iff_derivesIn] at hw'
    obtain ⟨n, hgwn⟩ := hw'
    apply implies_eliminate_empty
    · intro hw
      rw [List.map_eq_nil_iff] at hw
      rw [hw] at hw''
      contradiction
    · simp only [eliminate_empty]
      exact hgwn
  · intro w hw
    rw [Set.mem_setOf_eq] at hw
    rw [Set.mem_diff]
    constructor
    · exact eliminate_empty_implies hw
    · rw [Set.not_mem_singleton_iff]
      intro hw'
      apply derives_not_epsilon hw
      exact List.cons_ne_nil _ []
      rw [hw', List.map_nil]

end EliminateEmpty

end ContextFreeGrammar
