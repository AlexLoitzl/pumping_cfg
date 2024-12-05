/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.CountingSteps

namespace ContextFreeGrammar

universe uT uN
variable {T : Type uT}

/-! Properties of context-free transformations to the empty string -/
section NullableDerivations

variable {g : ContextFreeGrammar.{uN, uT} T}

abbrev NullableNonTerminal (v : g.NT) : Prop := g.Derives [Symbol.nonterminal v] []

abbrev NullableWord (w : List (Symbol T g.NT)) : Prop := g.Derives w []

private lemma DerivesIn.empty_of_append_left_aux {u v w: List (Symbol T g.NT)} {n : ℕ}
    (hwe : g.DerivesIn w [] n) (hw : w = u ++ v) :
    ∃ m ≤ n, g.DerivesIn u [] m := by
  revert u v
  induction hwe using DerivesIn.induction_refl_head with
  | refl => simp [DerivesIn.zero_steps]
  | @head m  u v huv _ ih =>
    intro x y heq
    obtain ⟨r, rin, huv⟩ := huv
    obtain ⟨p, q, h1, h2⟩ := ContextFreeRule.Rewrites.exists_parts huv
    rw [heq, List.append_assoc, List.append_eq_append_iff] at h1
    cases h1 with
    | inl h =>
      obtain ⟨x', hx, _⟩ := h
      have hveq : v = x ++ (x' ++ r.output ++ q) := by simp [h2, hx]
      obtain ⟨m', _, _⟩ := ih hveq
      use m'
      constructor <;> tauto
    | inr h =>
      obtain ⟨x', hx, hr⟩ := h
      cases x' with
      | nil =>
        have hveq : v = x ++ (r.output ++ q) := by simp [hx, h2]
        obtain ⟨m', _, _⟩ := ih hveq
        use m'
        constructor <;> tauto
      | cons h t =>
        obtain ⟨_, _⟩ := hr
        simp [←List.append_assoc] at h2
        obtain ⟨m', hm, hd⟩ := ih h2
        use m'.succ
        constructor
        · exact Nat.succ_le_succ hm
        · apply Produces.trans_derivesIn
          use r
          constructor
          exact rin
          rw [ContextFreeRule.rewrites_iff]
          use p, t
          constructor
          · simp [hx]
          · rfl
          exact hd

lemma DerivesIn.empty_of_append_left {n : ℕ} {u v : List (Symbol T g.NT)}
    (huv : g.DerivesIn (u ++ v) [] n) :
    ∃ m ≤ n, g.DerivesIn u [] m := by
  apply empty_of_append_left_aux <;> tauto

lemma DerivesIn.empty_of_append_right_aux {u v w : List (Symbol T g.NT)} {n : ℕ}
    (hwe : g.DerivesIn w [] n) (hw : w = u ++ v) :
    ∃ m ≤ n, g.DerivesIn v [] m := by
  revert u v
  induction hwe using DerivesIn.induction_refl_head with
  | refl => simp [DerivesIn.zero_steps]
  | @head m u v huv _ ih =>
    intro x y heq
    obtain ⟨r, rin, huv⟩ := huv
    obtain ⟨p, q, h1, h2⟩ := huv.exists_parts
    rw [heq, List.append_assoc, List.append_eq_append_iff] at h1
    cases h1 with
    | inl h =>
      obtain ⟨y', h1 , hy⟩ := h
      rw [h1, List.append_assoc, List.append_assoc] at h2
      obtain ⟨m', hm, hd⟩ := ih h2
      use m'.succ
      constructor
      · exact Nat.succ_le_succ hm
      · apply Produces.trans_derivesIn
        use r
        constructor
        exact rin
        rw [ContextFreeRule.rewrites_iff]
        use y', q
        constructor
        · simp
          exact hy
        · rfl
        simp [hd]
    | inr h =>
      obtain ⟨q', hx, hq⟩ := h
      cases q' with
      | nil =>
        simp at hq h2
        obtain ⟨m', hm, hd⟩ := ih h2
        use m'.succ
        constructor
        · exact Nat.succ_le_succ hm
        · apply Produces.trans_derivesIn
          use r
          constructor
          exact rin
          rw [ContextFreeRule.rewrites_iff]
          use [], q
          constructor
          · simp
            tauto
          · rfl
          exact hd
      | cons h t =>
        obtain ⟨_,_⟩ := hq
        simp at h2
        repeat rw [←List.append_assoc] at h2
        obtain ⟨m', hm, hd⟩ := ih h2
        use m'
        constructor
        · exact Nat.le_succ_of_le hm
        · exact hd

lemma DerivesIn.empty_of_append_right {n : ℕ} {u v : List (Symbol T g.NT)}
    (huv : g.DerivesIn (u ++ v) [] n) :
    ∃ m ≤ n, g.DerivesIn v [] m := by
  apply empty_of_append_right_aux <;> tauto

lemma DerivesIn.empty_of_append {u v w : List (Symbol T g.NT)} {n : ℕ}
  (hwe : g.DerivesIn (w ++ u ++ v) [] n) : ∃ m ≤ n, g.DerivesIn u [] m := by
  obtain ⟨m1, hm1n, hm1e⟩ := hwe.empty_of_append_left
  obtain ⟨m2, hm2n, hm2e⟩ := hm1e.empty_of_append_right
  exact ⟨m2, Nat.le_trans hm2n hm1n, hm2e⟩

lemma NullableWord.empty_of_append {u v w : List (Symbol T g.NT)} (huvw : NullableWord (u ++ v ++ w)) :
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

lemma DerivesIn.mem_nullable {w : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ}
    (hw : g.DerivesIn w [] n) (hin : s ∈ w) :
    ∃ m ≤ n, g.DerivesIn [s] [] m := by
  revert n
  induction w with
  | nil => contradiction
  | cons v t ih =>
    intro n hn
    cases hin with
    | head =>
      change g.DerivesIn ([s] ++ t) [] n at hn
      exact hn.empty_of_append_left
    | tail _ hs =>
      change g.DerivesIn ([v] ++ t) [] n at hn
      obtain ⟨m, hmn, hte⟩ := hn.empty_of_append_right
      obtain ⟨m', hmm, hse⟩ := ih hs hte
      exact ⟨m', hmm.trans hmn, hse⟩

lemma rewrites_empty_output {v : List (Symbol T g.NT)} {r : ContextFreeRule T g.NT}
    (hr : r.Rewrites v []) :
    r.output = [] := by
  obtain ⟨_, _, -, _⟩ := hr.exists_parts
  simp_all

lemma Derives.append_left_trans {v w x y: List (Symbol T g.NT)} (hvw : g.Derives v w)
    (hxy : g.Derives x y) :
    g.Derives (x ++ v) (y ++ w) :=
  (hvw.append_left _).trans (hxy.append_right _)

lemma rewrites_produces {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    g.Produces [.nonterminal r.input] r.output :=
  ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩

lemma nullable_not_terminal {t : T} {w : List (Symbol T g.NT)} :
    ¬ NullableWord (Symbol.terminal t :: w) := by
  by_contra htw
  change g.Derives ([Symbol.terminal t] ++ w) [] at htw
  cases (NullableWord.empty_of_append_left htw).eq_or_head with
  | inl => contradiction
  | inr hv =>
    obtain ⟨_, ⟨r, _, hr⟩, _⟩ := hv
    cases hr with
    | cons _ hrs =>
      cases hrs

lemma Derives.empty_empty {w : List (Symbol T g.NT)} (hw : g.Derives [] w) : w = [] := by
  induction hw with
  | refl => rfl
  | tail _ hp _ =>
    obtain ⟨r, _, hr⟩ := hp
    cases hr <;> contradiction

lemma symbols_nullable_nullableWord (w : List (Symbol T g.NT)) (hw : ∀ a ∈ w, g.Derives [a] []) :
    NullableWord w := by
  induction w with
  | nil => rfl
  | cons d l ih =>
    show g.Derives ([d] ++ l) []
    trans
    · apply Derives.append_right
      apply hw
      exact List.mem_cons_self d l
    · apply ih
      intro v hv
      apply hw
      right
      exact hv

lemma DerivesIn.nullable_mem_nonterminal {w : List (Symbol T g.NT)} {s : Symbol T g.NT} {n : ℕ}
    (hw : g.DerivesIn w [] n) (hin : s ∈ w) : ∃ v, s = Symbol.nonterminal v := by
  have ⟨m, _, hsm⟩ := hw.mem_nullable hin
  cases m with
  | zero =>
    contradiction
  | succ m =>
    obtain ⟨u, hwu, _⟩ := hsm.head_of_succ
    obtain ⟨r, _, hsu⟩ := hwu
    obtain ⟨p,q, hi, ho⟩ := hsu.exists_parts
    cases p <;> simp at hi
    cases q <;> simp at hi
    use r.input

lemma NullableWord.nullableNonTerminal {w : List (Symbol T g.NT)} {v : Symbol T g.NT}
    (hw : NullableWord w) (hvin : v ∈ w) :
    ∃ x, v = Symbol.nonterminal x ∧ NullableNonTerminal x := by
  revert v
  induction w with
  | nil => simp
  | cons d l ih =>
    intro _ hin
    cases hin with
    | head =>
      cases d with
      | terminal => exact (nullable_not_terminal hw).elim
      | nonterminal a => exact ⟨a, rfl, hw.empty_of_append_left⟩
    | tail _ hmem =>
      apply ih _ hmem
      apply NullableWord.empty_of_append_right
      change NullableWord ([d] ++ l) at hw
      exact hw

end NullableDerivations


section NullableRelated

variable {g : ContextFreeGrammar.{uN, uT} T}

/-- `NullableRelated u v` means that `v` and `u` are equal up to interspersed nonterminals, each of
 which can be transformed to the empty string (i.e. for each additional nonterminal `nt`,
 `NullableNonterminal nt` holds) -/
inductive NullableRelated : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop where
  /- The empty string is `NullableRelated` to any `w`, s.t., `NullableWord w`-/
  | empty_left (ys : List (Symbol T g.NT)) (h: NullableWord ys) : NullableRelated [] ys
  /- A terminal symbol `t` needs to be matched exactly -/
  | cons_term (xs ys: List (Symbol T g.NT)) (h: NullableRelated xs ys) (t : T) :
                      NullableRelated (Symbol.terminal t :: xs) (Symbol.terminal t :: ys)
  /- A nonterminal symbol `nt` can be matched exactly -/
  | cons_nterm_match (xs ys: List (Symbol T g.NT)) (h: NullableRelated xs ys) (nt : g.NT) :
                     NullableRelated (Symbol.nonterminal nt :: xs) (Symbol.nonterminal nt :: ys)
  /- A nonterminal symbol `nt`, s.t., `NullableNonterminal nt` on the right, need not be matched -/
  | cons_nterm_nullable (xs ys: List (Symbol T g.NT)) (h: NullableRelated xs ys) (nt : g.NT)
                        (hn : NullableNonTerminal nt) : NullableRelated xs (Symbol.nonterminal nt :: ys)

@[refl]
lemma NullableRelated.refl (w : List (Symbol T g.NT)) : NullableRelated w w := by
  induction w with
  | nil =>
    constructor
    rfl
  | cons hd tl ih =>
    cases hd <;> constructor <;> exact ih

lemma NullableRelated.derives {v w : List (Symbol T g.NT)} (h: NullableRelated v w) :
    g.Derives w v := by
  induction h with
  | empty_left _ h =>
    exact h
  | cons_term v w _ t ih =>
    change g.Derives ([Symbol.terminal t] ++ w) ([Symbol.terminal t] ++ v)
    exact ih.append_left _
  | cons_nterm_match v w _ nt ih =>
    change g.Derives ([Symbol.nonterminal nt] ++ w) ([Symbol.nonterminal nt] ++ v)
    exact ih.append_left _
  | cons_nterm_nullable v w _ nt hnt ih =>
    change g.Derives ([Symbol.nonterminal nt] ++ w) ([] ++ v)
    exact Derives.append_left_trans ih hnt

lemma NullableRelated.empty_nullable {w : List (Symbol T g.NT)} (h : NullableRelated [] w) :
    NullableWord w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases h with
    | empty_left _ hsw => exact hsw
    | cons_nterm_nullable _ _ hw nt hnt =>
      change g.Derives ([Symbol.nonterminal nt] ++ w) ([] ++ [])
      exact Derives.trans (Derives.append_right hnt w) (ih hw)

lemma NullableRelated.empty_empty {w : List (Symbol T g.NT)} (h : NullableRelated w []) : w = [] := by
  cases h
  rfl

lemma NullableRelated.append_nullable' {w w' v : List (Symbol T g.NT)} (h1 : NullableRelated w' w)
    (h2 : NullableWord v) :
    NullableRelated w' (v ++ w) := by
  revert w w'
  induction v with
  | nil =>
    intro w w' h1
    exact h1
  | cons hd tl ih =>
    intro w w' h1
    obtain ⟨nt, h3, h4⟩ := h2.nullableNonTerminal (List.mem_cons_self hd tl)
    rw [h3]
    constructor
    apply ih
    apply NullableWord.empty_of_append_right
    change NullableWord ([hd] ++ tl) at h2
    exact h2
    exact h1
    exact h4

lemma NullableRelated.append_nullable_left {u v w: List (Symbol T g.NT)} (huv : NullableRelated u v)
    (hw : NullableWord w) :
    NullableRelated u (w ++ v) := by
  revert u v
  induction w with
  | nil =>
    intro v u huv
    exact huv
  | cons s w ih =>
    intro u v huv
    obtain ⟨nt, hs, hnt⟩ := hw.nullableNonTerminal (List.mem_cons_self s w)
    rw [hs]
    constructor
    · apply ih
      apply NullableWord.empty_of_append_right
      change NullableWord ([s] ++ w) at hw
      exact hw
      exact huv
    · exact hnt

lemma NullableRelated.append {u₁ u₂ v₁ v₂ : List (Symbol T g.NT)} (hv : NullableRelated v₁ v₂)
    (hu : NullableRelated u₁ u₂) :
    NullableRelated (v₁ ++ u₁) (v₂ ++ u₂) := by
  induction hv with
  | empty_left v₂ hv =>
    simp
    exact hu.append_nullable_left hv
  | cons_term u₁ u₂ _ t ih =>
    constructor
    exact ih
  | cons_nterm_match u₁ u₂ _ nt ih =>
    constructor
    exact ih
  | cons_nterm_nullable u₁ u₂ _ nt hnt ih =>
    constructor
    exact ih
    exact hnt

-- TODO ? maybe easier to do (h : u = w1 ++ w2) and then induction on h. This is quite tedious
lemma NullableRelated.append_split {u v w : List (Symbol T g.NT)}
    (huvw : NullableRelated u (v ++ w)) :
    ∃ v' w', u = v' ++ w' ∧ NullableRelated v' v ∧ NullableRelated w' w := by
  revert u w
  induction v with
  | nil =>
    intro u w huvw
    use [], u
    simp
    constructor
    rfl
    exact huvw
  | cons s v ih =>
    intro u w huvw
    cases u with
    | nil =>
      use [], []
      simp
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
          apply Derives.append_right
          assumption
          simp
          exact hvw.empty_nullable.empty_of_append_left
      · rw [←hv'w'.2]
        exact hnw'w
    | cons sᵤ u =>
      cases huvw with
      | cons_term _ _ huvw t =>
        obtain ⟨v', w', huv'w', hv'v, hw'w⟩ := ih huvw
        use (Symbol.terminal t :: v'), w'
        simp
        constructor
        · exact huv'w'
        · constructor
          · constructor
            exact hv'v
          · exact hw'w
      | cons_nterm_match _ _ huvw nt =>
        obtain ⟨v', w', huv'w', hv'v, hw'w⟩ := ih huvw
        use (Symbol.nonterminal nt :: v'), w'
        simp
        constructor
        · exact huv'w'
        · constructor
          · constructor
            exact hv'v
          · exact hw'w
      | cons_nterm_nullable _ _ huvw nt hnt =>
        obtain ⟨v', w', huv'w', hv'v, hw'w⟩ := ih huvw
        use v', w'
        constructor
        · exact huv'w'
        · constructor
          · constructor
            exact hv'v
            exact hnt
          · exact hw'w

lemma NullableRelated.append_split_three {u v w x : List (Symbol T g.NT)}
  (huvwx : NullableRelated u (v ++ w ++ x)) :
    ∃ u₁ u₂ u₃, u = u₁ ++ u₂ ++ u₃ ∧ NullableRelated u₁ v
      ∧ NullableRelated u₂ w ∧ NullableRelated u₃ x := by
  obtain ⟨u', u₃, huu'u₃, hu'vw, hu₃x⟩ := huvwx.append_split
  obtain ⟨u₁, u₂, hu'u₁u₂, hu₁v, hu₂w⟩ := hu'vw.append_split
  use u₁, u₂, u₃
  constructor ; rw [huu'u₃, hu'u₁u₂]
  exact ⟨hu₁v, hu₂w, hu₃x⟩

end NullableRelated

-- *********************************************************************************************** --
-- ************************************** Nullable Symbols *************************************** --
-- *********************************************************************************************** --
section ComputeNullables

variable {NT : Type uN} [DecidableEq NT]

def symbol_is_nullable (nullable : Finset NT) (s : Symbol T NT) : Bool :=
  match s with
  | Symbol.terminal _ => False
  | Symbol.nonterminal nt => nt ∈ nullable

def rule_is_nullable (nullable : Finset NT) (r : ContextFreeRule T NT) : Bool :=
  ∀ s ∈ r.output, symbol_is_nullable nullable s

def add_if_nullable (r : ContextFreeRule T NT) (nullable : Finset NT) : Finset NT :=
  if rule_is_nullable nullable r then insert r.input nullable else nullable

lemma add_if_nullable_subset (r : ContextFreeRule T NT) (nullable : Finset NT) :
  nullable ⊆ (add_if_nullable r nullable) := by
  unfold add_if_nullable
  split <;> simp

variable {g : ContextFreeGrammar.{uN, uT} T} [DecidableEq g.NT]

/- `generators g` is the set of all nonterminals that appear in the left hand side of rules of g -/
noncomputable def generators (g : ContextFreeGrammar.{uN, uT} T) [DecidableEq g.NT] : Finset g.NT :=
  (g.rules.toList.map (fun r => r.input)).toFinset

lemma input_in_generators {r : ContextFreeRule T g.NT} (hrmem : r ∈ g.rules) :
  r.input ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at hrmem
  revert hrmem
  induction g.rules.toList with
  | nil => simp
  | cons hd tl ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw [c1]
    · right
      exact ih c2

lemma nonterminal_in_generators {v : g.NT} {r : ContextFreeRule T g.NT} (hrmem : r ∈ g.rules)
    (hrv : r.input = v) :
    v ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at hrmem
  revert hrmem
  induction g.rules.toList with
  | nil => simp
  | cons hd tl ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw [← hrv, c1]
    · right
      exact ih c2

lemma add_if_nullable_subset_generators {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
    (hsub : nullable ⊆ g.generators) (hrmem : r ∈ g.rules) :
    add_if_nullable r nullable ⊆ g.generators := by
  unfold add_if_nullable
  split
  · exact Finset.insert_subset (input_in_generators hrmem) hsub
  · exact hsub

/- Single round of fixpoint iteration; adds `r.input` to the set of nullable symbols if all symbols in
 `r.output` are nullable -/
noncomputable def add_nullables (nullable : Finset g.NT) : Finset g.NT :=
  g.rules.toList.attach.foldr (fun ⟨r, _⟩ => add_if_nullable r) nullable

lemma add_nullables_sub_generators (nullable : Finset g.NT) (hsub : nullable ⊆ g.generators) :
    add_nullables nullable ⊆ g.generators := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil => simp; exact hsub
  | cons hd tl ih =>
    exact add_if_nullable_subset_generators ih (Finset.mem_toList.1 hd.2)

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

noncomputable def compute_nullables (g : ContextFreeGrammar.{uN, uT} T) [DecidableEq g.NT] : Finset g.NT :=
  add_nullables_iter ∅ g.generators.empty_subset

-- ********************************************************************** --
-- Only If direction of the main correctness theorem of compute_nullables --
-- ********************************************************************** --

lemma rule_is_nullable_correct (nullable : Finset g.NT) (r : ContextFreeRule T g.NT)
    (hrmem : r ∈ g.rules) (hn : ∀ v ∈ nullable, NullableNonTerminal v) (hr : rule_is_nullable nullable r) :
    NullableNonTerminal r.input := by
  unfold rule_is_nullable at hr
  unfold NullableNonTerminal
  have h1 : g.Produces [Symbol.nonterminal r.input] r.output := by
    use r
    constructor
    exact hrmem
    rw [ContextFreeRule.rewrites_iff]
    use [], []
    simp
  apply Produces.trans_derives h1
  apply symbols_nullable_nullableWord
  intro v hvin
  simp at hr
  specialize hr v hvin
  unfold symbol_is_nullable at hr
  cases v <;> simp at hr
  exact hn _ hr

lemma add_nullables_nullable (nullable : Finset g.NT) (hn : ∀ v ∈ nullable, NullableNonTerminal v) :
    ∀ v ∈ add_nullables nullable, NullableNonTerminal v := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil =>
    simp
    apply hn
  | cons hd tl ih =>
    simp
    unfold add_if_nullable
    split <;> rename_i h
    · simp
      constructor
      · apply rule_is_nullable_correct _ _ (Finset.mem_toList.1 hd.2) ih
        simp
        exact h
      · simp at ih
        exact ih
    · simp at ih
      exact ih

-- Main correctness result of the only if direction
lemma add_nullables_iter_only_nullable (nullable : Finset g.NT) (hsub : nullable ⊆ g.generators)
    (hn : ∀ v ∈ nullable, NullableNonTerminal v) :
    ∀ v ∈ (add_nullables_iter nullable hsub), NullableNonTerminal v:= by
  unfold add_nullables_iter
  intro v
  simp
  split
  · tauto
  · apply add_nullables_iter_only_nullable (add_nullables nullable)
          (add_nullables_sub_generators nullable hsub)
    exact add_nullables_nullable nullable hn
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable hsub h

-- ***************************************************************** --
-- If direction of the main correctness theorem of compute_nullables --
-- ***************************************************************** --

lemma subset_add_if_nullable_subset {r: ContextFreeRule T g.NT} {nullable nullable' : Finset g.NT}
    (hsub : nullable ⊆ nullable') : add_if_nullable r nullable ⊆ add_if_nullable r nullable' := by
  intro v hvin
  unfold add_if_nullable rule_is_nullable at hvin ⊢
  by_cases  h : decide (∀ s ∈ r.output, symbol_is_nullable nullable s) = true <;> simp [h] at hvin; simp at h
  · split <;> rename_i h'; simp at h'
    · cases hvin with
      | inl h =>
        rw [h]
        exact Finset.mem_insert_self r.input nullable'
      | inr h =>
        exact Finset.mem_insert_of_mem (hsub h)
    · cases hvin with
      | inl h'' =>
        unfold symbol_is_nullable at h' h
        simp at h' h
        obtain ⟨s, hsin, hs⟩ := h'
        specialize h s
        cases s <;> simp at hs h
        · contradiction
        · rename_i u
          apply h at hsin
          apply hsub at hsin
          contradiction
      | inr h =>
        exact hsub h
  · split
    · exact Finset.mem_insert_of_mem (hsub hvin)
    · exact (hsub hvin)

private lemma add_if_nullable_subset_rec {l : List (ContextFreeRule T g.NT)} {nullable : Finset g.NT} :
    nullable ⊆ List.foldr add_if_nullable nullable l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp
    apply Finset.Subset.trans ih
    apply add_if_nullable_subset

lemma nullable_in_add_nullables {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
    (hr : rule_is_nullable nullable r) (hrmem : r ∈ g.rules) : r.input ∈ add_nullables nullable := by
  unfold add_nullables
  have h := List.mem_attach g.rules.toList ⟨r, (Finset.mem_toList.2 hrmem)⟩
  revert r nullable
  induction g.rules.toList.attach with
  | nil =>
    intro r nullable _ hrmem
    simp
  | cons r t ih =>
    intro r' nullable h hr' hr''
    cases hr'' <;> simp at ih ⊢
    · apply Finset.mem_of_subset
      apply subset_add_if_nullable_subset
      apply add_if_nullable_subset_rec
      unfold add_if_nullable
      simp [h]
    · rename_i hr''
      apply Finset.mem_of_subset
      apply add_if_nullable_subset
      apply ih h
      exact hr''
      exact hr'

lemma add_nullable_add_nullable_iter (nullable: Finset g.NT) (hsub : nullable ⊆ g.generators) :
    add_nullables_iter nullable hsub = add_nullables (add_nullables_iter nullable hsub) := by
  unfold add_nullables_iter
  simp
  split <;> rename_i h
  · exact h
  · apply add_nullable_add_nullable_iter
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable hsub h

lemma nullable_in_compute_nullables (nullable : Finset g.NT) (hsub : nullable ⊆ g.generators)
    (v : g.NT) (n : ℕ) (hv: g.DerivesIn [Symbol.nonterminal v] [] n) :
    v ∈ add_nullables_iter nullable hsub := by
  cases n with
  | zero =>
    cases hv
  | succ n =>
    obtain ⟨u, hwu, hue⟩ := hv.head_of_succ
    obtain ⟨r, hrmem, hwu⟩ := hwu
    have h : rule_is_nullable (add_nullables_iter nullable hsub) r := by
      have h1 : u = r.output := by
        obtain ⟨p,q,h1,h2⟩ := hwu.exists_parts
        cases p <;> simp at h1
        cases q <;> simp at h1
        simp at h2
        exact h2
      unfold rule_is_nullable
      simp
      intro s hsin
      rw [←h1] at hsin
      obtain ⟨v', hv'⟩ := hue.nullable_mem_nonterminal hsin
      unfold symbol_is_nullable
      rw [hv']
      simp
      have ⟨m,_, hse⟩ := hue.mem_nullable hsin
      apply nullable_in_compute_nullables
      rw [←hv']
      exact hse
    have h1 : v = r.input := by
      obtain ⟨p,q,h2,_⟩ := hwu.exists_parts
      cases p <;> simp at h2
      cases q <;> simp at h2
      exact h2
    rw [add_nullable_add_nullable_iter]
    rw [h1]
    exact nullable_in_add_nullables h hrmem

-- Main correctness theorem of computing all nullable symbols --
lemma compute_nullables_iff (v : g.NT) : v ∈ compute_nullables g ↔ NullableNonTerminal v := by
  constructor
  · intro h
    apply add_nullables_iter_only_nullable Finset.empty
    tauto
    exact h
  · intro h
    unfold NullableNonTerminal at h
    obtain ⟨m, h⟩ := (derives_iff_derivesIn _ _ _).1 h
    apply nullable_in_compute_nullables
    exact h

end ComputeNullables

-- *********************************************************************************************** --
-- ************************************* Epsilon Elimination ************************************* --
-- *********************************************************************************************** --

section EliminateEmpty

variable {NT : Type uN} [DecidableEq NT]

/- Compute all possible combinations of leaving out nullable nonterminals from output -/
def remove_nullable (nullable : Finset NT) (output : List (Symbol T NT)) : List (List (Symbol T NT)) :=
  match output with
  | [] => [[]]
  | x :: xs => match x with
               | Symbol.nonterminal n => (if n ∈ nullable then remove_nullable nullable xs else [])
                                         ++ List.map (fun y => x :: y) (remove_nullable nullable xs)
               | Symbol.terminal _ => List.map (fun y => x :: y) (remove_nullable nullable xs)

def remove_nullable_rule (nullable : Finset NT) (r: ContextFreeRule T NT) : (List (ContextFreeRule T NT)) :=
  let fltrmap : List (Symbol T NT) → Option (ContextFreeRule T NT)
    | [] => Option.none
    | h :: t => ContextFreeRule.mk r.input (h :: t)
  (remove_nullable nullable r.output).filterMap fltrmap

variable {g : ContextFreeGrammar.{uN, uT} T} [DecidableEq g.NT]

noncomputable def remove_nullables (nullable : Finset g.NT) [DecidableEq T] : Finset (ContextFreeRule T g.NT) :=
  (g.rules.toList.map (remove_nullable_rule nullable)).flatten.toFinset

/- Given `g`, computes a new grammar g' in which all rules deriving `[]` are removed and all
 rules in `g` have a set of corresponding rules in g' in which some nullable symbols do not appear
 in the output. For example if `r: V -> ABC` is in `g` and `A` and `B` are nullable, the rules
 `r₁: V -> ABC`, `r₂: V -> BC`, `r₃: V -> AC`, and `r₄: V -> C` will be in `g'` -/
noncomputable def eliminate_empty (g : ContextFreeGrammar.{uN, uT} T) [DecidableEq g.NT] [DecidableEq T] :=
  ContextFreeGrammar.mk g.NT g.initial (remove_nullables g.compute_nullables)

-- ******************************************************************** --
-- Only If direction of the main correctness theorem of eliminate_empty --
-- ******************************************************************** --

lemma in_remove_nullable_rule {r r': ContextFreeRule T g.NT} {nullable : Finset g.NT}
    (hr'mem: r' ∈ remove_nullable_rule nullable r) :
    r'.output ≠ [] := by
  unfold remove_nullable_rule at hr'mem
  rw [List.mem_filterMap] at hr'mem
  obtain ⟨a, h1, h2⟩ := hr'mem
  cases a <;> simp at h2
  · rw [←h2]
    simp

lemma in_remove_not_epsilon {r : ContextFreeRule T g.NT} {nullable : Finset g.NT} [DecidableEq T]
    (hrmem : r ∈ remove_nullables nullable) :
    r.output ≠ [] := by
  unfold remove_nullables at hrmem
  rw [List.mem_toFinset, List.mem_flatten] at hrmem
  obtain ⟨l, hlin, hrmem⟩ := hrmem
  rw [List.mem_map] at hlin
  obtain ⟨r',hr'in, hr'l⟩ := hlin
  rw [←hr'l] at hrmem
  exact in_remove_nullable_rule hrmem

lemma produces_not_epsilon {u v : List (Symbol T g.NT)} [DecidableEq T]
    (huv : (g.eliminate_empty).Produces u v) :
    v ≠ [] := by
  unfold Produces at huv
  change ∃ r ∈ (remove_nullables g.compute_nullables), r.Rewrites u v at huv
  obtain ⟨r, hrmem, hr⟩ := huv
  intro hw
  rw [hw] at hr
  apply in_remove_not_epsilon hrmem
  exact rewrites_empty_output hr

lemma derives_not_epsilon {u v : List (Symbol T g.NT)} [DecidableEq T]
    (huv : (g.eliminate_empty).Derives u v) (hune : u ≠ []) :
    v ≠ [] := by
  change List (Symbol T g.eliminate_empty.NT) at u v
  -- TODO Very awkward
  induction huv using Derives.head_induction_on with
  | refl => exact hune
  | step hp _ ih =>
    apply ih
    exact produces_not_epsilon (g := g) hp

-- Main proof of the only if direction: If the eliminate_empty grammar derives a string,
-- it is derivable in the original grammar

lemma remove_nullable_related {u v: List (Symbol T g.NT)} (nullable : Finset g.NT)
    (hn : ∀ x ∈ nullable, NullableNonTerminal x) (humem : u ∈ (remove_nullable nullable v)) :
    NullableRelated u v := by
  revert u
  induction v with
  | nil =>
    intro u humem
    unfold remove_nullable at humem
    simp at humem
    rw [humem]
  | cons s v ih =>
    intro u humem
    unfold remove_nullable at humem
    cases s with
    | nonterminal nt =>
      simp at humem
      cases humem <;> rename_i humem
      · by_cases h : nt ∈ nullable <;> simp [h] at humem
        constructor
        exact ih humem
        exact hn _ h
      · obtain ⟨u', hu'mem, hu'⟩ := humem
        rw [←hu']
        constructor
        exact ih hu'mem
    | terminal t =>
      simp at humem
      obtain ⟨u', hu'mem, hu'⟩ := humem
      rw [←hu']
      constructor
      exact ih hu'mem

lemma remove_nullable_rule_related {r': ContextFreeRule T g.NT} [DecidableEq T]
    {r : ContextFreeRule T g.NT} {hrmem : r ∈ remove_nullable_rule g.compute_nullables r'} :
    r.input = r'.input ∧ NullableRelated r.output r'.output := by
  unfold remove_nullable_rule at hrmem
  rw [List.mem_filterMap] at hrmem
  obtain ⟨o, ho1, ho2⟩ := hrmem
  cases o <;> simp at ho2
  rw [←ho2]
  constructor
  rfl
  apply remove_nullable_related
  intro
  apply (compute_nullables_iff _).1
  exact ho1

lemma eliminate_empty_rules [DecidableEq T] (r : ContextFreeRule T g.NT)
    {hrmem : r ∈ g.eliminate_empty.rules} :
    ∃ r' ∈ g.rules, r.input = r'.input ∧ NullableRelated r.output r'.output := by
  unfold eliminate_empty remove_nullables at hrmem
  simp at hrmem
  obtain ⟨r', hr'mem, hr'⟩ := hrmem
  use r'
  constructor
  exact hr'mem
  apply remove_nullable_rule_related
  exact hr'

lemma eliminate_empty_step_derives [DecidableEq T] {u v : List (Symbol T g.NT)}
    (h : g.eliminate_empty.Produces u v) :
    g.Derives u v := by
  obtain ⟨r, hrmem, hr⟩ := h
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  apply Derives.append_right
  apply Derives.append_left
  obtain ⟨r', hr'mem, hrr', hnrr'⟩ := @eliminate_empty_rules _ g _ _ r hrmem
  rw [hrr']
  apply Produces.trans_derives
  exact rewrites_produces hr'mem
  apply hnrr'.derives

lemma eliminate_empty_implies [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : g.eliminate_empty.Derives u v) : g.Derives u v := by
  induction huv using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    apply Derives.trans
    exact eliminate_empty_step_derives hp
    exact ih

-- *************************************************************** --
-- If direction of the main correctness theorem of eliminate_empty --
-- *************************************************************** --

lemma in_remove_nullable (nullable : Finset g.NT) (u : List (Symbol T g.NT)) :
    u ∈ remove_nullable nullable u := by
  induction u with
  | nil =>
    unfold remove_nullable
    simp
  | cons s u ih =>
    unfold remove_nullable
    cases s <;> simp
    · exact ih
    · rename_i nt
      by_cases h : nt ∈ nullable <;> simp [h]
      · right
        exact ih
      · exact ih

lemma nullableRelated_in_remove_nullable {nullable : Finset g.NT} {u v: List (Symbol T g.NT)}
    (hvu : NullableRelated v u) (hn : ∀ s, s ∈ nullable ↔ NullableNonTerminal s) :
    v ∈ remove_nullable nullable u := by
  revert v
  induction u with
  | nil =>
    intro v hvu
    rw [hvu.empty_empty]
    unfold remove_nullable
    exact List.mem_singleton.2 rfl
  | cons s u ih =>
    unfold remove_nullable
    intro v hvu
    cases s with
    | terminal t =>
      simp
      cases hvu with
      | empty_left =>
        rename_i hvu
        exfalso
        exact nullable_not_terminal hvu
      | cons_term u' _ hu'u =>
        use u'
        constructor
        · exact ih hu'u
        · rfl
    | nonterminal nt =>
      simp
      cases hvu with
      | empty_left _ hu =>
        left
        rw [←List.singleton_append] at hu
        rw [hn]
        exact ⟨hu.empty_of_append_left, ih (NullableRelated.empty_left u hu.empty_of_append_right)⟩
      | cons_nterm_match u' _ hu'u =>
        right
        use u'
        constructor
        · exact ih hu'u
        · rfl
      | cons_nterm_nullable u' _ hvu _ hnt =>
        left
        rw [hn]
        exact ⟨hnt, ih hvu⟩

variable [DecidableEq T]

lemma in_remove_nullables (nullable : Finset g.NT) (r : ContextFreeRule T g.NT)
    (hrmem : r ∈ g.rules) (hne : r.output ≠ []) :
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
    · obtain ⟨rin, rout⟩ := r
      cases rout
      contradiction
      simp


lemma nullableRelated_rule_in_rules {r : ContextFreeRule T g.NT}
    {u : List (Symbol T g.NT)} (hrmem : r ∈ g.rules) (h : NullableRelated u r.output)
    (hneq : u ≠ []) :
    { input := r.input, output := u } ∈ (@eliminate_empty T g).rules := by
  unfold eliminate_empty
  simp
  unfold remove_nullables
  rw [List.mem_toFinset, List.mem_flatten]
  use (remove_nullable_rule g.compute_nullables r)
  unfold remove_nullable_rule
  constructor
  · rw [List.mem_map]
    use r
    constructor
    · exact Finset.mem_toList.2 hrmem
    · rfl
  · rw [List.mem_filterMap]
    use u
    constructor
    · exact nullableRelated_in_remove_nullable h compute_nullables_iff
    · cases u
      contradiction
      rfl

lemma empty_related_produces_derives {u v w: List (Symbol T g.NT)} (huv : g.Produces u v)
    (hwv : NullableRelated w v) : ∃ u', NullableRelated u' u ∧ g.eliminate_empty.Derives u' w := by
  unfold Produces at huv
  obtain ⟨r, hrmem, hr⟩ := huv
  rw [r.rewrites_iff] at hr
  obtain ⟨p,q, hv, hw⟩ := hr
  rw [hw] at hwv
  obtain ⟨w1', w2', w3', heq, hw1, hw2, hw3⟩ := hwv.append_split_three
  cases w2' with
  | nil =>
    use w
    constructor
    · rw [hv, heq]
      apply (hw1.append _).append hw3
      apply NullableRelated.empty_left
      apply Produces.trans_derives
      apply rewrites_produces hrmem
      exact hw2.empty_nullable
    · rfl
  | cons hd tl =>
    use (w1' ++ [Symbol.nonterminal r.input] ++ w3')
    constructor
    · rw [hv]
      apply (hw1.append _).append hw3
      rfl
    · rw [heq]
      apply Produces.single
      have hneq : (hd :: tl) ≠ [] := by simp
      have h := nullableRelated_rule_in_rules hrmem hw2 hneq
      let r' : ContextFreeRule T g.NT := { input := r.input, output := hd :: tl }
      use r'
      constructor
      exact h
      change r'.Rewrites (w1' ++ [Symbol.nonterminal r'.input] ++ w3') (w1' ++ r'.output ++ w3')
      apply ContextFreeRule.rewrites_of_exists_parts

lemma implies_eliminate_empty_related {u v : List (Symbol T g.NT)} (hne : v ≠ [])
    {n : ℕ} (huv : g.DerivesIn u v n) :
    ∃ u', NullableRelated u' u ∧ g.eliminate_empty.Derives u' v := by
  cases n with
  | zero =>
    cases huv
    use u
  | succ n =>
    obtain ⟨u, huv, hvw⟩ := huv.head_of_succ
    obtain ⟨u', hru', huw'⟩ := @implies_eliminate_empty_related _ _ hne _ hvw
    obtain ⟨v', hvrv', hpv'u'⟩ := empty_related_produces_derives huv hru'
    use v'
    constructor
    exact hvrv'
    exact Derives.trans hpv'u' huw'

lemma implies_eliminate_empty {w : List (Symbol T g.NT)} {nt : g.NT} {hne : w ≠ []}
    {n : ℕ} (hntw : g.DerivesIn [Symbol.nonterminal nt] w n) :
    (@eliminate_empty T g).Derives [Symbol.nonterminal nt] w := by
  obtain ⟨w', hw', hw'w⟩ := implies_eliminate_empty_related hne hntw
  cases hw'
  · rename_i h
    obtain ⟨h1, h1⟩ := Derives.eq_or_head hw'w
    · contradiction
    · apply Derives.empty_empty at hw'w
      contradiction
  · rename_i h
    cases h
    exact hw'w
  · rename_i h
    apply NullableRelated.empty_empty at h
    rw [h] at hw'w
    apply Derives.empty_empty at hw'w
    contradiction

theorem eliminate_empty_correct : g.language \ {[]} = g.eliminate_empty.language := by
  unfold language Generates
  apply Set.eq_of_subset_of_subset
  · intro w h
    rw [Set.mem_diff] at h
    obtain ⟨h1, h2⟩ := h
    simp at h1
    rw [g.derives_iff_derivesIn] at h1
    obtain ⟨n, h1⟩ := h1
    apply implies_eliminate_empty
    · intro h'
      simp at h'
      rw [h'] at h2
      contradiction
    · unfold eliminate_empty
      simp
      exact h1
  · intro w h
    simp at h
    rw [Set.mem_diff]
    constructor
    · exact eliminate_empty_implies h
    · rw [Set.not_mem_singleton_iff]
      intro h'
      apply derives_not_epsilon h
      simp
      rw [h', List.map_nil]

end EliminateEmpty

end ContextFreeGrammar
