/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.CountingSteps

namespace ContextFreeGrammar

variable {T : Type} {g : ContextFreeGrammar T}

/-! Properties of context-free transformations to the empty string -/
section NullableDerivations

abbrev NullableNonTerminal (v : g.NT) : Prop := g.Derives [Symbol.nonterminal v] []

abbrev NullableWord (w : List (Symbol T g.NT)) : Prop := g.Derives w []

private lemma DerivesIn.empty_of_append_left_aux {u v w: List (Symbol T g.NT)} {n : ℕ}
  (hwe : g.DerivesIn w [] n) (hw : w = u ++ v) : ∃ m ≤ n, g.DerivesIn u [] m := by
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
  (hwe : g.DerivesIn w [] n) (hw : w = u ++ v) : ∃ m ≤ n, g.DerivesIn v [] m := by
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
  (h2 : NullableWord v) : NullableRelated w' (v ++ w) := by
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
  (hw : NullableWord w) : NullableRelated u (w ++ v) := by
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
  (hu : NullableRelated u₁ u₂) : NullableRelated (v₁ ++ u₁) (v₂ ++ u₂) := by
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
variable [DecidableEq g.NT]

-- All lefthand side non-terminals
noncomputable def generators : Finset g.NT := (g.rules.toList.map (fun r => r.input)).toFinset

lemma input_in_generators {r : ContextFreeRule T g.NT} (h : r ∈ g.rules) :
  r.input ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at h
  revert h
  induction g.rules.toList with
  | nil => simp
  | cons hd tl ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw [c1]
    · right
      exact ih c2

lemma nonterminal_in_generators {v : g.NT} {r : ContextFreeRule T g.NT} (h : r ∈ g.rules) (h' : r.input = v):
  v ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at h
  revert h
  induction g.rules.toList with
  | nil => simp
  | cons hd tl ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw [← h', c1]
    · right
      exact ih c2

-- Fixpoint iteration to compute all nullable variables
-- For the termination proof, we ensure that we only ever add nonterminals from the set of generators
def symbol_is_nullable (nullable : Finset g.NT) (s : Symbol T g.NT) : Bool :=
  match s with
  | Symbol.terminal _ => False
  | Symbol.nonterminal nt => nt ∈ nullable

def rule_is_nullable (nullable : Finset g.NT) (r : ContextFreeRule T g.NT) : Bool :=
  ∀ s ∈ r.output, symbol_is_nullable nullable s

def add_if_nullable (r : ContextFreeRule T g.NT) (nullable : Finset g.NT) : Finset g.NT :=
  if rule_is_nullable nullable r then insert r.input nullable else nullable

lemma add_if_nullable_subset_generators {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (p : nullable ⊆ g.generators) (hin : r ∈ g.rules) :
  add_if_nullable r nullable ⊆ g.generators := by
  unfold add_if_nullable
  split
  · exact Finset.insert_subset (input_in_generators hin) p
  · exact p

lemma add_if_nullable_subset (r : ContextFreeRule T g.NT) (nullable : Finset g.NT) :
  nullable ⊆ (add_if_nullable r nullable) := by
  unfold add_if_nullable
  split <;> simp

--  Single round of fixpoint iteration
--  Add all rules' lefthand variable if all output symbols are in the set of nullable symbols
noncomputable def add_nullables (nullable : Finset g.NT) : Finset g.NT :=
  g.rules.toList.attach.foldr (fun ⟨r, _⟩ => add_if_nullable r) nullable

lemma add_nullables_subset_generators (nullable : Finset g.NT) (p : nullable ⊆ g.generators) :
  add_nullables nullable ⊆ g.generators := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil => simp; exact p
  | cons hd tl ih =>
    exact add_if_nullable_subset_generators ih (Finset.mem_toList.1 hd.2)

lemma add_nullables_grows (nullable : Finset g.NT) :
  nullable ⊆ (add_nullables nullable) := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil => simp
  | cons hd tl ih =>
    apply subset_trans ih
    apply add_if_nullable_subset hd.1

-- Proof of our termination measure shrinking
lemma generators_limits_nullable (nullable : Finset g.NT) (p : nullable ⊆ g.generators)
  (hneq : nullable ≠ add_nullables nullable) :
  (g.generators).card - (add_nullables nullable).card < (g.generators).card - nullable.card := by
  have h := HasSubset.Subset.ssubset_of_ne (add_nullables_grows nullable) hneq
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_lt_of_le
    · apply Finset.card_lt_card h
    · exact Finset.card_le_card (add_nullables_subset_generators nullable p)
  · apply Finset.card_lt_card h

noncomputable def add_nullables_iter (nullable : Finset g.NT) (p : nullable ⊆ g.generators) : Finset g.NT :=
  let nullable' := add_nullables nullable
  if nullable = nullable' then
    nullable
  else
    add_nullables_iter nullable' (add_nullables_subset_generators nullable p)
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable p h

-- Compute all nullable variables of a grammar
noncomputable def compute_nullables : Finset g.NT :=
  add_nullables_iter ∅ generators.empty_subset

-- ********************************************************************** --
-- Only If direction of the main correctness theorem of compute_nullables --
-- ********************************************************************** --

lemma rule_is_nullable_correct (nullable : Finset g.NT) (r : ContextFreeRule T g.NT)
  (hrin : r ∈ g.rules) (hin : ∀ v ∈ nullable, NullableNonTerminal v) (hr : rule_is_nullable nullable r) :
  NullableNonTerminal r.input := by
  unfold rule_is_nullable at hr
  unfold NullableNonTerminal
  have h1 : g.Produces [Symbol.nonterminal r.input] r.output := by
    use r
    constructor
    exact hrin
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
  exact hin _ hr

lemma add_nullables_nullable (nullable : Finset g.NT) (hin : ∀ v ∈ nullable, NullableNonTerminal v) :
  ∀ v ∈ add_nullables nullable, NullableNonTerminal v := by
  unfold add_nullables
  induction g.rules.toList.attach with
  | nil =>
    simp
    apply hin
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
lemma add_nullables_iter_only_nullable (nullable : Finset g.NT) (p : nullable ⊆ g.generators)
  (hin : ∀ v ∈ nullable, NullableNonTerminal v) :
  ∀ v ∈ (add_nullables_iter nullable p), NullableNonTerminal v:= by
  unfold add_nullables_iter
  intro v
  simp
  split
  · tauto
  · apply add_nullables_iter_only_nullable (add_nullables nullable)
          (add_nullables_subset_generators nullable p)
    exact add_nullables_nullable nullable hin
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable p h

-- ***************************************************************** --
-- If direction of the main correctness theorem of compute_nullables --
-- ***************************************************************** --

lemma subset_add_if_nullable_subset {r: ContextFreeRule T g.NT} {nullable nullable' : Finset g.NT}
  (p : nullable ⊆ nullable') : add_if_nullable r nullable ⊆ add_if_nullable r nullable' := by
  intro v hvin
  unfold add_if_nullable rule_is_nullable at hvin ⊢
  by_cases  h : decide (∀ s ∈ r.output, symbol_is_nullable nullable s) = true <;> simp [h] at hvin; simp at h
  · split <;> rename_i h'; simp at h'
    · cases hvin with
      | inl h =>
        rw [h]
        exact Finset.mem_insert_self r.input nullable'
      | inr h =>
        exact Finset.mem_insert_of_mem (p h)
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
          apply p at hsin
          contradiction
      | inr h =>
        exact p h
  · split
    · exact Finset.mem_insert_of_mem (p hvin)
    · exact (p hvin)

private lemma add_if_nullable_subset_rec {l : List (ContextFreeRule T g.NT)} {nullable : Finset g.NT} :
  nullable ⊆ List.foldr add_if_nullable nullable l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp
    apply Finset.Subset.trans ih
    apply add_if_nullable_subset

lemma nullable_in_add_nullables {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (h : rule_is_nullable nullable r) (hr : r ∈ g.rules) : r.input ∈ add_nullables nullable := by
  unfold add_nullables
  have h := List.mem_attach g.rules.toList ⟨r, (Finset.mem_toList.2 hr)⟩
  revert r nullable
  induction g.rules.toList.attach with
  | nil =>
    intro r nullable _ hrin
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

lemma add_nullable_add_nullable_iter (nullable: Finset g.NT) (p : nullable ⊆ generators) :
  add_nullables_iter nullable p = add_nullables (add_nullables_iter nullable p) := by
  unfold add_nullables_iter
  simp
  split <;> rename_i h
  · exact h
  · apply add_nullable_add_nullable_iter
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable p h

lemma nullable_in_compute_nullables (nullable : Finset g.NT) (p : nullable ⊆ generators) (v : g.NT)
  (n : ℕ) (h: g.DerivesIn [Symbol.nonterminal v] [] n) : v ∈ add_nullables_iter nullable p := by
  cases n with
  | zero =>
    cases h
  | succ n =>
    obtain ⟨u, hwu, hue⟩ := h.head_of_succ
    obtain ⟨r, hrin, hwu⟩ := hwu
    have h : rule_is_nullable (add_nullables_iter nullable p) r := by
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
    exact nullable_in_add_nullables h hrin

-- Main correctness theorem of computing all nullable symbols --
lemma compute_nullables_iff (v : g.NT) :
  v ∈ compute_nullables ↔ NullableNonTerminal v := by
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

variable [DecidableEq g.NT]

def remove_nullable (nullable : Finset g.NT) (output : List (Symbol T g.NT)) : List (List (Symbol T g.NT)) :=
  match output with
  | [] => [[]]
  | x :: xs => match x with
               | Symbol.nonterminal n => (if n ∈ nullable then remove_nullable nullable xs else [])
                                         ++ List.map (fun y => x :: y) (remove_nullable nullable xs)
               | Symbol.terminal _ => List.map (fun y => x :: y) (remove_nullable nullable xs)

def remove_nullable_rule (nullable : Finset g.NT) (r: ContextFreeRule T g.NT) : (List (ContextFreeRule T g.NT)) :=
  let fltrmap : List (Symbol T g.NT) → Option (ContextFreeRule T g.NT)
    | [] => Option.none
    | h :: t => ContextFreeRule.mk r.input (h :: t)
  (remove_nullable nullable r.output).filterMap fltrmap

noncomputable def remove_nullables (nullable : Finset g.NT) [DecidableEq T] : Finset (ContextFreeRule T g.NT) :=
  (g.rules.toList.map (remove_nullable_rule nullable)).flatten.toFinset

noncomputable def eliminate_empty (g : ContextFreeGrammar T) [DecidableEq g.NT] [DecidableEq T] :=
  ContextFreeGrammar.mk g.NT g.initial (remove_nullables compute_nullables)

-- ******************************************************************** --
-- Only If direction of the main correctness theorem of eliminate_empty --
-- ******************************************************************** --

-- First we prove that the grammar cannot derive empty (Given the input non-empty)

lemma in_remove_nullable_rule {r r': ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (h: r' ∈ remove_nullable_rule nullable r) : r'.output ≠ [] := by
  unfold remove_nullable_rule at h
  rw [List.mem_filterMap] at h
  obtain ⟨a, h1, h2⟩ := h
  cases a <;> simp at h2
  · rw [←h2]
    simp

lemma in_remove_not_epsilon {r : ContextFreeRule T g.NT} {nullable : Finset g.NT} [DecidableEq T]
  (h : r ∈ remove_nullables nullable) : r.output ≠ [] := by
  unfold remove_nullables at h
  rw [List.mem_toFinset, List.mem_flatten] at h
  obtain ⟨l, hlin, hrin⟩ := h
  rw [List.mem_map] at hlin
  obtain ⟨r',hr'in, hr'l⟩ := hlin
  rw [←hr'l] at hrin
  exact in_remove_nullable_rule hrin

lemma produces_not_epsilon {v w : List (Symbol T g.NT)} [DecidableEq T]
  (h : (g.eliminate_empty).Produces v w) : w ≠ [] := by
  unfold Produces at h
  change ∃ r ∈ (remove_nullables compute_nullables), r.Rewrites v w at h
  obtain ⟨r, hin, hr⟩ := h
  intro hw
  rw [hw] at hr
  apply in_remove_not_epsilon hin
  exact rewrites_empty_output hr

lemma derives_not_epsilon {v w : List (Symbol T g.NT)} [DecidableEq T]
  (h : (g.eliminate_empty).Derives v w) (he : v ≠ []) :
  w ≠ [] := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact he
  | head hd _ ih =>
    apply ih
    exact produces_not_epsilon hd

-- Main proof of the only if direction: If the eliminate_empty grammar derives a string,
-- it is derivable in the original grammar

lemma remove_nullable_related {o o': List (Symbol T g.NT)} (nullable : Finset g.NT)
  (p : ∀ x ∈ nullable, NullableNonTerminal x) (hin : o ∈ (remove_nullable nullable o')) :
  NullableRelated o o' := by
  revert o
  induction o' with
  | nil =>
    intro o hin
    unfold remove_nullable at hin
    simp at hin
    rw [hin]
  | cons hd tl ih =>
    intro o hin
    unfold remove_nullable at hin
    cases hd with
    | nonterminal nt =>
      simp at hin
      cases hin <;> rename_i h
      · by_cases h' : nt ∈ nullable <;> simp [h'] at h
        constructor
        exact ih h
        exact p _ h'
      · obtain ⟨o1, hoin, ho⟩ := h
        rw [←ho]
        constructor
        exact ih hoin
    | terminal t =>
      simp at hin
      obtain ⟨o1, hoin, ho⟩ := hin
      rw [←ho]
      constructor
      exact ih hoin

lemma remove_nullable_rule_related {r': ContextFreeRule T g.NT} [DecidableEq T]
  {r : ContextFreeRule T (@eliminate_empty T g).NT} {h : r ∈ remove_nullable_rule compute_nullables r'} :
  r.input = r'.input ∧ @NullableRelated _ g r.output r'.output := by
  unfold remove_nullable_rule at h
  rw [List.mem_filterMap] at h
  obtain ⟨o, ho1, ho2⟩ := h
  cases o <;> simp at ho2
  rw [←ho2]
  constructor
  rfl
  apply remove_nullable_related
  intro
  apply (compute_nullables_iff _).1
  exact ho1

lemma eliminate_empty_rules [DecidableEq T] (r : ContextFreeRule T (@eliminate_empty T g).NT) {h : r ∈ (@eliminate_empty T g).rules} :
  ∃ r' ∈ g.rules, r.input = r'.input ∧ @NullableRelated _ g r.output r'.output := by
  unfold eliminate_empty remove_nullables at h
  simp at h
  obtain ⟨r', hrin', hr'⟩ := h
  use r'
  constructor
  exact hrin'
  apply remove_nullable_rule_related
  exact hr'

lemma eliminate_empty_step_derives [DecidableEq T] {v w : List (Symbol T g.NT)} (h : (@eliminate_empty T g).Produces v w) :
  g.Derives v w := by
  obtain ⟨r, hrin, hr⟩ := h
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  apply Derives.append_right
  apply Derives.append_left
  obtain ⟨r', hin, heq, hn⟩ := @eliminate_empty_rules _ _ _ _ r hrin
  rw [heq]
  apply Produces.trans_derives
  exact rewrites_produces hin
  apply hn.derives

lemma eliminate_empty_implies [DecidableEq T] {v w : List (Symbol T g.NT)}
  (h : (@eliminate_empty T g).Derives v w) : g.Derives v w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    apply Derives.trans
    exact eliminate_empty_step_derives hp
    exact ih

-- *************************************************************** --
-- If direction of the main correctness theorem of eliminate_empty --
-- *************************************************************** --

lemma in_remove_nullable (nullable : Finset g.NT) (output : List (Symbol T g.NT)) :
  output ∈ remove_nullable nullable output := by
  induction output with
  | nil =>
    unfold remove_nullable
    simp
  | cons o output ih =>
    unfold remove_nullable
    cases o <;> simp
    · exact ih
    · rename_i nt
      by_cases h : nt ∈ nullable <;> simp [h]
      · right
        exact ih
      · exact ih

lemma in_remove_nullables [DecidableEq T] (nullable : Finset g.NT) (r : ContextFreeRule T g.NT) (h : r ∈ g.rules)
  (ho : r.output ≠ []):
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

lemma nullableRelated_in_remove_nullable {nullable : Finset g.NT} {o o': List (Symbol T g.NT)}
  (h : NullableRelated o' o) (p : ∀ s, s ∈ nullable ↔ NullableNonTerminal s) :
  o' ∈ remove_nullable nullable o := by
  revert o'
  induction o with
  | nil =>
    intro o' h
    rw [h.empty_empty]
    unfold remove_nullable
    exact List.mem_singleton.2 rfl
  | cons o os ih =>
    unfold remove_nullable
    intro o' h
    cases o with
    | terminal t =>
      simp
      cases h with
      | empty_left =>
        rename_i h
        exfalso
        exact nullable_not_terminal h
      | cons_term os' _ h =>
        use os'
        constructor
        · exact ih h
        · rfl
    | nonterminal nt =>
      simp
      cases h with
      | empty_left _ h =>
        left
        rw [←List.singleton_append] at h
        rw [p]
        exact ⟨h.empty_of_append_left, ih (NullableRelated.empty_left os h.empty_of_append_right)⟩
      | cons_nterm_match os' _ h =>
        right
        use os'
        constructor
        · exact ih h
        · rfl
      | cons_nterm_nullable os' _ h _ hn =>
        left
        rw [p]
        exact ⟨hn, ih h⟩

lemma nullableRelated_rule_in_rules [DecidableEq T] {r : ContextFreeRule T g.NT} {o' : List (Symbol T g.NT)}
  (hrin : r ∈ g.rules) (h : NullableRelated o' r.output) (hneq : o' ≠ []) :
  { input := r.input, output := o' } ∈ (@eliminate_empty T g).rules := by
  unfold eliminate_empty
  simp
  unfold remove_nullables
  rw [List.mem_toFinset, List.mem_flatten]
  use (remove_nullable_rule compute_nullables r)
  unfold remove_nullable_rule
  constructor
  · rw [List.mem_map]
    use r
    constructor
    · exact Finset.mem_toList.2 hrin
    · rfl
  · rw [List.mem_filterMap]
    use o'
    constructor
    · exact nullableRelated_in_remove_nullable h compute_nullables_iff
    · cases o'
      contradiction
      rfl

lemma empty_related_produces_derives [DecidableEq T] {v w w': List (Symbol T g.NT)} (hp : g.Produces v w)
  (hn : NullableRelated w' w) : ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w' := by
  unfold Produces at hp
  obtain ⟨r, hrin, hr⟩ := hp
  rw [r.rewrites_iff] at hr
  obtain ⟨p,q, hv, hw⟩ := hr
  rw [hw] at hn
  obtain ⟨w1', w2', w3', heq, hw1, hw2, hw3⟩ := hn.append_split_three
  cases w2' with
  | nil =>
    use w'
    constructor
    · rw [hv, heq]
      apply (hw1.append _).append hw3
      apply NullableRelated.empty_left
      apply Produces.trans_derives
      apply rewrites_produces hrin
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
      have h := nullableRelated_rule_in_rules hrin hw2 hneq
      let r' : ContextFreeRule T g.NT := { input := r.input, output := hd :: tl }
      use r'
      constructor
      exact h
      change r'.Rewrites (w1' ++ [Symbol.nonterminal r'.input] ++ w3') (w1' ++ r'.output ++ w3')
      apply ContextFreeRule.rewrites_of_exists_parts

lemma implies_eliminate_empty_related [DecidableEq T] {v w : List (Symbol T g.NT)} (hneq : w ≠ []) {n : ℕ}
  (h : g.DerivesIn v w n) :
  ∃ v', NullableRelated v' v ∧ (@eliminate_empty T g).Derives v' w := by
  cases n with
  | zero =>
    cases h
    use v
  | succ n =>
    obtain ⟨u, huv, hvw⟩ := h.head_of_succ
    obtain ⟨u', hru', huw'⟩ := @implies_eliminate_empty_related _ _ _ hneq _ hvw
    obtain ⟨v', hvrv', hpv'u'⟩ := empty_related_produces_derives huv hru'
    use v'
    constructor
    exact hvrv'
    exact Derives.trans hpv'u' huw'

lemma implies_eliminate_empty [DecidableEq T] {w : List (Symbol T g.NT)} {v : g.NT} {hneq : w ≠ []} {n : ℕ}
  (h : g.DerivesIn [Symbol.nonterminal v] w n) :
  (@eliminate_empty T g).Derives [Symbol.nonterminal v] w := by
  obtain ⟨w', hw', hw'w⟩ := implies_eliminate_empty_related hneq h
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

theorem eliminate_empty_correct [DecidableEq T] :
  g.language \ {[]} = (@eliminate_empty T g).language := by
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
