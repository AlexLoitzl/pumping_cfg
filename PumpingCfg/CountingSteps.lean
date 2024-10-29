/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/
import Mathlib.Computability.ContextFreeGrammar

universe uT uN
variable {T : Type uT}

namespace ContextFreeGrammar

/-- Given a context-free grammar `g`, strings `u` and `v`, and number `n`
`g.DerivesSteps u v n` means that `g` can transform `u` to `v` in `n` rewriting steps. -/
inductive DerivesSteps (g : ContextFreeGrammar.{uN} T) : List (Symbol T g.NT) → List (Symbol T g.NT) → ℕ → Prop
  | refl (w : List (Symbol T g.NT)) : g.DerivesSteps w w 0
  | tail (u v w : List (Symbol T g.NT)) (n : ℕ) : g.DerivesSteps u v n → g.Produces v w → g.DerivesSteps u w n.succ

lemma derives_iff_derivesSteps (g : ContextFreeGrammar.{uN} T) (v w : List (Symbol T g.NT)) :
    g.Derives v w ↔ ∃ n : ℕ, g.DerivesSteps v w n := by
  constructor
  · intro hgvw
    induction hgvw with
    | refl =>
      use 0
      left
    | tail _ last ih =>
      obtain ⟨n, ihn⟩ := ih
      use n.succ
      right
      · exact ihn
      · exact last
  · intro ⟨n, hgvwn⟩
    induction hgvwn with
    | refl => rfl
    | tail _ _ _ _ last ih => exact ih.trans_produces last

lemma mem_language_iff_derivesSteps (g : ContextFreeGrammar.{uN} T) (w : List T) :
    w ∈ g.language ↔ ∃ n, g.DerivesSteps [Symbol.nonterminal g.initial] (List.map Symbol.terminal w) n := by
  rw [mem_language_iff, derives_iff_derivesSteps]

variable {g : ContextFreeGrammar.{uN} T}

lemma DerivesSteps.zero_steps (w : List (Symbol T g.NT)) : g.DerivesSteps w w 0 := by
  left

lemma Produces.single_step {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) : g.DerivesSteps v w 1 := by
  right
  left
  exact hvw

variable {n : ℕ}

lemma DerivesSteps.trans_produces {u v w : List (Symbol T g.NT)} (huv : g.DerivesSteps u v n) (hvw : g.Produces v w) :
    g.DerivesSteps u w n.succ :=
  DerivesSteps.tail u v w n huv hvw

@[trans]
lemma DerivesSteps.trans {u v w : List (Symbol T g.NT)} {m : ℕ} (huv : g.DerivesSteps u v n) (hvw : g.DerivesSteps v w m) :
    g.DerivesSteps u w (n + m) := by
  induction hvw with
  | refl => exact huv
  | tail _ _ _ _ last ih => exact trans_produces ih last

lemma Produces.trans_derivesSteps {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hvw : g.DerivesSteps v w n) :
    g.DerivesSteps u w n.succ :=
  n.succ_eq_one_add ▸ huv.single_step.trans hvw

lemma DerivesSteps.tail_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesSteps u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.DerivesSteps u v n ∧ g.Produces v w := by
  cases huw with
  | tail v w n huv hvw =>
    use v

lemma DerivesSteps.head_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesSteps u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.DerivesSteps v w n := by
  induction n generalizing w with
  | zero =>
    cases huw with
    | tail v w n huv hvw =>
      cases huv with
      | refl => exact ⟨w, hvw, zero_steps w⟩
  | succ m ih =>
    cases huw with
    | tail v w n huv hvw =>
      obtain ⟨x, hux, hxv⟩ := ih huv
      exact ⟨x, hux, hxv.trans_produces hvw⟩

/-- Add extra prefix to context-free deriving (number of steps unchanged). -/
lemma DerivesSteps.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesSteps v w n) (p : List (Symbol T g.NT)) :
    g.DerivesSteps (p ++ v) (p ++ w) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to context-free deriving (number of steps unchanged). -/
lemma DerivesSteps.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesSteps v w n) (p : List (Symbol T g.NT)) :
    g.DerivesSteps (v ++ p) (w ++ p) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_right p

@[elab_as_elim]
lemma DerivesSteps.induction_refl_head {b : List (Symbol T g.NT)}
    {P : ∀ n : ℕ, ∀ a : List (Symbol T g.NT), g.DerivesSteps a b n → Prop}
    (refl : P 0 b (DerivesSteps.zero_steps b))
    (head : ∀ {n a c} (hac : g.Produces a c) (hcb : g.DerivesSteps c b n),
      P n c hcb → P n.succ a (hac.trans_derivesSteps hcb))
    {a : List (Symbol T g.NT)} (hab : g.DerivesSteps a b n) :
    P n a hab := by
  induction hab with
  | refl => exact refl
  | tail _ _ _ _ last ih =>
    apply ih
    · exact head last _ refl
    · intro _ _ _ produc deriv
      exact head produc (deriv.tail _ last)

private lemma DerivesSteps.empty_of_append_left_aux {w u v : List (Symbol T g.NT)} {n : ℕ}
  (hwe : g.DerivesSteps w [] n) (heq : w = u ++ v) : ∃ m ≤ n, g.DerivesSteps u [] m := by
  revert u v
  induction hwe using DerivesSteps.induction_refl_head with
  | refl => simp[DerivesSteps.zero_steps]
  | @head m  u v huv _ ih =>
    intro x y heq
    obtain ⟨r, rin, huv⟩ := huv
    obtain ⟨p, q, h1, h2⟩ := ContextFreeRule.Rewrites.exists_parts huv
    rw[heq, List.append_assoc, List.append_eq_append_iff] at h1
    cases h1 with
    | inl h =>
      obtain ⟨x', hx, _⟩ := h
      have hveq : v = x ++ (x' ++ r.output ++ q) := by simp[h2, hx]
      obtain ⟨m', hm, hd⟩ := ih hveq
      use m'
      constructor <;> tauto
    | inr h =>
      obtain ⟨x', hx, hr⟩ := h
      cases x' with
      | nil =>
        have hveq : v = x ++ (r.output ++ q) := by simp[hx, h2]
        obtain ⟨m', hm, hd⟩ := ih hveq
        use m'
        constructor <;> tauto
      | cons h t =>
        obtain ⟨_, _⟩ := hr
        simp[←List.append_assoc] at h2
        obtain ⟨m', hm, hd⟩ := ih h2
        use m'.succ
        constructor
        · exact Nat.succ_le_succ hm
        · apply Produces.trans_derivesSteps
          use r
          constructor
          exact rin
          rw[ContextFreeRule.rewrites_iff]
          use p, t
          constructor
          · simp[hx]
          · rfl
          exact hd

lemma DerivesSteps.empty_of_append_left {u v : List (Symbol T g.NT)} (huv : g.DerivesSteps (u ++ v) [] n) :
    ∃ m ≤ n, g.DerivesSteps u [] m := by
  apply empty_of_append_left_aux <;> tauto

lemma DerivesSteps.empty_of_append_right_aux {w u v : List (Symbol T g.NT)} {n : ℕ}
  (hwe : g.DerivesSteps w [] n) (heq : w = u ++ v) : ∃ m ≤ n, g.DerivesSteps v [] m := by
  revert u v
  induction hwe using DerivesSteps.induction_refl_head with
  | refl => simp[DerivesSteps.zero_steps]
  | @head m u v huv _ ih =>
    intro x y heq
    obtain ⟨r, rin, huv⟩ := huv
    obtain ⟨p, q, h1, h2⟩ := ContextFreeRule.Rewrites.exists_parts huv
    rw[heq, List.append_assoc, List.append_eq_append_iff] at h1
    cases h1 with
    | inl h =>
      obtain ⟨y', h1 , hy⟩ := h
      repeat rw[h1, List.append_assoc, List.append_assoc] at h2
      obtain ⟨m', hm, hd⟩ := ih h2
      use m'.succ
      constructor
      · exact Nat.succ_le_succ hm
      · apply Produces.trans_derivesSteps
        use r
        constructor
        exact rin
        rw[ContextFreeRule.rewrites_iff]
        use y', q
        constructor
        · simp
          exact hy
        · rfl
        simp[hd]
    | inr h =>
      obtain ⟨q', hx, hq⟩ := h
      cases q' with
      | nil =>
        simp at hq h2
        obtain ⟨m', hm, hd⟩ := ih h2
        use m'.succ
        constructor
        · exact Nat.succ_le_succ hm
        · apply Produces.trans_derivesSteps
          use r
          constructor
          exact rin
          rw[ContextFreeRule.rewrites_iff]
          use [], q
          constructor
          · simp
            tauto
          · rfl
          exact hd
      | cons h t =>
        obtain ⟨_,_⟩ := hq
        simp at h2
        repeat rw[←List.append_assoc] at h2
        obtain ⟨m', hm, hd⟩ := ih h2
        use m'
        constructor
        · exact Nat.le_succ_of_le hm
        · exact hd

lemma DerivesSteps.empty_of_append_right {u v : List (Symbol T g.NT)} (huv : g.DerivesSteps (u ++ v) [] n) :
    ∃ m ≤ n, g.DerivesSteps v [] m := by
  apply empty_of_append_right_aux <;> tauto

lemma DerivesSteps.empty_of_append {w u v: List (Symbol T g.NT)} {n : ℕ}
  (hwe : g.DerivesSteps (w ++ u ++ v) [] n) : ∃ m ≤ n, g.DerivesSteps u [] m := by
  obtain ⟨m1, hm1n, hm1e⟩ := DerivesSteps.empty_of_append_left hwe
  obtain ⟨m2, hm2n, hm2e⟩ := DerivesSteps.empty_of_append_right hm1e
  use m2
  exact ⟨Nat.le_trans hm2n hm1n, hm2e⟩
