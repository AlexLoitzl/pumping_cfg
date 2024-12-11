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
`g.DerivesIn u v n` means that `g` can transform `u` to `v` in `n` rewriting steps. -/
inductive DerivesIn (g : ContextFreeGrammar.{uN} T) : List (Symbol T g.NT) → List (Symbol T g.NT) → ℕ → Prop
  | refl (w : List (Symbol T g.NT)) : g.DerivesIn w w 0
  | tail (u v w : List (Symbol T g.NT)) (n : ℕ) : g.DerivesIn u v n → g.Produces v w → g.DerivesIn u w n.succ

lemma derives_iff_derivesIn (g : ContextFreeGrammar.{uN} T) (v w : List (Symbol T g.NT)) :
    g.Derives v w ↔ ∃ n : ℕ, g.DerivesIn v w n := by
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

lemma mem_language_iff_derivesIn (g : ContextFreeGrammar.{uN} T) (w : List T) :
    w ∈ g.language ↔ ∃ n, g.DerivesIn [Symbol.nonterminal g.initial] (w.map Symbol.terminal) n := by
  rw [mem_language_iff, derives_iff_derivesIn]

variable {g : ContextFreeGrammar.{uN} T}

lemma DerivesIn.zero_steps (w : List (Symbol T g.NT)) : g.DerivesIn w w 0 := by
  left

lemma Produces.single_step {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) : g.DerivesIn v w 1 := by
  right
  left
  exact hvw

variable {n : ℕ}

lemma DerivesIn.trans_produces {u v w : List (Symbol T g.NT)} (huv : g.DerivesIn u v n) (hvw : g.Produces v w) :
    g.DerivesIn u w n.succ :=
  DerivesIn.tail u v w n huv hvw

@[trans]
lemma DerivesIn.trans {u v w : List (Symbol T g.NT)} {m : ℕ} (huv : g.DerivesIn u v n) (hvw : g.DerivesIn v w m) :
    g.DerivesIn u w (n + m) := by
  induction hvw with
  | refl => exact huv
  | tail _ _ _ _ last ih => exact trans_produces ih last

lemma Produces.trans_derivesIn {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hvw : g.DerivesIn v w n) :
    g.DerivesIn u w n.succ :=
  n.succ_eq_one_add ▸ huv.single_step.trans hvw

lemma DerivesIn.tail_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.DerivesIn u v n ∧ g.Produces v w := by
  cases huw with
  | tail v w n huv hvw =>
    use v

lemma DerivesIn.head_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.DerivesIn v w n := by
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
lemma DerivesIn.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesIn v w n) (p : List (Symbol T g.NT)) :
    g.DerivesIn (p ++ v) (p ++ w) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to context-free deriving (number of steps unchanged). -/
lemma DerivesIn.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesIn v w n) (p : List (Symbol T g.NT)) :
    g.DerivesIn (v ++ p) (w ++ p) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_right p


lemma DerivesIn.append_split {p q w : List (Symbol T g.NT)} {n : ℕ} (hpqw : g.DerivesIn (p ++ q) w n) :
  ∃ x y m1 m2, w = x ++ y ∧ g.DerivesIn p x m1 ∧ g.DerivesIn q y m2 ∧ n = m1 + m2 := by
  cases n with
  | zero =>
    use p, q, 0, 0
    constructor
    · cases hpqw; rfl
    · exact ⟨DerivesIn.refl p, DerivesIn.refl q, rfl⟩
  | succ n =>
    obtain ⟨v, hp, hd⟩ := hpqw.head_of_succ
    obtain ⟨r, hrin, hr⟩ := hp
    obtain ⟨p', q', heq, hv⟩ := hr.exists_parts
    simp at heq
    have h {p q x y : List (Symbol T g.NT)} {v : Symbol T g.NT} (h: p ++ q = x ++ v :: y) :
         (∃ w, y = w ++ q ∧ p = x ++ v :: w) ∨ (∃ w, x = p ++ w ∧ q = w ++ v :: y) := by
      have h1 := List.append_eq_append_iff.1 h
      cases h1 <;> rename_i h1
      · obtain ⟨a, heq, hq⟩ := h1
        right
        use a
      · obtain ⟨a, heq, hq⟩ := h1
        cases a with
        | nil =>
          right
          use []
          rw [heq, hq]
          constructor
          repeat rw [List.append_nil]
          rfl
        | cons hd tl =>
          left
          use tl
          simp at hq
          rw [hq.1]
          exact ⟨hq.2, heq⟩
    rcases h heq with ⟨a, hq', hp⟩ | ⟨a, hp', hq⟩
    · rw[hv, hq', ← List.append_assoc] at hd
      obtain ⟨x, y, m1, m2, hw, hd1, hd2, hn⟩ := hd.append_split
      use x, y, (m1 + 1), m2
      constructor
      · exact hw
      · constructor
        · apply Produces.trans_derivesIn
          use r
          constructor
          · exact hrin
          · rw [hp, ← List.singleton_append, ← List.append_assoc]
            apply r.rewrites_of_exists_parts
          · exact hd1
        · exact ⟨hd2, by omega⟩
    · rw[hv, hp', List.append_assoc, List.append_assoc] at hd
      obtain ⟨x, y, m1, m2, hw, hd1, hd2, hn⟩ := hd.append_split
      use x, y, m1, m2 + 1
      constructor
      · exact hw
      · constructor
        · exact hd1
        · constructor
          · apply Produces.trans_derivesIn
            use r
            constructor
            · exact hrin
            · rw [hq, ← List.singleton_append, ← List.append_assoc]
              apply r.rewrites_of_exists_parts
            · rwa [List.append_assoc]
          · omega

lemma DerivesIn.three_split {p q r w : List (Symbol T g.NT)} {n : ℕ} (h : g.DerivesIn (p ++ q ++ r) w n) :
  ∃ x y z m1 m2 m3, w = x ++ y ++ z ∧ g.DerivesIn p x m1 ∧ g.DerivesIn q y m2
    ∧ g.DerivesIn r z m3 ∧ n = m1 + m2 + m3 := by
  obtain ⟨x', z, m1', m3, hw2, hd1', hd3, hn2⟩ := h.append_split
  obtain ⟨x, y, m1, m2, hw1, hd1, hd2, hn1⟩ := hd1'.append_split
  use x, y, z, m1, m2, m3
  constructor
  rw [hw2, hw1]
  constructor
  exact hd1
  constructor
  exact hd2
  constructor
  exact hd3
  rw [hn2, hn1]


@[elab_as_elim]
lemma DerivesIn.head_induction_on {b : List (Symbol T g.NT)}
    {P : ∀ n : ℕ, ∀ a : List (Symbol T g.NT), g.DerivesIn a b n → Prop}
    (refl : P 0 b (DerivesIn.zero_steps b))
    (head : ∀ {n a c} (hac : g.Produces a c) (hcb : g.DerivesIn c b n),
      P n c hcb → P n.succ a (hac.trans_derivesIn hcb))
    {a : List (Symbol T g.NT)} (hab : g.DerivesIn a b n) :
    P n a hab := by
  induction hab with
  | refl => exact refl
  | tail _ _ _ _ last ih =>
    apply ih
    · exact head last _ refl
    · intro _ _ _ produc deriv
      exact head produc (deriv.tail _ _ _ _ last)
