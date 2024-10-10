/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
-- Type of terminals.
variable {T : Type}

-- Non-terminals need to be restricted. Since the number of rules is finite,
-- we can also only have finite number of non-terminals

inductive CNFRule (T : Type) (N : Type)
  | leaf (n:N) (t:T) : CNFRule T N
  | node (n ln rn: N) : CNFRule T N

structure CNF (T : Type) where
  /-- Type of nonterminals. -/
  NT : Type
  /-- Initial nonterminal. -/
  initial : NT
  /-- Rewrite rules. -/
  rules : List (CNFRule T NT)

namespace CNFRule

@[simp]
def input (r: CNFRule T N) :=
  match r with
  | leaf n _ => n
  | node n _ _ => n

@[simp]
def output (r: CNFRule T N) :=
  match r with
  | leaf _ t => [Symbol.terminal t]
  | node _ ln rn => [Symbol.nonterminal ln, Symbol.nonterminal rn]

inductive Rewrites : (CNFRule T N) → List (Symbol T N) → List (Symbol T N) → Prop
  | head_leaf (n: N) (t: T) (s : List (Symbol T N)) :
      Rewrites (leaf n t) (Symbol.nonterminal n :: s) (Symbol.terminal t :: s)
  | head_node (n ln rn: N) (s : List (Symbol T N)) :
      Rewrites (node n ln rn) (Symbol.nonterminal n :: s) (Symbol.nonterminal ln :: Symbol.nonterminal rn :: s)
  | cons (r: CNFRule T N) (x: Symbol T N) {s₁ s₂ : List (Symbol T N)} (hrs: Rewrites r s₁ s₂) :
      Rewrites r (x :: s₁) (x :: s₂)

lemma Rewrites.exists_parts {r : CNFRule T N} {u v : List (Symbol T N)}
    (hr : r.Rewrites u v) :
    ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
    induction hr with
    | head_leaf _ _ s | head_node _ _ _ s =>
      use [], s
      simp
    | cons r x rw hrs =>
      rcases hrs with ⟨p, q, rfl, rfl⟩
      use x :: p, q
      simp

lemma rewrites_of_exists_parts (r : CNFRule T N) (p q : List (Symbol T N)) :
    r.Rewrites (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
    induction p with
    | nil =>
      simp
      match r with
      | leaf n t | node n ln rn =>
        constructor
    | cons hd tl h =>
      constructor
      apply h

theorem rewrites_iff {r : CNFRule T N} (u v : List (Symbol T N)) :
    r.Rewrites u v ↔ ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
      constructor
      · intros
        apply Rewrites.exists_parts
        tauto
      · intro h
        rcases h with ⟨p, q, rfl, rfl⟩
        apply rewrites_of_exists_parts

lemma Rewrites.append_left {r : CNFRule T N} {v w : List (Symbol T N)}
    (hvw : r.Rewrites v w) (p : List (Symbol T N)) : r.Rewrites (p ++ v) (p ++ w) := by
    induction p with
    | nil =>
      simp
      apply hvw
    | cons hd tl ih =>
      constructor
      apply ih

lemma Rewrites.append_right {r : CNFRule T N} {v w : List (Symbol T N)}
    (hvw : r.Rewrites v w) (p : List (Symbol T N)) : r.Rewrites (v ++ p) (w ++ p) := by
    induction hvw with
    | head_leaf | head_node =>
      simp
      constructor
    | cons hd _ _ ih =>
      constructor
      apply ih

end CNFRule

-- Why do I have to write Language.IsContextfree rather than L.isContextfree?
-- I definitely need to restrict the type of variables with Fintype
theorem pumping_lemma {T : Type} {L : Language T} (cf: Language.IsContextFree L) :
  ∃ p : ℕ, ∀ w ∈ L, w.length ≥ p → ∃ u v x y z : List T,
    w = u ++ v ++ x ++ y ++ z ∧
    (v ++ y).length > 0       ∧
    (v ++ x ++ y).length ≤ p  ∧
    ∀ i : ℕ, u ++ (v ^^ i) ++ x ++ y ^^ i ++ z ∈ L :=
  sorry
