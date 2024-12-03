/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/

import Mathlib.Computability.ContextFreeGrammar

inductive CNFRule (T N : Type)
  | leaf (n : N) (t : T) : CNFRule T N
  | node (n l r : N) : CNFRule T N
deriving DecidableEq

structure CNF (T : Type) where
  /-- Type of nonterminals. -/
  NT : Type
  /-- Initial nonterminal. -/
  initial : NT
  /-- Rewrite rules. -/
  rules : Finset (CNFRule T NT)

-- Type of terminals.
variable {T : Type}

namespace CNFRule

-- Type of nonterminals.
variable {N : Type}

@[simp]
def input (r : CNFRule T N) :=
  match r with
  | leaf n _ => n
  | node n _ _ => n

@[simp]
def output (r : CNFRule T N) :=
  match r with
  | leaf _ t => [Symbol.terminal t]
  | node _ l r => [Symbol.nonterminal l, Symbol.nonterminal r]

inductive Rewrites : (CNFRule T N) → List (Symbol T N) → List (Symbol T N) → Prop
  | head_leaf (n : N) (t : T) (s : List (Symbol T N)) :
      Rewrites (leaf n t) (Symbol.nonterminal n :: s) (Symbol.terminal t :: s)
  | head_node (n l r : N) (s : List (Symbol T N)) :
      Rewrites (node n l r) (Symbol.nonterminal n :: s) (Symbol.nonterminal l :: Symbol.nonterminal r :: s)
  | cons (r : CNFRule T N) (x : Symbol T N) {s₁ s₂ : List (Symbol T N)} (hrs : Rewrites r s₁ s₂) :
      Rewrites r (x :: s₁) (x :: s₂)

lemma Rewrites.exists_parts {r : CNFRule T N} {u v : List (Symbol T N)} (hr : r.Rewrites u v) :
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
      cases r <;> constructor
    | cons _ _ h =>
      constructor
      exact h

theorem rewrites_iff {r : CNFRule T N} (u v : List (Symbol T N)) :
    r.Rewrites u v ↔ ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
  constructor
  · apply Rewrites.exists_parts
  · rintro ⟨p, q, rfl, rfl⟩
    apply rewrites_of_exists_parts

lemma Rewrites.append_left {r : CNFRule T N} {v w : List (Symbol T N)}
    (hvw : r.Rewrites v w) (p : List (Symbol T N)) : r.Rewrites (p ++ v) (p ++ w) := by
  induction p <;> tauto

lemma Rewrites.append_right {r : CNFRule T N} {v w : List (Symbol T N)}
    (hvw : r.Rewrites v w) (p : List (Symbol T N)) : r.Rewrites (v ++ p) (w ++ p) := by
  induction hvw <;> tauto

end CNFRule

namespace CNF

def Produces (g : CNF T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.Rewrites u v

abbrev Derives (g : CNF T) : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Produces

def Generates (g : CNF T) (s : List (Symbol T g.NT)) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] s

def language (g : CNF T) : Language T :=
  { w | g.Generates (w.map Symbol.terminal) }

@[simp]
lemma mem_language_iff (g : CNF T) (w : List T) :
    w ∈ g.language ↔ g.Generates (List.map Symbol.terminal w) := by
  rfl

variable {g : CNF T}

@[refl]
lemma Derives.refl (w : List (Symbol T g.NT)) : g.Derives w w :=
  Relation.ReflTransGen.refl

lemma Produces.single {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) : g.Derives v w :=
  Relation.ReflTransGen.single hvw

@[trans]
lemma Derives.trans {u v w : List (Symbol T g.NT)} (huv : g.Derives u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  Relation.ReflTransGen.trans huv hvw

lemma Derives.trans_produces {u v w : List (Symbol T g.NT)}
    (huv : g.Derives u v) (hvw : g.Produces v w) :
    g.Derives u w :=
  huv.trans hvw.single

lemma Produces.trans_derives {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  huv.single.trans hvw

lemma Derives.eq_or_head {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.Derives v w :=
  Relation.ReflTransGen.cases_head huw

lemma Derives.eq_or_tail {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Derives u v ∧ g.Produces v w :=
  (Relation.ReflTransGen.cases_tail huw).casesOn (Or.inl ∘ Eq.symm) Or.inr

lemma Produces.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (p ++ v) (p ++ w) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_left p⟩

lemma Produces.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (v ++ p) (w ++ p) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_right p⟩

lemma Derives.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (p ++ v) (p ++ w) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_left p

lemma Derives.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (v ++ p) (w ++ p) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_right p

end CNF
