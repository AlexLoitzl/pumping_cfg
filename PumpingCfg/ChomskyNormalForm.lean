/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/

import Mathlib.Computability.ContextFreeGrammar

/-- Rule that rewrites a single nonterminal to a single terminal or a pair of nonterminals. -/
inductive ChomskyNormalFormRule.{uT,uN} (T : Type uT) (N : Type uN)
  /-- First kind of rule, rewriting a nonterminal `n` to a single terminal `t`. -/
  | leaf (n : N) (t : T) : ChomskyNormalFormRule T N
  /-- Second kind of rule,  rewriting a nonterminal `n` to a pair of nonterminal `lr`. -/
  | node (n l r : N) : ChomskyNormalFormRule T N
deriving DecidableEq

structure ChomskyNormalFormGrammar.{uN,uT} (T : Type uT) where
  /-- Type of nonterminals. -/
  NT : Type uN
  /-- Initial nonterminal. -/
  initial : NT
  /-- Rewrite rules. -/
  rules : Finset (ChomskyNormalFormRule T NT)

universe uT uN
variable {T : Type uT}

namespace ChomskyNormalFormRule
variable {N : Type uN} {r : ChomskyNormalFormRule T N} {u v : List (Symbol T N)}

/-- The input of a CNF rule, similar to `ContextFreeRule.input` -/
@[simp]
def input (r : ChomskyNormalFormRule T N) :=
  match r with
  | leaf n _ => n
  | node n _ _ => n

/-- The output of a CNF rule, similar to `ContextFreeRule.output` -/
@[simp]
def output (r : ChomskyNormalFormRule T N) :=
  match r with
  | leaf _ t => [Symbol.terminal t]
  | node _ l r => [Symbol.nonterminal l, Symbol.nonterminal r]

/-- Inductive definition of a single application of a given cnf rule `r` to a string `u`;
`r.Rewrites u v` means that the `r` sends `u` to `v` (there may be multiple such strings `v`). -/
inductive Rewrites : (ChomskyNormalFormRule T N) → List (Symbol T N) → List (Symbol T N) → Prop
  /-- The replacement is at the start of the remaining string and the rule is a leaf rule. -/
  | head_leaf (n : N) (t : T) (s : List (Symbol T N)) :
      Rewrites (leaf n t) (Symbol.nonterminal n :: s) (Symbol.terminal t :: s)
  /-- The replacement is at the start of the remaining string and the rule is a node rule. -/
  | head_node (n l r : N) (s : List (Symbol T N)) :
      Rewrites (node n l r) (Symbol.nonterminal n :: s) (Symbol.nonterminal l :: Symbol.nonterminal r :: s)
  /-- The replacement is at the start of the remaining string. -/
  | cons (r : ChomskyNormalFormRule T N) (x : Symbol T N) {s₁ s₂ : List (Symbol T N)} (hrs : Rewrites r s₁ s₂) :
      Rewrites r (x :: s₁) (x :: s₂)

lemma Rewrites.exists_parts (hr : r.Rewrites u v) :
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

lemma Rewrites.input_output : r.Rewrites [.nonterminal r.input] r.output := by
  cases r
  · simpa using head_leaf _ _ []
  · simpa using head_node _ _ _ []

lemma rewrites_of_exists_parts (r : ChomskyNormalFormRule T N) (p q : List (Symbol T N)) :
    r.Rewrites (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
    induction p with
    | nil =>
      simp
      cases r <;> constructor
    | cons _ _ h =>
      constructor
      exact h

/-- Rule `r` rewrites string `u` to string `v` iff they share both a prefix `p` and postfix `q`
such that the remaining middle part of `u` is the input of `r` and the remaining middle part
of `v` is the output of `r`. -/
theorem rewrites_iff {r : ChomskyNormalFormRule T N} (u v : List (Symbol T N)) :
    r.Rewrites u v ↔ ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
  constructor
  · apply Rewrites.exists_parts
  · rintro ⟨p, q, rfl, rfl⟩
    apply rewrites_of_exists_parts

/-- Add extra prefix to cnf rewriting. -/
lemma Rewrites.append_left {r : ChomskyNormalFormRule T N} {v w : List (Symbol T N)}
    (hvw : r.Rewrites v w) (p : List (Symbol T N)) : r.Rewrites (p ++ v) (p ++ w) := by
  induction p <;> tauto

/-- Add extra postfix to cnf rewriting. -/
lemma Rewrites.append_right {r : ChomskyNormalFormRule T N} {v w : List (Symbol T N)}
    (hvw : r.Rewrites v w) (p : List (Symbol T N)) : r.Rewrites (v ++ p) (w ++ p) := by
  induction hvw <;> tauto

end ChomskyNormalFormRule

namespace ChomskyNormalFormGrammar

/-- Given a cnf grammar `g` and strings `u` and `v`
`g.Produces u v` means that one step of a cnf transformation by a rule from `g` sends
`u` to `v`. -/
def Produces (g : ChomskyNormalFormGrammar T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.Rewrites u v

/-- Given a cnf grammar `g` and strings `u` and `v`
`g.Derives u v` means that `g` can transform `u` to `v` in some number of rewriting steps. -/
abbrev Derives (g : ChomskyNormalFormGrammar T) : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Produces

/-- Given a cnf grammar `g` and a string `s`
`g.Generates s` means that `g` can transform its initial nonterminal to `s` in some number of
rewriting steps. -/
def Generates (g : ChomskyNormalFormGrammar T) (s : List (Symbol T g.NT)) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] s

/-- The language (set of words) that can be generated by a given cnf grammar `g`. -/
def language (g : ChomskyNormalFormGrammar T) : Language T :=
  { w | g.Generates (w.map Symbol.terminal) }

/-- A given word `w` belongs to the language generated by a given cnf grammar `g` iff
`g` can derive the word `w` (wrapped as a string) from the initial nonterminal of `g` in some
number of steps. -/
@[simp]
lemma mem_language_iff (g : ChomskyNormalFormGrammar T) (w : List T) :
    w ∈ g.language ↔ g.Generates (List.map Symbol.terminal w) := by
  rfl

variable {g : ChomskyNormalFormGrammar T}

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

/-- Add extra prefix to cnf producing. -/
lemma Produces.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (p ++ v) (p ++ w) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_left p⟩

/-- Add extra postfix to cnf producing. -/
lemma Produces.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (v ++ p) (w ++ p) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_right p⟩

/-- Add extra prefix to cnf deriving. -/
lemma Derives.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (p ++ v) (p ++ w) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to cnf deriving. -/
lemma Derives.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (v ++ p) (w ++ p) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_right p

theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
  {u : List (Symbol T g.NT)} (h : g.Derives u v)
  (refl : P v (Derives.refl v))
  (head : ∀ {u w} (h' : g.Produces u w) (h : g.Derives w v), P w h → P u (h.head h')) : P u h :=
  Relation.ReflTransGen.head_induction_on h refl head

end ChomskyNormalFormGrammar
