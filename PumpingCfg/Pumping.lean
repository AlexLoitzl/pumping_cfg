/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/

import Mathlib.Computability.ContextFreeGrammar
import PumpingCfg.Utils

-- Non-terminals need to be restricted. Since the number of rules is finite,
-- we can also only have finite number of non-terminals

inductive CNFRule (T N : Type)
  | leaf (n : N) (t : T) : CNFRule T N
  | node (n l r : N) : CNFRule T N

structure CNF (T : Type) where
  /-- Type of nonterminals. -/
  NT : Type
  /-- Initial nonterminal. -/
  initial : NT
  /-- Rewrite rules. -/
  rules : List (CNFRule T NT)

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

def toCFGRule (r : CNFRule T N) : ContextFreeRule T N :=
  match r with
  | leaf n t => { input := n, output := [Symbol.terminal t] }
  | node n l r => { input := n, output := [Symbol.nonterminal l, Symbol.nonterminal r] }

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
      apply h

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

lemma Rewrites.toCFGRule_match {v w : List (Symbol T N)} {r : CNFRule T N} (hwv : r.Rewrites v w) :
    r.toCFGRule.Rewrites v w := by
  induction hwv <;> tauto

lemma Rewrites.match_toCFGRule {v w : List (Symbol T N)} {r : CNFRule T N} (hwv : r.toCFGRule.Rewrites v w) :
    r.Rewrites v w := by
  induction hwv with
  | head => cases r <;> tauto
  | cons x _ ih => exact Rewrites.cons r x ih

end CNFRule

namespace CNF

def Produces (g : CNF T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.Rewrites u v

abbrev Derives (g : CNF T) : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Produces

def Generates (g : CNF T) (s : List (Symbol T g.NT)) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] s

def language (g : CNF T) : Language T :=
  { w | g.Generates (List.map Symbol.terminal w) }

@[simp]
lemma mem_language_iff (g : CNF T) (w : List T) :
    w ∈ g.language ↔ g.Generates (List.map Symbol.terminal w) := by
  rfl

def toCFG (g : CNF T) : ContextFreeGrammar T where
  NT := g.NT
  initial := g.initial
  rules := g.rules.map CNFRule.toCFGRule

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

lemma Produces.toCFG_match {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) : g.toCFG.Produces v w := by
  rcases hvw with ⟨r, rin, hrw⟩
  exact ⟨r.toCFGRule, List.mem_map_of_mem _ rin, CNFRule.Rewrites.toCFGRule_match hrw⟩

lemma Derives.toCFG_match {v w : List (Symbol T g.NT)} (hvw : g.Derives v w) : g.toCFG.Derives v w := by
  induction hvw with
  | refl => rfl
  | tail _ last ih =>
    apply ih.trans_produces
    apply Produces.toCFG_match last

lemma Generates.toCFG_match {s : List (Symbol T g.NT)} (hg : g.Generates s) : g.toCFG.Generates s :=
  Derives.toCFG_match hg

lemma Produces.match_toCFG {v w : List (Symbol T g.NT)} (hvw : g.toCFG.Produces v w) : g.Produces v w := by
  rcases hvw with ⟨r, rin, hrw⟩
  simp only [toCFG, List.mem_map] at rin
  rcases rin with ⟨r', rin', rfl⟩
  exact ⟨r', rin', CNFRule.Rewrites.match_toCFGRule hrw⟩

lemma Derives.match_toCFG {v w : List (Symbol T g.NT)} (hvw : g.toCFG.Derives v w) : g.Derives v w := by
  induction hvw with
  | refl => rfl
  | tail _ last ih =>
    apply ih.trans_produces
    apply Produces.match_toCFG last

lemma Generates.match_toCFG {s : List (Symbol T g.NT)} (hg : g.toCFG.Generates s) : g.Generates s :=
  Derives.match_toCFG hg

theorem toCFG_correct {s : List (Symbol T g.NT)} : g.Generates s ↔ g.toCFG.Generates s :=
  ⟨Generates.toCFG_match, Generates.match_toCFG⟩

end CNF

namespace ContextFreeGrammar

variable {g : ContextFreeGrammar T}

variable [DecidableEq g.NT]

-- All lefthand side non-terminals
def generators : Finset g.NT := (g.rules.map (fun r => r.input)).toFinset

lemma in_generators {r : ContextFreeRule T g.NT} (h : r ∈ g.rules) :
  r.input ∈ g.generators := by
  unfold generators
  revert h
  induction g.rules with
  | nil => simp
  | cons hd tl ih =>
    simp at ih ⊢
    rintro (c1 | c2)
    · left
      rw[c1]
    · right
      exact ih c2

def rule_is_nullable (nullable : Finset g.NT) (r : ContextFreeRule T g.NT) : Bool :=
  let symbol_is_nullable : (Symbol T g.NT) → Bool := fun s =>
    match s with
    | Symbol.terminal _ => False
    | Symbol.nonterminal nt => nt ∈ nullable
  ∀ s ∈ r.output, symbol_is_nullable s

def add_if_nullable (r : ContextFreeRule T g.NT) (nullable : Finset g.NT) : Finset g.NT :=
  if rule_is_nullable nullable r then insert r.input nullable else nullable

lemma add_if_nullable_subset_generators {r : ContextFreeRule T g.NT} {nullable : Finset g.NT}
  (p : nullable ⊆ g.generators) (hin : r ∈ g.rules) :
  add_if_nullable r nullable ⊆ g.generators := by
  unfold add_if_nullable
  split
  · exact Finset.insert_subset (in_generators hin) p
  · exact p

def add_nullables (nullable : Finset g.NT) : Finset g.NT :=
  g.rules.attach.foldr (fun ⟨r, _⟩ => add_if_nullable r) nullable

lemma add_nullables_subset_generators (nullable : Finset g.NT) (p : nullable ⊆ g.generators) :
  add_nullables nullable ⊆ g.generators := by
  unfold add_nullables
  induction g.rules.attach with
  | nil => simp; exact p
  | cons hd tl ih => exact add_if_nullable_subset_generators ih hd.2

lemma add_if_nullable_subset (r : ContextFreeRule T g.NT) (nullable : Finset g.NT) :
  nullable ⊆ (add_if_nullable r nullable) := by
  unfold add_if_nullable
  split <;> simp

lemma nullable_subset_add_nullables (nullable : Finset  g.NT) :
  nullable ⊆ (add_nullables nullable) := by
  unfold add_nullables
  induction g.rules.attach with
  | nil => simp
  | cons hd tl ih =>
    apply subset_trans ih
    apply add_if_nullable_subset hd.1

-- Fixpoint iteration to compute all nullable variables
-- I can't quite get functional induction to work here :(
-- NOTE If we instead shrink the set of generators the termination argument should
-- be easier. For correctness we'll probably have to reason about the contents of generators

lemma generators_limits_nullable (nullable : Finset g.NT) (p : nullable ⊆ g.generators)
  (hneq : nullable ≠ add_nullables nullable) :
  (g.generators).card - (add_nullables nullable).card < (g.generators).card - nullable.card := by
  have h := HasSubset.Subset.ssubset_of_ne (nullable_subset_add_nullables nullable) hneq
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_lt_of_le
    · apply Finset.card_lt_card h
    · exact Finset.card_le_card (add_nullables_subset_generators nullable p)
  · apply Finset.card_lt_card h

def add_nullables_iter (nullable : Finset g.NT) (p : nullable ⊆ g.generators) : Finset g.NT :=
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
def compute_nullables : Finset g.NT :=
  add_nullables_iter ∅ generators.empty_subset

def NullableNonTerminal (v : g.NT) : Prop := g.Derives [Symbol.nonterminal v] []

-- That's annoying
omit [DecidableEq g.NT] in
lemma all_nullable_nullable (w : List (Symbol T g.NT)) (h: ∀ v ∈ w, g.Derives [v] []) :
  g.Derives w [] := by
  induction w with
  | nil => exact Derives.refl []
  | cons hd tl ih =>
    change g.Derives ([hd] ++ tl) []
    apply Derives.trans
    · apply Derives.append_right
      apply h
      simp
    · simp
      apply ih
      intro v hv
      apply h
      right
      exact hv

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
  apply all_nullable_nullable
  intro v hvin
  simp at hr
  specialize hr v hvin
  cases v <;> simp at hr
  apply hin _ hr

lemma add_nullables_nullable (nullable : Finset g.NT) (hin : ∀ v ∈ nullable, NullableNonTerminal v) :
  ∀ v ∈ add_nullables nullable, NullableNonTerminal v := by
  unfold add_nullables
  induction g.rules.attach with
  | nil =>
    simp
    apply hin
  | cons hd tl ih =>
    simp
    unfold add_if_nullable
    split
    · simp
      constructor
      · apply rule_is_nullable_correct _ _ hd.2 ih
        rename_i h
        exact h
      · exact ih
    · exact ih

lemma add_nullables_iter_nullable (nullable : Finset g.NT) (p : nullable ⊆ g.generators)
  (hin : ∀ v ∈ nullable, NullableNonTerminal v) :
  ∀ v ∈ (add_nullables_iter nullable p), NullableNonTerminal v:= by
  unfold add_nullables_iter
  intro v
  simp
  split
  · tauto
  · have ih := add_nullables_iter_nullable (add_nullables nullable) (add_nullables_subset_generators nullable p)
    apply ih
    exact add_nullables_nullable nullable hin
  termination_by ((g.generators).card - nullable.card)
  decreasing_by
    rename_i h
    exact generators_limits_nullable nullable p h

lemma compute_nullables_iff (v : g.NT) :
  v ∈ compute_nullables ↔ NullableNonTerminal v := by
  constructor
  · intro h
    apply add_nullables_iter_nullable Finset.empty
    tauto
    exact h
  · sorry

def nonterminalProp (s : Symbol T g.NT) (P : g.NT → Prop) :=
  match s with
  | Symbol.terminal _ => False
  | Symbol.nonterminal n => P n

def remove_nullable (nullable : Finset g.NT) (s: (Symbol T g.NT)) (acc : List (List (Symbol T g.NT))) :=
  match s with
  | Symbol.nonterminal n => (if n ∈ nullable then acc else []) ++ acc.map (fun x => s :: x)
  | Symbol.terminal _ => acc.map (fun x => s :: x)

def remove_nullable_rule (nullable : Finset g.NT) (r: ContextFreeRule T g.NT) : (List (ContextFreeRule T g.NT)) :=
  let fltrmap : List (Symbol T g.NT) → Option (ContextFreeRule T g.NT)
    | [] => Option.none
    | h :: t => ContextFreeRule.mk r.input (h :: t)
  (r.output.foldr (remove_nullable nullable) [[]]).filterMap fltrmap

def remove_nullables (nullable : Finset g.NT) : List (ContextFreeRule T g.NT) :=
  (g.rules.map (remove_nullable_rule nullable)).join

def eliminate_empty : ContextFreeGrammar T :=
  ContextFreeGrammar.mk g.NT g.initial (remove_nullables compute_nullables)

theorem eliminate_empty_correct :
  g.language = (@eliminate_empty T g).language \ {[]} := by sorry

end ContextFreeGrammar

-- I definitely need to restrict the type of variables with Fintype
theorem pumping_lemma {L : Language T} (hL : L.IsContextFree) :
  ∃ p : ℕ, ∀ w ∈ L, w.length ≥ p → ∃ u v x y z : List T,
    w = u ++ v ++ x ++ y ++ z ∧
    (v ++ y).length > 0       ∧
    (v ++ x ++ y).length ≤ p  ∧
    ∀ i : ℕ, u ++ (v ^^ i) ++ x ++ y ^^ i ++ z ∈ L :=
  sorry
