/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import PumpingCfg.ChomskyNormalForm
import PumpingCfg.ChomskyNormalFormTranslation

universe uN uT

variable {T : Type uT}

namespace ChomskyNormalFormGrammar

variable {g : ChomskyNormalFormGrammar.{uN,uT} T}

-------------------------------------------
------------------ STUFF ------------------
-------------------------------------------

lemma Derives.append_left_trans {u v w x: List (Symbol T g.NT)} (huv : g.Derives u v)
    (hwx : g.Derives w x) :
    g.Derives (w ++ u) (x ++ v) :=
  (huv.append_left _).trans (hwx.append_right _)

inductive ParseTree : g.NT → Type _ where
  | tree_leaf {n : g.NT} (t : T)
      (h : (ChomskyNormalFormRule.leaf n t) ∈ g.rules) : ParseTree n
  | tree_node {n c₁ c₂ : g.NT} (t₁ : ParseTree c₁) (t₂ : ParseTree c₂)
      (h : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules) : ParseTree n

namespace ParseTree

def yield {n : g.NT} (p : ParseTree n) : List T :=
  match p with
  | tree_leaf t _ => [t]
  | tree_node t1 t2 _ => yield t1 ++ yield t2

variable {n : g.NT} {p : ParseTree n}

lemma yield_derives {u : List T} (h : p.yield = u) :
    g.Derives [Symbol.nonterminal n] (List.map Symbol.terminal u) := by
  induction p generalizing u with
  | tree_leaf t hg =>
    simp only [yield] at h
    rw [← h]
    exact Produces.single ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
  | tree_node l r hg ihl ihr =>
    simp only [yield] at h
    rw [← h]
    apply Produces.trans_derives
    exact ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
    rw [ChomskyNormalFormRule.output, List.map_append, ←List.singleton_append]
    exact ((ihr rfl).append_left _).trans ((ihl rfl).append_right _)

end ParseTree

lemma Produces.rule {n : g.NT} {u : List (Symbol T g.NT)}
    (hnu : g.Produces [Symbol.nonterminal n] u) :
    ∃ r ∈ g.rules, r.input = n ∧ r.output = u := by
  obtain ⟨r, hrg, hnu⟩ := hnu
  cases hnu
  · sorry
  · sorry
  · sorry

private lemma Derives.yield_rec {n : g.NT} {u : List T} {v : List (Symbol T g.NT)}
    (hvn : v = [Symbol.nonterminal n]) (h : g.Derives v (List.map Symbol.terminal u)) :
    ∃ p : ParseTree n, p.yield = u := by
  induction h using Derives.head_induction_on generalizing n with
  | refl =>
    cases u <;> simp only [List.map_nil, List.ne_cons_self, List.map_cons, List.cons.injEq,
      reduceCtorEq, List.map_eq_nil_iff, false_and] at hvn
  | @head v w hvw hwu ih =>
    rw [hvn] at hvw
    obtain ⟨r, hrg, hr₁, hr₂⟩ := hvw.rule
    cases r with
    | leaf n t =>
      cases hwu.eq_or_head with
      | inl hw =>
        simp at hr₁ hr₂
        rw [hr₁] at hrg
        use (ParseTree.tree_leaf t hrg)
        simp [ParseTree.yield]
        rw [hw] at hr₂
        cases u; contradiction
        simp at hr₂ ⊢
        exact hr₂
      | inr => sorry
    | node => sorry

lemma Derives.yield {n : g.NT} {u : List T}
    (h : g.Derives [Symbol.nonterminal n] (List.map Symbol.terminal u)) :
    ∃ p : ParseTree n, p.yield = u := Derives.yield_rec rfl h

end ChomskyNormalFormGrammar
