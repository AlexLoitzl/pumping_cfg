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
