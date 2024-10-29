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

private lemma DerivesSteps.empty_of_append_right_aux {u v w : List (Symbol T g.NT)}
    (huv : g.DerivesSteps (u ++ v) w n) (hw : w = []) :
    ∃ m ≤ n, ∃ w', g.DerivesSteps u w' m ∧ w' = [] := by
  induction n generalizing u v with
  | zero =>
    use 0
    cases huv with
    | refl =>
      have hu : u = [] := by simp_all
      constructor
      · rfl
      use []
      constructor
      · rw [hu]
        left
      · rfl
  | succ k ih =>
    obtain ⟨x, ⟨r, rin, hr⟩, hxw⟩ := huv.head_of_succ
    rw [ContextFreeRule.rewrites_iff] at hr
    obtain ⟨p, q, huvpq, hxpq⟩ := hr
    rw [←List.append_cons, List.append_eq_append_iff] at huvpq
    cases huvpq with
    | inl ha' =>
      obtain ⟨a, hpa, hva⟩ := ha'
      rw [hpa] at hxpq
      simp only [List.append_assoc] at hxpq
      rw [hxpq] at hxw
      obtain ⟨m, hm, w', hguw', hw'⟩ := ih hxw
      use m
      constructor
      · exact Nat.le_add_right_of_le hm
      · use w'
    | inr hc' =>
      obtain ⟨c, huc, hvc⟩ := hc'
      rw [hxpq] at hxw
      cases c with
      | nil =>
        rw [List.nil_append] at hvc
        cases v with
        | nil =>
          exfalso
          simp at hvc
        | cons d' l' =>
          rw [List.cons.injEq] at hvc
          obtain ⟨hd', rfl⟩ := hvc
          rw [List.append_nil] at huc
          rw [←hd'] at *
          rw [huc] at *
          clear hd' huc hxpq u x
          rw [List.append_assoc] at hxw
          obtain ⟨m, hm, w', hguw', hw'⟩ := ih hxw
          use m
          constructor
          · exact Nat.le_add_right_of_le hm
          · use w'
      | cons d l =>
        rw [List.cons_append, List.cons.injEq] at hvc
        obtain ⟨hd', rfl⟩ := hvc
        rw [huc] at *
        rw [←hd'] at *
        clear huc hd' hxpq x d
        rw [←List.append_assoc] at hxw
        obtain ⟨m, hm, w', hguw', hw'⟩ := ih hxw
        use m.succ
        constructor
        · exact Nat.le_add_of_sub_le hm
        · use w'
          simp [hw']
          rw [hw'] at hguw'
          apply Produces.trans_derivesSteps
          swap; exact hguw'
          refine ⟨r, rin, ?_⟩
          rw [ContextFreeRule.rewrites_iff]
          exact ⟨p, l, List.append_cons .., rfl⟩

lemma DerivesSteps.empty_of_append_right {u v : List (Symbol T g.NT)} (huv : g.DerivesSteps (u ++ v) [] n) :
    ∃ m ≤ n, g.DerivesSteps u [] m := by
  obtain ⟨m, _, _, _, rfl⟩ := huv.empty_of_append_right_aux rfl
  use m

@[elab_as_elim] -- not tested, please check
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
