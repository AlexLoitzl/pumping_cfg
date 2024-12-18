import Mathlib.Data.List.Basic

def nTimes {α : Type _} (l : List α) (n : ℕ) : List α :=
  (List.replicate n l).flatten

infixl:100 "^+^" => nTimes

variable {α : Type _}

lemma nTimes_succ_l {l : List α} {n : ℕ} : l^+^n.succ = l ++ l^+^n := by
  simp [nTimes, List.replicate]

lemma nTimes_succ_r {l : List α} {n : ℕ} : l^+^n.succ = l^+^n ++ l := by
  simp only [nTimes]
  rw [List.replicate_succ']
  simp

lemma nTimes_map {β : Type _} {l : List α} {f : α → β} {n : ℕ} : (l.map f)^+^n = (l^+^n).map f := by
  simp [nTimes]
