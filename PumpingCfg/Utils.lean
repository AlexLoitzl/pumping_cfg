import Mathlib.Data.List.Basic

def nTimes {α : Type _} (l : List α) (n : Nat) : List α :=
  (List.replicate n l).flatten

infixl:100 "^+^" => nTimes

variable {α : Type _}

theorem nTimes_succ_l {l : List α} {n : Nat}: l^+^n.succ = l ++ l^+^n := by
  simp [nTimes, List.replicate]

theorem nTimes_succ_r {l : List α} {n : Nat}: l^+^n.succ = l^+^n ++ l := by
  simp only [nTimes]
  rw [List.replicate_succ']
  simp
