import Mathlib.Data.List.Basic

variable {α : Type _}

def nTimes (l : List α) (n : ℕ) : List α :=
  (List.replicate n l).flatten

infixl:69 " ^+^ " => nTimes

variable {l : List α} {n : ℕ}

lemma nTimes_succ_l : l^+^n.succ = l ++ l^+^n := by
  simp [nTimes, List.replicate_succ]

lemma nTimes_succ_r : l^+^n.succ = l^+^n ++ l := by
  simp [nTimes, List.replicate_succ']

lemma nTimes_map {β : Type _} {f : α → β} : (l.map f)^+^n = (l^+^n).map f := by
  simp [nTimes]

lemma nTimes_add {m : ℕ} : l ^+^ (m + n) = l ^+^ m ++ l ^+^ n := by
  induction n with
  | zero => exact (l ^+^ m).append_nil.symm
  | succ _ ih => rw [Nat.add_succ, nTimes_succ_r, nTimes_succ_r, ih, List.append_assoc]

lemma nTimes_mul {m : ℕ} : l ^+^ m * n = l ^+^ m ^+^ n := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Nat.mul_succ, nTimes_add, ih, nTimes_succ_r]
