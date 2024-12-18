import Mathlib.Data.List.Basic

variable {α : Type _}

def nTimes (l : List α) (n : ℕ) : List α :=
  (List.replicate n l).flatten

infixl:69 " ^+^ " => nTimes

lemma nTimes_succ_l {l : List α} {n : ℕ} : l^+^n.succ = l ++ l^+^n := by
  simp [nTimes, List.replicate_succ]

lemma nTimes_succ_r {l : List α} {n : ℕ} : l^+^n.succ = l^+^n ++ l := by
  simp [nTimes, List.replicate_succ']

lemma nTimes_map {β : Type _} {l : List α} {f : α → β} {n : ℕ} : (l.map f)^+^n = (l^+^n).map f := by
  simp [nTimes]

lemma nTimes_add {l : List α} {m n : ℕ} : l ^+^ (m + n) = l ^+^ m ++ l ^+^ n := by
  induction n with
  | zero => exact (l ^+^ m).append_nil.symm
  | succ k ih => rw [Nat.add_succ, nTimes_succ_r, nTimes_succ_r, ih, List.append_assoc]

lemma nTimes_mul {l : List α} {m n : ℕ} : l ^+^ m * n = l ^+^ m ^+^ n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, nTimes_add, ih, nTimes_succ_r]
