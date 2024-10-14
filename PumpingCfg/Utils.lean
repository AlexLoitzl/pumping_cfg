
def nTimes {α : Type _} (l : List α) (n : Nat) : List α :=
  (List.replicate n l).join

infixl:100 " ^^ " => nTimes
