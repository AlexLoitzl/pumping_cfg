
def nTimes (l : List α) (n : Nat) : List α :=
  (List.replicate n l).join

infixl:100 " ^^ " => nTimes
