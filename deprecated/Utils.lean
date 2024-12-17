import Mathlib.Computability.ContextFreeGrammar

def nTimes {α : Type _} (l : List α) (n : Nat) : List α :=
  (List.replicate n l).flatten

infixl:100 "^^" => nTimes

namespace ContextFreeGrammar

universe uN uT
variable {T : Type uT} {g : ContextFreeGrammar.{uN, uT} T}

theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
  {u : List (Symbol T g.NT)} (huv : g.Derives u v)
  (refl : P v (Derives.refl v))
  (head : ∀ {u w} (huw : g.Produces u w) (hwv : g.Derives w v), P w hwv → P u (hwv.head huw)) :
  P u huv :=
  Relation.ReflTransGen.head_induction_on huv refl head

end ContextFreeGrammar

namespace ContextFreeRule

universe uN uT
variable {T : Type uT} {N : Type uN}

-- later put `deriving DecidableEq` on `ContextFreeRule` instead
instance [eqt : DecidableEq T] [eqnt : DecidableEq N] : DecidableEq (ContextFreeRule T N) := by
  intro x y
  cases x
  cases y
  simp
  exact instDecidableAnd

end ContextFreeRule
