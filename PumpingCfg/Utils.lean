import Mathlib.Computability.ContextFreeGrammar

def nTimes {α : Type _} (l : List α) (n : Nat) : List α :=
  (List.replicate n l).flatten

infixl:100 " ^^ " => nTimes

namespace ContextFreeGrammar

universe uN uT
variable {T : Type uT} {g : ContextFreeGrammar.{uN, uT} T}

theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
  {u : List (Symbol T g.NT)} (h : g.Derives u v)
  (refl : P v (Derives.refl v))
  (head : ∀ {u w} (h' : g.Produces u w) (h : g.Derives w v), P w h → P u (h.head h')) : P u h :=
  Relation.ReflTransGen.head_induction_on h refl head

end ContextFreeGrammar

namespace ContextFreeRule

universe uN uT
variable {T : Type uT} {N : Type uN}

instance [eqt : DecidableEq T] [eqnt : DecidableEq N] : DecidableEq (ContextFreeRule T N) := by
  intro x y
  cases x
  cases y
  simp
  exact instDecidableAnd

end ContextFreeRule
