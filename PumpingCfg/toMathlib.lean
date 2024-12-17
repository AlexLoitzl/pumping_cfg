import Mathlib.Computability.ChomskyNormalForm.Basic

universe uT uN
variable {T : Type uT}

namespace ChomskyNormalFormRule

lemma Rewrites.word {T N : Type*} {r : ChomskyNormalFormRule T N} {u : List T} {v : List (Symbol T N)}
    (hruv : r.Rewrites (u.map Symbol.terminal) v) :
    False := by
  induction u generalizing v with
  | nil => cases hruv
  | cons u₁ u ih =>
    cases hruv with
    | cons _ _ hru => exact ih hru

end ChomskyNormalFormRule

namespace ChomskyNormalFormGrammar

variable {g : ChomskyNormalFormGrammar.{uN} T}

lemma Produces.input_output {r : ChomskyNormalFormRule T g.NT} (hrg : r ∈ g.rules) :
    g.Produces [.nonterminal r.input] r.output :=
  ⟨r, hrg, ChomskyNormalFormRule.Rewrites.input_output⟩

end ChomskyNormalFormGrammar
