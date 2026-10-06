import P23.Monomial.PlainSmallPresentation

open P23.Monomial
noncomputable section
variable (k : Type*) [Field k] (G : Finset PlainExp)
    (hf : (plainSurvivors k G).Finite)
    (hv : PlainVariablesSurvive (plainSurvivorRoots k G hf))

-- Break caught: omitting an axis, accepting exponent one, or ignoring minimality.
example (j : Fin 3) : ∃ A : ℕ, 2 ≤ A ∧
    Finsupp.single j A ∈ plainBorderFinset (plainSurvivorRoots k G hf) :=
  exists_plain_pure_axis_border k G hf hv j

example : 3 ≤ (plainBorderFinset (plainSurvivorRoots k G hf)).card :=
  plain_border_card_ge_three_of_variables_survive _ hv

example (he : G = plainBorderFinset (plainSurvivorRoots k G hf)) (hc : G.card ≤ 3) :
    (plainSurvivorRoots k G hf).card = 1 :=
  plain_small_minimal_presentation_root_card_one k G hf hv he hc

example (R : Finset PlainExp) (hv : PlainVariablesSurvive R)
    (hc : (plainBorderFinset R).card ≤ 3) : plainBorderFinset R =
    Finset.univ.image (fun j : Fin 3 => Finsupp.single j (plainAxisBound R j)) :=
  plain_small_border_eq_axis_triple R hv hc
