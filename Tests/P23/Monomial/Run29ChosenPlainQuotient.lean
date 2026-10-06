import P23.Semigroup.ChosenBasePlainQuotient
namespace P23.Semigroup
noncomputable section
open P23.Monomial
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
variable (G : Finset PlainExp) (hI : plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal D i)
example : (plainSurvivors ℚ G).Finite := chosenBase_plainSurvivors_finite D i G hI
example : (0 : PlainExp) ∈ plainSurvivors ℚ G := chosenBase_plain_unit_survives D i G hI
example (hf : (plainSurvivors ℚ G).Finite) :
    PlainVariablesSurvive (plainSurvivorRoots ℚ G hf) :=
  chosenBase_plain_variables_survive D i G hI hf
example (hf : (plainSurvivors ℚ G).Finite)
    (hG : G = plainBorderFinset (plainSurvivorRoots ℚ G hf)) :
    ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] PlainMonomialArtin ℚ (plainSurvivorRoots ℚ G hf) :=
  chosenBasePlainQuotientEquiv D i G hI hf hG
end
end P23.Semigroup
