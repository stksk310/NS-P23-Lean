import P23.Semigroup.ChosenBasePlainPresentation
namespace P23.Semigroup
open P23.Monomial P23.Presentation
example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 0) :
    ∃ G : Finset PlainExp, plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal D i ∧
      G.card = D.semigroupRho ∧ HasMinimalGeneratorCard (plainMonomialIdeal ℚ G) G.card :=
  chosenBase_plain_exponentPresentation_of_budget_zero D i hB
end P23.Semigroup
