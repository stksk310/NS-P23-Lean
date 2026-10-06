import P23.Semigroup.ChosenBaseMinimality
namespace P23.Semigroup
noncomputable section
open P23.Presentation
variable {k : Type*} [Field k] (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
example (G : Finset (TailPoly k))
    (hG : Ideal.span (↑G : Set (TailPoly k)) = chosenBaseDefiningIdeal D i) :
    D.semigroupRho ≤ G.card := chosenBaseDefiningIdeal_generator_card_lower_bound D i G hG
example : idealGeneratorMu (chosenBaseDefiningIdeal (k := k) D i) = D.semigroupRho :=
  chosenBaseDefiningIdeal_mu_eq_rho D i
example : HasMinimalGeneratorCard (chosenBaseDefiningIdeal (k := k) D i) D.semigroupRho :=
  chosenBaseDefiningIdeal_minimalGeneratorCard D i
example (hB : D.fourBaseBudget i = 0) : MinimalMonomialChosenBasePresentation (k := k) D i :=
  chosenBase_minimalMonomialPresentation_of_budget_zero D i hB
example (hB : D.fourBaseBudget i = 1) : MinimalOneLiveBinomialChosenBasePresentation (k := k) D i :=
  chosenBase_minimal_one_live_binomial_of_budget_one D i hB
example : ChosenBaseMinimalityBridge (k := k) D i := chosenBaseMinimalityBridge D i
end
end P23.Semigroup
