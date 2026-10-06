import P23.Semigroup.RhoFiveMonomialAlternative
namespace P23.Semigroup
variable (D : FourGeneratedNumericalSemigroup)
variable (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
example (i : Fin 4) (hz : D.fourBaseBudget i=0)
    (htq : chosenBaseType (k := ℚ) D i=3)
    (hnq : ChosenBaseNearlyGorenstein (k := ℚ) D i) :
    P23.Presentation.idealGeneratorMu (chosenBaseDefiningIdeal (k := ℚ) D i) ≠ 5 :=
  chosenBase_budget_zero_type_three_ng_mu_ne_five D i hz htq hnq
example (i : Fin 4) (hz : D.fourBaseBudget i=0) : D.semigroupRho ≠ 5 :=
  budget_zero_type_three_ng_rho_ne_five D i hz ht hn
example (hr : D.semigroupRho=5) (i : Fin 4) : 0<D.fourBaseBudget i :=
  rho_five_budget_positive D ht hn hr i
example (hr : D.semigroupRho=5) (i : Fin 4) : D.fourBaseBudget i=1 :=
  rho_five_all_budgets_eq_one D ht hn hr i
end P23.Semigroup
