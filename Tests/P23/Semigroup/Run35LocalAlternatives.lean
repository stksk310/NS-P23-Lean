import P23.Semigroup.HighRhoLocalAlternatives
namespace P23.Semigroup
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
example {k : Type*} [Field k] (h0 : D.fourBaseBudget i=0)
    (ht : chosenBaseType (k:=k) D i=2) :
    P23.Presentation.idealGeneratorMu (chosenBaseDefiningIdeal (k:=k) D i) ≤ 5 :=
  budget_zero_type_two_mu_le_five D i h0 ht
example (h1 : D.fourBaseBudget i=1) (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupType+4≤D.semigroupRho) :
    Nonempty (BudgetOneDominantCanonicalRoot D i) :=
  budgetOneDominantCanonicalRoot D i h1 ht hn hr
example (h0 : D.fourBaseBudget i=0) (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) : Nonempty (BudgetZeroTypeThreeFrontier D i) :=
  budgetZeroTypeThreeFrontier D i h0 ht hn
example (h0 : D.fourBaseBudget i=0) (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : 7≤D.semigroupRho) :
    Nonempty (BudgetZeroTypeThreeSevenDominant D i) :=
  budgetZeroTypeThreeSevenDominant D i h0 ht hn hr
example (h0 : D.fourBaseBudget i=0) (ht : D.semigroupType=2) : D.semigroupRho≤5 :=
  budget_zero_type_two_rho_le_five D i h0 ht
example (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupType+4≤D.semigroupRho) :
    HighRhoChosenBaseLocalAlternative D i :=
  highRhoChosenBaseLocalAlternative D i ht hn hr
example (h : 2≤D.fourBaseBudget i) : HighRhoChosenBaseLocalAlternative D i :=
  .budgetAtLeastTwo h
example : Run35LocalAsForcingSummary D := run35LocalAsForcingSummary D
end P23.Semigroup
