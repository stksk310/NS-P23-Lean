import P23.Semigroup.NormalizedMonomialIdeal
noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (hB : D.fourBaseBudget i = 1) :
    Nonempty (BudgetOneNormalizedPresentation D i) := budgetOneNormalizedPresentation D i hB
