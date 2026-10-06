import P23.Semigroup.OneTieNormalization

noncomputable section
open P23.Semigroup P23.Presentation

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 1) :
    ∃ (p : TailPoly ℚ) (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ)),
      Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C ∧
      E.card = D.semigroupRho - 1 ∧ 0 < D.semigroupRho :=
  budgetOne_raw_normalization_data D i hB
