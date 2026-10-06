import P23.Semigroup.NormalizedMonomialIdeal
noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4} {p : TailPoly ℚ}
variable (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ))
variable (hs : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C)
example : monomial (k := ℚ) (1 : Normal C.a C.b C.c) ∉
    normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) :=
  chosenBase_normal_unit_survives C E hs
example : monomial (k := ℚ) (liveTiePoint : Normal C.a C.b C.c) ∉
    normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) :=
  chosenBase_normal_tie_survives C E hs
