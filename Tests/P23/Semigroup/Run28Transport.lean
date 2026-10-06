import P23.Semigroup.ChosenBaseCanonicalQuotient
noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
variable (B : BudgetOneNormalizedPresentation D i)
example : quotientType ℚ B.roots B.roots_nonempty B.coordinates.liveDomain B.roots_live =
    chosenBaseType (k := ℚ) D i := B.canonicalOneTieType_eq_chosenBaseType
example : ChosenBaseNearlyGorenstein (k := ℚ) D i ↔
    QuotientNearlyGorenstein ℚ B.roots B.roots_nonempty B.coordinates.liveDomain B.roots_live :=
  B.canonicalOneTie_ng_iff
example : idealGeneratorMu (finitePresentationIdeal (k := ℚ) B.roots) = D.semigroupRho :=
  B.canonicalKernelMu_eq_rho
