import P23.Semigroup.NormalizedMonomialIdeal
noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
variable (B : BudgetOneNormalizedPresentation D i)
example : (rawLiftGeneratorFinset B.coordinates B.rawExponents).card = D.semigroupRho := B.raw_family_card
example (d : Fin 3 →₀ ℕ) : tiePolynomial (k := ℚ) B.coordinates.a B.coordinates.b B.coordinates.c ≠
    MvPolynomial.monomial d 1 := B.tie_ne_raw_monomial d
example : Set.InjOn (normalizeExponent B.coordinates.a B.coordinates.b B.coordinates.c) B.rawExponents :=
  B.normalization_injective
example (q : Normal B.coordinates.a B.coordinates.b B.coordinates.c) : polynomialLift (k := ℚ) q ≠ 0 :=
  B.normalized_lift_ne_zero q
