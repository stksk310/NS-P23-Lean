import P23.Semigroup.NormalizedMonomialIdeal

noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (p : TailPoly ℚ)
variable (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ))
variable (hspan : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) =
  renamedChosenBaseIdeal C)

example : (renamedChosenBaseIdeal C).map
    (polyToNormalAlg (k := ℚ) (a := C.a) (b := C.b) (c := C.c)).toRingHom =
      normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) :=
  normalizedMonomialIdeal_map C E hspan

example : ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ]
    (NormalMonoidAlgebra ℚ C.a C.b C.c ⧸ normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E)) :=
  chosenBaseQuotientEquivNormalGenerators C E hspan

example : Module.Finite ℚ
    (NormalMonoidAlgebra ℚ C.a C.b C.c ⧸ normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E)) :=
  chosenBase_normal_survivorQuotient_finite C E hspan
