import P23.Semigroup.OneTieNormalization

noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin

example (e : ThreePoly ℚ ≃ₐ[ℚ] ThreePoly ℚ) (I : Ideal (ThreePoly ℚ))
    (n : ℕ) (h : HasMinimalGeneratorCard I n) :
    HasMinimalGeneratorCard (I.map e.toRingHom) n := minimalGeneratorCard_map_algEquiv e I n h

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (p : TailPoly ℚ) (C : OneTieCoordinates D i p) :
    HasMinimalGeneratorCard (renamedChosenBaseIdeal C) D.semigroupRho :=
  renamedChosenBaseIdeal_minimalGeneratorCard C

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (p : TailPoly ℚ) (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ)) :
    Ideal.span (↑(normalizedLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) =
      Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) :=
  normalizedLiftGeneratorFinset_span_eq C E

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (p : TailPoly ℚ) (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ))
    (hspan : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) =
      renamedChosenBaseIdeal C) (hcard : E.card = D.semigroupRho - 1)
    (hpos : 0 < D.semigroupRho) :
    (normalizedLiftGeneratorFinset C E).card = D.semigroupRho ∧
      (normalizedMonomialGeneratorFinset C E).card = D.semigroupRho - 1 :=
  normalizedGeneratorFinsets_card C E hspan hcard hpos
