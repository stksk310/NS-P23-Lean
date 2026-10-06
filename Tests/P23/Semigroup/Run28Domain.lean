import P23.Semigroup.ChosenBaseCanonicalQuotient
noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4} {p : TailPoly ℚ}
variable (C : OneTieCoordinates D i p)

example (hc : 0 < C.c) : 2 ≤ C.a ∧ 1 ≤ C.b ∧ 1 ≤ C.c := by
  obtain ⟨ha,hm | hp⟩ := C.liveDomain
  · exact ⟨ha,hm⟩
  · omega

example (hc : C.c = 0) : 2 ≤ C.a ∧ 2 ≤ C.b := by
  obtain ⟨ha,hm | hp⟩ := C.liveDomain
  · omega
  · exact ⟨ha,hp.1⟩

example (B : BudgetOneNormalizedPresentation D i) :
    B.generators = borderFinset B.roots := B.generators_exact_border

example (B : BudgetOneNormalizedPresentation D i) :
    renamedChosenBaseIdeal B.coordinates = finitePresentationIdeal (k := ℚ) B.roots :=
  B.canonical_ideal

example (B : BudgetOneNormalizedPresentation D i) :
    IsLiveTie B.roots ∧ IsRootAntichain B.roots ∧ B.roots.Nonempty :=
  ⟨B.roots_live,B.roots_antichain,B.roots_nonempty⟩

example (B : BudgetOneNormalizedPresentation D i) :
    ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] FinitePolynomialQuotient ℚ B.roots :=
  B.chosenBaseEquivCanonicalOneTie
