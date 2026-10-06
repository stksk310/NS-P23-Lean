import P23.Semigroup.OneTieNormalization

noncomputable section
open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup P23.Presentation
open P23.OneTie P23.Artin

variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

example (p : TailPoly ℚ) (hp : D.LiveTailBinomial i p) :
    Nonempty (LiveTailTieData D i p) := liveTailTieData_exists D i p hp

example (hB : D.fourBaseBudget i = 1) :
    ∃ p : TailPoly ℚ, p ∈ chosenBaseDefiningIdeal D i ∧
      Nonempty (OneTieCoordinates D i p) := oneTieCoordinates_of_budget_one D i hB

example (p : TailPoly ℚ) (C : OneTieCoordinates D i p) :
    IsLiveParameterDomain C.a C.b C.c := oneTieCoordinates_liveDomain C

example (p : TailPoly ℚ) (C : OneTieCoordinates D i p) :
    renameToOneTie C p = tiePolynomial C.a C.b C.c ∨
      renameToOneTie C p = -tiePolynomial C.a C.b C.c := renameToOneTie_live C

example (p : TailPoly ℚ) (C : OneTieCoordinates D i p)
    (hp : p ∈ chosenBaseDefiningIdeal D i) :
    tiePolynomial C.a C.b C.c ∈ renamedChosenBaseIdeal C :=
  tiePolynomial_mem_renamedChosenBaseIdeal C hp

example (p : TailPoly ℚ) (C : OneTieCoordinates D i p) :
    ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ]
      (ThreePoly ℚ ⧸ renamedChosenBaseIdeal C) := chosenBaseQuotientEquivRenamed C
