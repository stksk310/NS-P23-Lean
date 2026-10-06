import P23.Semigroup.ChosenBaseCanonicalQuotient
noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 1) (ht : D.semigroupType = 3)
    (hng : SemigroupNearlyGorenstein D) :
    Nonempty (ChosenBaseCanonicalOneTieBridge D i) :=
  chosenBaseCanonicalOneTieBridge D i hB ht hng
