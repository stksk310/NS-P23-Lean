import P23.Monomial.PlainTypeThreeFrontier

open P23.Monomial

example (R : Finset PlainExp) (ha : PlainRootAntichain R)
    (h3 : R.card = 3) (hv : PlainVariablesSurvive R)
    (hc : HasPlainDirectionalCentres R) :
    (plainBorderFinset R).card = 4 ∨ (plainBorderFinset R).card = 6 ∨
      (plainBorderFinset R).card = 7 := by
  exact plain_type_three_ng_border_frontier R ha h3 hv hc

example (R : Finset PlainExp) (ha : PlainRootAntichain R)
    (h3 : R.card = 3) (hv : PlainVariablesSurvive R)
    (hc : HasPlainDirectionalCentres R) (h7 : (plainBorderFinset R).card = 7) :
    ∃ s, PlainIsDominantRoot R s := by
  exact plain_type_three_border_seven_has_dominant_root R ha h3 hv hc h7
