import P23.Monomial.PlainTypeTwoBound
open P23.Monomial

example (R : Finset PlainExp) (ha : PlainRootAntichain R)
    (h2 : R.card=2) (hv : PlainVariablesSurvive R) :
    (plainBorderFinset R).card ≤ 5 := by
  exact plain_type_two_border_card_le_five R ha h2 hv
