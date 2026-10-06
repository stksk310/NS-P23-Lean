import P23.Monomial.PlainNoFive
namespace P23.Monomial
example (R : Finset PlainExp) (ha : PlainRootAntichain R)
    (h3 : R.card = 3) (hv : PlainVariablesSurvive R)
    (hc : HasPlainDirectionalCentres R) :
    (plainBorderFinset R).card ≠ 5 := plain_three_root_no_five R ha h3 hv hc
end P23.Monomial
