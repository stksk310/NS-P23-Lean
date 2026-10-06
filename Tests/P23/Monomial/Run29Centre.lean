import P23.Monomial.PlainTraceToCentre
namespace P23.Monomial
variable {k : Type*} [Field k] (R : Finset PlainExp)
example (hR : R.Nonempty) (hcard : 2 ≤ R.card) (ha : PlainRootAntichain R)
    (hv : PlainVariablesSurvive R) (ht : PlainVariablesInTrace k R hv) :
    HasPlainDirectionalCentres R := plain_hasDirectionalCentres_of_variablesInTrace R hR hcard ha hv ht
end P23.Monomial
