import P23.Monomial.PlainCentrePatterns
namespace P23.Monomial
example (p q r : PlainExp) (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc : HasPlainDirectionalCentres {p,q,r}) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r :=
  plain_three_root_coordinate_patterns p q r hpq hpr hqr ha hv hc
end P23.Monomial
