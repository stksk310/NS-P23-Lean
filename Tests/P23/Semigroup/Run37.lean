import P23.Semigroup.OriginalBranches
open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup
#check highRho_implies_almostSymmetric
#check notAlmostSymmetric_rho_le_type_plus_three
#check type_two_notAS_rho_le_five
#check type_three_notAS_rho_le_six
#check type_two_ng_notAS_rho_eq_four_or_five
#check type_three_ng_notAS_rho_eq_six
#check run37Summary

variable (D : FourGeneratedNumericalSemigroup)
example (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupType+4≤D.semigroupRho) :
    D.IsAlmostSymmetric := highRho_implies_almostSymmetric D ht hn hr
example (ht : D.semigroupType=2) (hn : SemigroupNearlyGorenstein D)
    (ha : ¬D.IsAlmostSymmetric) : D.semigroupRho=4 ∨ D.semigroupRho=5 :=
  type_two_ng_notAS_rho_eq_four_or_five D ht hn ha
example (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (ha : ¬D.IsAlmostSymmetric) : D.semigroupRho=6 :=
  type_three_ng_notAS_rho_eq_six D ht hn ha
example : Run37Summary D := run37Summary D
