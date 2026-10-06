import P23.Semigroup.RhoFourExclusion
open P23.Semigroup FourGeneratedNumericalSemigroup
example (D : FourGeneratedNumericalSemigroup) (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) : D.semigroupRho ≠ 4 :=
  type_three_ng_semigroupRho_ne_four D ht hn
