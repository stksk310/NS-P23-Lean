import P23.Semigroup.TypeThreeLowerBound
open P23.Semigroup

example (D : FourGeneratedNumericalSemigroup) (ht : D.semigroupType = 3)
    (hn : SemigroupNearlyGorenstein D) : 6 ≤ D.semigroupRho :=
  type_three_ng_semigroupRho_ge_six D ht hn
