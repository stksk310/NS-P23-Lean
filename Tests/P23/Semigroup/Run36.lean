import P23.Semigroup.HighRhoAllBaseDominance
open P23.Semigroup
example (D : FourGeneratedNumericalSemigroup) : Run36Summary D := run36Summary D
example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) : HighRhoAllBaseDominance D :=
  highRho_allBaseDominance D ht hn hr
