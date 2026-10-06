import P23.Semigroup.HighRhoAllBaseDominance
open P23.Semigroup
example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) (i : Fin 4) : 0<D.fourBaseBudget i :=
  highRho_budget_positive D ht hn hr i
example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) (i : Fin 4) (hb : 2≤D.fourBaseBudget i) : False :=
  highRho_budget_at_least_two_impossible D ht hn hr i hb
