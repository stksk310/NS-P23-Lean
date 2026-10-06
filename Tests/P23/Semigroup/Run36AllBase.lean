import P23.Semigroup.HighRhoAllBaseDominance
#check P23.Semigroup.highRho_all_budgets_eq_one
#check P23.Semigroup.highRho_dominantAperyBase

open P23.Semigroup
example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) (i : Fin 4) : D.fourBaseBudget i=1 :=
  highRho_all_budgets_eq_one D ht hn hr i

example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) (i : Fin 4) : Nonempty (DominantAperyBase D i) :=
  highRho_dominantAperyBase D ht hn hr i
