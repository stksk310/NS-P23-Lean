import P23.Semigroup.RhoBaseline
open P23.Semigroup

-- Break caught: a baseline accidentally depending on NG or on rho=4.
example (D : FourGeneratedNumericalSemigroup) : ∃ i : Fin 4, D.fourBaseBudget i ≤ 1 :=
  exists_base_budget_le_one D

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hb : D.fourBaseBudget i = 0) (hr : D.semigroupRho ≤ 3) : D.semigroupType = 1 :=
  budget_zero_rho_le_three_semigroupType_eq_one D i hb hr

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hb : D.fourBaseBudget i = 1) (hr : D.semigroupRho ≤ 3) : D.semigroupType = 1 :=
  budget_one_rho_le_three_semigroupType_eq_one D i hb hr

example (D : FourGeneratedNumericalSemigroup) (hr : D.semigroupRho ≤ 3) :
    D.semigroupType = 1 := semigroupRho_le_three_imp_type_one D hr

example (D : FourGeneratedNumericalSemigroup) (ht : D.semigroupType = 2) :
    4 ≤ D.semigroupRho := type_two_semigroupRho_ge_four D ht

example (D : FourGeneratedNumericalSemigroup) (ht : D.semigroupType = 3) :
    4 ≤ D.semigroupRho := type_three_semigroupRho_ge_four D ht
