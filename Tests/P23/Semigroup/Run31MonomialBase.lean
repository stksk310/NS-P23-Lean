import P23.Semigroup.RhoFourMonomialBase

namespace P23.Semigroup
open P23.Monomial

example (R : Finset PlainExp) (ha : PlainRootAntichain R) (h3 : R.card=3)
    (hv : PlainVariablesSurvive R) (hc : HasPlainDirectionalCentres R)
    (h4 : (plainBorderFinset R).card=4) :
    ∃ r u v : ℕ, R=plainTriangleRoots r u v ∧
      plainBorderFinset R=plainTriangleBorder r u v :=
  plain_three_root_four_border_exact_triangle R ha h3 hv hc h4

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (G : Finset PlainExp)
    (r u v : ℕ)
    (hI : plainMonomialIdeal ℚ G=chosenBaseDefiningIdeal (k := ℚ) D i)
    (hG : G=plainTriangleBorder r u v)
    (ha : PlainRootAntichain (plainTriangleRoots r u v))
    (ht : D.semigroupType=3) :
    ∃ P : TailSocleTopPattern D i, P.top=tailDegree D i (plainExp (r+1) (u+1) (v+1)) :=
  triangle_topPattern_of_chosenBase_border D i G r u v hI hG ha ht

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (P : TailSocleTopPattern D i)
    (j : Fin 3) : P.top≠D.n i+D.tailGen i j := P.top_ne_base_add_tail j

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho=4) :
    D.fourBaseBudget i≠0 := rho_four_budget_zero_impossible D i ht hn hr

end P23.Semigroup
