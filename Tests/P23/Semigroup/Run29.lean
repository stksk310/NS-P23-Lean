import P23.Semigroup.RhoFiveMonomialAlternative
namespace P23.Semigroup
variable (D : FourGeneratedNumericalSemigroup)
variable (ht : D.semigroupType = 3) (hn : SemigroupNearlyGorenstein D)
example : MonomialFiveGeneratorObstruction D := monomialFiveGeneratorObstruction D ht hn
example (hr : D.semigroupRho = 5) : ∀ i, D.fourBaseBudget i = 1 :=
  (monomialFiveGeneratorObstruction D ht hn).rhoFiveAllOne hr
end P23.Semigroup
