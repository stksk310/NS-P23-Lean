import P23.Semigroup.RhoBaseline
import P23.Semigroup.RhoFourExclusion
import P23.Semigroup.RhoFiveExclusion

/-! Exact type-three lower bound, with frozen project PF-NG scope. -/
namespace P23.Semigroup

theorem type_three_ng_semigroupRho_ge_six (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 3) (hn : SemigroupNearlyGorenstein D) :
    6 ≤ D.semigroupRho := by
  have h4 := type_three_semigroupRho_ge_four D ht
  have hn4 := type_three_ng_semigroupRho_ne_four D ht hn
  have hn5 := type_three_ng_semigroupRho_ne_five D ht hn
  omega

structure TypeThreeLowerBound (D : FourGeneratedNumericalSemigroup) : Prop where
  baseline : SmallPresentationBaseline D
  typeThreeNgRhoNotFour : D.semigroupType = 3 → SemigroupNearlyGorenstein D → D.semigroupRho ≠ 4
  typeThreeNgRhoNotFive : D.semigroupType = 3 → SemigroupNearlyGorenstein D → D.semigroupRho ≠ 5
  typeThreeNgRhoSix : D.semigroupType = 3 → SemigroupNearlyGorenstein D → 6 ≤ D.semigroupRho

theorem typeThreeLowerBound (D : FourGeneratedNumericalSemigroup) : TypeThreeLowerBound D where
  baseline := smallPresentationBaseline D
  typeThreeNgRhoNotFour := type_three_ng_semigroupRho_ne_four D
  typeThreeNgRhoNotFive := type_three_ng_semigroupRho_ne_five D
  typeThreeNgRhoSix := type_three_ng_semigroupRho_ge_six D

end P23.Semigroup
