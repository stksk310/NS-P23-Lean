import P23.Semigroup.RepeatedCentre
import P23.Semigroup.HighRhoAllBaseDominance

namespace P23.Semigroup
open FourGeneratedNumericalSemigroup

theorem highRho_implies_almostSymmetric (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupType+4≤D.semigroupRho) :
    D.IsAlmostSymmetric :=
  four_dominant_bases_imply_almostSymmetric ht (highRho_allBaseDominance D ht hn hr).allDominant

theorem notAlmostSymmetric_rho_le_type_plus_three (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (ha : ¬D.IsAlmostSymmetric) :
    D.semigroupRho≤D.semigroupType+3 := by
  by_contra h
  exact ha (highRho_implies_almostSymmetric D ht hn (by omega))

theorem type_two_notAS_rho_le_five (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2) (hn : SemigroupNearlyGorenstein D) (ha : ¬D.IsAlmostSymmetric) :
    D.semigroupRho≤5 := by
  have h := notAlmostSymmetric_rho_le_type_plus_three D (Or.inl ht) hn ha
  omega

theorem type_three_notAS_rho_le_six (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) (ha : ¬D.IsAlmostSymmetric) :
    D.semigroupRho≤6 := by
  have h := notAlmostSymmetric_rho_le_type_plus_three D (Or.inr ht) hn ha
  omega

structure GlobalASForcing (D : FourGeneratedNumericalSemigroup) : Prop where
  highRhoAS : (D.semigroupType=2 ∨ D.semigroupType=3) →
    SemigroupNearlyGorenstein D → D.semigroupType+4≤D.semigroupRho → D.IsAlmostSymmetric
  notASBound : (D.semigroupType=2 ∨ D.semigroupType=3) →
    SemigroupNearlyGorenstein D → ¬D.IsAlmostSymmetric → D.semigroupRho≤D.semigroupType+3

theorem globalASForcing (D : FourGeneratedNumericalSemigroup) : GlobalASForcing D :=
  ⟨highRho_implies_almostSymmetric D,notAlmostSymmetric_rho_le_type_plus_three D⟩

end P23.Semigroup
