import P23.Semigroup.ASForcing
import P23.Semigroup.TypeThreeLowerBound

namespace P23.Semigroup
open FourGeneratedNumericalSemigroup

theorem type_two_ng_notAS_rho_eq_four_or_five (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2) (hn : SemigroupNearlyGorenstein D) (ha : ¬D.IsAlmostSymmetric) :
    D.semigroupRho=4 ∨ D.semigroupRho=5 := by
  have hl := type_two_semigroupRho_ge_four D ht
  have hu := type_two_notAS_rho_le_five D ht hn ha
  omega

theorem type_three_ng_notAS_rho_eq_six (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) (ha : ¬D.IsAlmostSymmetric) :
    D.semigroupRho=6 := by
  have hl := type_three_ng_semigroupRho_ge_six D ht hn
  have hu := type_three_notAS_rho_le_six D ht hn ha
  omega

/-- The two original branches, with the project PF-NG criterion explicit. -/
structure OriginalP23Branches (D : FourGeneratedNumericalSemigroup) : Prop where
  typeTwo : D.semigroupType=2 → SemigroupNearlyGorenstein D → ¬D.IsAlmostSymmetric →
    D.semigroupRho=4 ∨ D.semigroupRho=5
  typeThree : D.semigroupType=3 → SemigroupNearlyGorenstein D → ¬D.IsAlmostSymmetric →
    D.semigroupRho=6

theorem originalP23Branches (D : FourGeneratedNumericalSemigroup) : OriginalP23Branches D :=
  ⟨type_two_ng_notAS_rho_eq_four_or_five D,type_three_ng_notAS_rho_eq_six D⟩

/-- Run37 only: no Main packaging, global rho-seven bound, or external ring-NG equivalence. -/
structure Run37Summary (D : FourGeneratedNumericalSemigroup) : Prop where
  asForcing : GlobalASForcing D
  originalBranches : OriginalP23Branches D
  asGapCriterion : D.IsAlmostSymmetric ↔ 2*D.genus=D.frobenius+D.semigroupType
  genusLowerBound : D.frobenius+D.semigroupType≤2*D.genus

theorem run37Summary (D : FourGeneratedNumericalSemigroup) : Run37Summary D :=
  ⟨globalASForcing D,originalP23Branches D,D.almostSymmetric_iff_two_genus_eq,
    D.frobenius_type_le_two_genus⟩

end P23.Semigroup
