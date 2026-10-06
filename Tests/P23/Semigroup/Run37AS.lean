import P23.Semigroup.AlmostSymmetric
open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup
#check doubleGap_reflection
#check two_genus_eq_frobenius_one_add_doubleGapCard
#check nonFrobeniusPF_subset_doubleGap
#check frobenius_type_le_two_genus
#check almostSymmetric_iff_doubleGap_card
#check almostSymmetric_iff_two_genus_eq

variable (D : FourGeneratedNumericalSemigroup)
example : 2*D.genus=D.frobenius+1+D.doubleGapFinset.card :=
  D.two_genus_eq_frobenius_one_add_doubleGapCard
example : D.frobenius+D.semigroupType≤2*D.genus := D.frobenius_type_le_two_genus
example : D.IsAlmostSymmetric ↔ 2*D.genus=D.frobenius+D.semigroupType :=
  D.almostSymmetric_iff_two_genus_eq
example : 0∉D.doubleGapFinset := by simp [doubleGapFinset]
example : D.frobenius∉D.doubleGapFinset := by simp [doubleGapFinset]
example {a : ℕ} (ha : a∈D.doubleGapFinset) : D.frobenius-a∈D.doubleGapFinset :=
  D.doubleGap_reflection ha
