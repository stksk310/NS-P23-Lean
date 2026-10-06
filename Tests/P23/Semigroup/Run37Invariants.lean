import P23.Semigroup.NumericalInvariants
open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup
#check one_not_mem_Gamma
#check gapFinset_nonempty
#check frobenius_mem_gapFinset
#check gap_le_frobenius
#check frobenius_not_mem_Gamma
#check frobenius_lt_imp_mem_Gamma
#check frobenius_isPseudoFrobenius
#check pseudoFrobenius_pos
#check pseudoFrobeniusNat_mem_gapFinset
#check pseudoFrobeniusNat_injective
#check pseudoFrobeniusSum_erase

variable (D : FourGeneratedNumericalSemigroup)
example : 1∉D.Gamma := D.one_not_mem_Gamma
example : D.gapFinset.Nonempty := D.gapFinset_nonempty
example {a : ℕ} (ha : a∈D.gapFinset) : a≤D.frobenius := D.gap_le_frobenius ha
example {a : ℕ} (ha : D.frobenius<a) : a∈D.Gamma := D.frobenius_lt_imp_mem_Gamma ha
example : D.IsPseudoFrobenius (D.frobenius:ℤ) := D.frobenius_isPseudoFrobenius
example (f : D.PseudoFrobeniusIndex) : 0<f.1 := D.pseudoFrobenius_pos f
example (f : D.PseudoFrobeniusIndex) : f.1≤(D.frobenius:ℤ) := D.pseudoFrobenius_le_frobenius f
example (f : D.PseudoFrobeniusIndex) : (D.pseudoFrobeniusNat f:ℤ)=f.1 := D.pseudoFrobeniusNat_cast f
example : Function.Injective D.pseudoFrobeniusNat := D.pseudoFrobeniusNat_injective
