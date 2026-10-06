import P23.Semigroup.AperyGenus
open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup
#check aperyOfResidue
#check aperyQuotient
#check apery_residue_decomposition
#check gap_iff_lt_aperyQuotient
#check gapResidueEquiv
#check genus_eq_sum_aperyQuotient
#check apery_genus_formula_doubled

noncomputable section
open scoped BigOperators
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
example (r : Fin (D.n i)) : (D.aperyOfResidue i r).1.1=r.1+D.n i*D.aperyQuotient i r :=
  D.apery_residue_decomposition i r
example (r : Fin (D.n i)) (k : ℕ) : r.1+D.n i*k∈D.gapFinset ↔ k<D.aperyQuotient i r :=
  D.gap_iff_lt_aperyQuotient i r k
example : D.genus=∑ r : Fin (D.n i),D.aperyQuotient i r := D.genus_eq_sum_aperyQuotient i
example : 2*(D.n i:ℤ)*(D.genus:ℤ)=
    2*(∑ w : D.AperyIndex i,(w.1.1:ℤ))-(D.n i:ℤ)*((D.n i:ℤ)-1) :=
  D.apery_genus_formula_doubled i
example (r : Fin (D.n i)) : r.1∈D.gapFinset ↔ 0<D.aperyQuotient i r := by
  simpa using D.gap_iff_lt_aperyQuotient i r 0
