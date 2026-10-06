import P23.Semigroup.PlainAperyResidues
noncomputable section
open P23.Semigroup
#check plainStandardAperyEquiv
#check plainStandardResidueEquiv
#check plain_standard_degree_injective

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (M : BudgetZeroPlainModel D i) :
    P23.Monomial.PlainMonomialIndex M.roots ≃ D.AperyIndex i := plainStandardAperyEquiv M
example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (M : BudgetZeroPlainModel D i) :
    P23.Monomial.PlainMonomialIndex M.roots ≃ ZMod (D.n i) := plainStandardResidueEquiv M
