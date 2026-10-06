import P23.Monomial.PlainQuotient
namespace P23.Monomial
variable {k : Type*} [Field k] (R : Finset PlainExp)
example (p : PlainExp) : PlainMonomialArtin.PXall (k := k) R p ≠ 0 ↔
    p ∈ plainStandardSet R := plain_PXall_nonzero_iff R p
example : PlainVariablesSurvive R ↔
    ∀ j, PlainMonomialArtin.PXall (k := k) R (plainUnitVector j) ≠ 0 :=
  plainVariablesSurvive_iff_nonzero R
example (I : Ideal (MvPolynomial (Fin 3) k)) (n : ℕ)
    (h : P23.Presentation.HasMinimalGeneratorCard I n) :
    P23.Presentation.idealGeneratorMu I=n := plain_idealGeneratorMu_eq_of_minimal I n h
end P23.Monomial
