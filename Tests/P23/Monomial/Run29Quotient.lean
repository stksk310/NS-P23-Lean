import P23.Monomial.PlainQuotient

namespace P23.Monomial
noncomputable section
variable (k : Type*) [Field k] (R : Finset PlainExp) (hR : R.Nonempty)
example (p : PlainExp) (r : k) :
    plainPolyToArtin k R (MvPolynomial.monomial p r) =
      r • PlainMonomialArtin.PXall (k := k) R p := plainPolyToArtin_monomial k R p r
example : Function.Surjective (plainPolyToArtin k R) := plainPolyToArtin_surjective k R
example : RingHom.ker (plainPolyToArtin k R).toRingHom =
    plainMonomialIdeal k (plainBorderFinset R) := plainPolyToArtin_kernel k R
example : (MvPolynomial (Fin 3) k ⧸ plainMonomialIdeal k (plainBorderFinset R)) ≃ₐ[k]
    PlainMonomialArtin k R := plainQuotientEquiv k R
end
end P23.Monomial
