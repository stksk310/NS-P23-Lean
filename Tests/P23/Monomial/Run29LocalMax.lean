import P23.Monomial.PlainLocalSocle
namespace P23.Monomial
variable {k : Type*} [Field k]
example (R : Finset PlainExp) (hR : R.Nonempty)
    (I : Ideal (PlainMonomialArtin k R)) (hI : I.IsMaximal) :
    I = plainAugmentationIdeal R hR := plainMaximalIdeal_eq_augmentationIdeal R hR I hI
end P23.Monomial
