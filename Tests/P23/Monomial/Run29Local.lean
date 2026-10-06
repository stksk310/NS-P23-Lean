import P23.Monomial.PlainLocalSocle
namespace P23.Monomial
variable {k : Type*} [Field k] (R : Finset PlainExp) (hR : R.Nonempty)
example : (plainAugmentationIdeal (k := k) R hR).IsMaximal := plainAugmentationIdeal_isMaximal R hR
example : IsLocalRing (PlainMonomialArtin k R) := plainIsLocalRing R hR
example : plainVariableIdeal (k := k) R = plainAugmentationIdeal R hR :=
  plainVariableIdeal_eq_augmentationIdeal R hR
end P23.Monomial
