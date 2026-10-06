import P23.Monomial.PlainSocle
namespace P23.Monomial
variable {k : Type*} [Field k] (R : Finset PlainExp) (hR : R.Nonempty) (ha : PlainRootAntichain R)
example : PlainDirectSocle (k := k) R hR = plainRootSpan R := plain_socle_eq_rootSpan R hR ha
example : plainDirectType k R hR = R.card := plainDirectType_eq_rootCard R hR ha
end P23.Monomial
