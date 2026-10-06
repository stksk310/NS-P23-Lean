import P23.Monomial.PlainArtin
open P23.Monomial
example (k : Type*) [Field k] (R : Finset PlainExp) (p q : PlainExp)
    (hp : p ∈ plainStandardFinset R) (hq : q ∈ plainStandardFinset R) :
    PlainMonomialArtin.PX (k := k) R p hp * PlainMonomialArtin.PX (k := k) R q hq =
      if h : p + q ∈ plainStandardFinset R then PlainMonomialArtin.PX (k := k) R (p+q) h else 0 :=
  PlainMonomialArtin.PX_mul_PX R p q hp hq
example (k : Type*) [Field k] (R : Finset PlainExp) (x y z : PlainMonomialArtin k R) :
    (x*y)*z = x*(y*z) := mul_assoc x y z
example (k : Type*) [Field k] (R : Finset PlainExp) :
    Module.finrank k (PlainMonomialArtin k R) = (plainStandardFinset R).card :=
  PlainMonomialArtin.finrank_plainMonomialArtin k R
