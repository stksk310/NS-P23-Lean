import P23.Monomial.PlainCoefficients
namespace P23.Monomial
variable {k : Type*} [Field k] (R : Finset PlainExp) (hR : R.Nonempty)
example (p q : PlainExp) : p + q = 0 ↔ p = 0 ∧ q = 0 := plain_add_eq_zero_iff p q
example (j : Fin 3) (p q : PlainExp) (h : p+q=plainUnitVector j) : p=0 ∨ q=0 :=
  plain_variable_is_atom j p q h
example (m e t : PlainMonomialIndex R) (h : m.1+e.1=t.1) (v : PlainMonomialArtin k R) :
    plainCoeffAt R t (PX R m.1 m.2 * v) = plainCoeffAt R e v :=
  plainCoeffAt_PX_mul R m e t h v
end P23.Monomial
