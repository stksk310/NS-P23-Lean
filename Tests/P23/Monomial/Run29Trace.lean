import P23.Monomial.PlainTrace
namespace P23.Monomial
variable {k : Type*} [Field k] (R : Finset PlainExp) (hR : R.Nonempty)
example : PlainTraceSubmodule k R =
    Submodule.span (PlainMonomialArtin k R) (plainRootTraceValueSet k R) :=
  plainTrace_eq_span_rootTraceValueSet R
example (hcard : 2 ≤ R.card) (hanti : PlainRootAntichain R)
    (j : Fin 3) (hj : plainUnitVector j ∈ plainStandardFinset R)
    (htrace : PX (k := k) R (plainUnitVector j) hj ∈ PlainTraceSubmodule k R) :
    ∃ (F : PlainOmega k R →ₗ[PlainMonomialArtin k R] PlainMonomialArtin k R)
      (s : PlainExp) (hs : s ∈ R),
      plainCoeffAt R ⟨plainUnitVector j,hj⟩ (F (PU R (plainRootIndex R s hs))) ≠ 0 :=
  plain_exists_root_image_with_variable_coeff_of_mem_trace R hR hcard hanti j hj htrace
end P23.Monomial
