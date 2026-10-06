import P23.Monomial.PlainCanonicalDual
namespace P23.Monomial
variable {k : Type*} [Field k] (R : Finset PlainExp)
example (m q s : PlainMonomialIndex R) :
    (PX (k := k) R m.1 m.2 • PU (k := k) R s) (PX R q.1 q.2) =
      if m.1 + q.1 = s.1 then 1 else 0 := PX_smul_PU_apply_PX R m q s
example : Submodule.span (PlainMonomialArtin k R) (plainRootDualSet k R) = ⊤ :=
  plainRootDual_span_eq_top R
example (s : PlainExp) (hs : s ∈ R) (w : PlainMonomialIndex R) :
    PX (k := k) R w.1 w.2 • PU (k := k) R (plainRootIndex R s hs) = 0 ↔
      ¬ plainDivides w.1 s := PX_smul_plainRootDual_eq_zero_iff (k := k) R s hs w
end P23.Monomial
