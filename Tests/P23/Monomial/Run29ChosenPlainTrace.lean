import P23.Semigroup.ChosenBasePlainTrace

open P23.Monomial P23.Semigroup
noncomputable section
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
variable (R : Finset PlainExp) (hR : R.Nonempty)
variable (E : ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] PlainMonomialArtin ℚ R)

example : plainDirectType ℚ R hR = chosenBaseType (k := ℚ) D i :=
  chosenPlain_type_eq R hR E

example (x : ChosenBaseQuotient (k := ℚ) D i) :
    x ∈ ChosenBaseTraceSubmodule (k := ℚ) D i ↔ E x ∈ PlainTraceSubmodule ℚ R :=
  chosenPlain_trace_mem_iff R E x

example : ChosenBaseNearlyGorenstein (k := ℚ) D i ↔ PlainDirectNearlyGorenstein ℚ R hR :=
  chosenPlain_ng_iff R hR E
