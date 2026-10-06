import P23.Presentation.TieQuotient

open scoped BigOperators

namespace P23.Presentation.Run14Test

open P23.OneTie
open MvPolynomial

section Symbolic

variable {k : Type} [Field k]
variable {a b c : ℕ} [NeZero a]

#check ThreePoly
#check polyX
#check polyY
#check polyZ
#check tiePolynomial
#check normalizeExponent
#check normalExponent
#check normalizeExponent_add
#check normalizeExponent_normalExponent
#check polyToNormalAlg
#check polyToNormalAlg_polyX
#check polyToNormalAlg_polyY
#check polyToNormalAlg_polyZ
#check polyToNormalAlg_monomial
#check polyToNormalAlg_tiePolynomial
#check polyToNormalAlg_surjective
#check tieIdeal
#check monomial_sub_normalMonomial_mem_tieIdeal
#check reducedRepresentative
#check reducedRepresentative_isReduced
#check sub_reducedRepresentative_mem_tieIdeal
#check polyToNormalAlg_injective_on_reduced
#check polyToNormalAlg_ker
#check TieQuotient
#check tieQuotientEquivNormalMonoidAlgebra
#check tieQuotientEquiv_polyX
#check tieQuotientEquiv_polyY
#check tieQuotientEquiv_polyZ
#check tieQuotientEquiv_monomial
#check NormalMonoidAlgebraAsTieQuotient
#check normalMonoidAlgebra_as_tieQuotient

end Symbolic

section Concrete

/- Mixed and nonprimitive exact variable/tie images. -/
example : polyToNormalAlg (k := ℚ) (a := 2) (b := 1) (c := 1) polyX =
    monomial (Normal.xGenerator : Normal 2 1 1) := by simp

example : polyToNormalAlg (k := ℚ) (a := 4) (b := 2) (c := 2)
    (tiePolynomial (k := ℚ) 4 2 2) = 0 := by simp

/- Pure nonprimitive tie. -/
example : polyToNormalAlg (k := ℚ) (a := 4) (b := 2) (c := 0)
    (tiePolynomial (k := ℚ) 4 2 0) = 0 := by simp

/- a=1 and the extreme x-1 relation. -/
example : polyToNormalAlg (k := ℚ) (a := 1) (b := 3) (c := 2)
    (tiePolynomial (k := ℚ) 1 3 2) = 0 := by simp

example : polyToNormalAlg (k := ℚ) (a := 1) (b := 0) (c := 0)
    (tiePolynomial (k := ℚ) 1 0 0) = 0 := by simp

/- One and multiple x-tie reductions. -/
example : polyToNormalAlg (k := ℚ) (a := 3) (b := 2) (c := 1)
    (MvPolynomial.monomial (Finsupp.single 0 4) 1) =
      monomial (normalizeExponent 3 2 1 (Finsupp.single 0 4)) := by simp

example : polyToNormalAlg (k := ℚ) (a := 3) (b := 2) (c := 1)
    (MvPolynomial.monomial (Finsupp.single 0 10) 1) =
      monomial (normalizeExponent 3 2 1 (Finsupp.single 0 10)) := by simp

/- A multi-term kernel element. -/
example : polyX * tiePolynomial (k := ℚ) 3 2 1 +
    polyY * tiePolynomial (k := ℚ) 3 2 1 ∈ tieIdeal (k := ℚ) 3 2 1 := by
  apply Ideal.add_mem
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

/- A reduced nonzero polynomial is not in the kernel. -/
example : polyY + polyZ ∉ RingHom.ker
    (polyToNormalAlg (k := ℚ) (a := 3) (b := 2) (c := 1)).toRingHom := by
  rw [RingHom.mem_ker]
  intro h
  have hc := congrArg (fun f : NormalMonoidAlgebra ℚ 3 2 1 =>
    f.coeff (Normal.yGenerator : Normal 3 2 1)) h
  simp [monomial, Finsupp.single_apply, Normal.yGenerator, Normal.zGenerator] at hc

/- Quotient transport on variables and a wrapped monomial. -/
example : tieQuotientEquivNormalMonoidAlgebra (k := ℚ) (a := 3) (b := 2) (c := 1)
    (Ideal.Quotient.mk _ polyX) = monomial (Normal.xGenerator : Normal 3 2 1) := by simp

example : tieQuotientEquivNormalMonoidAlgebra (k := ℚ) (a := 3) (b := 2) (c := 1)
    (Ideal.Quotient.mk _
      (MvPolynomial.monomial (Finsupp.single 0 7 + Finsupp.single 1 1) 1)) =
      monomial (normalizeExponent 3 2 1
        (Finsupp.single 0 7 + Finsupp.single 1 1)) := by simp

end Concrete

end P23.Presentation.Run14Test
