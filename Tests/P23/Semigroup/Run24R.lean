import P23.Semigroup.BettiLowerDegree

namespace P23.Semigroup

open FourGeneratedNumericalSemigroup

noncomputable section

#check FourGeneratedNumericalSemigroup.ActualLowerDegreeRelationSubmodule
#check FourGeneratedNumericalSemigroup.componentKernel_of_fiberPolynomial_mem_lower
#check FourGeneratedNumericalSemigroup.fiberPolynomial_mem_lower_iff_componentKernel
#check FourGeneratedNumericalSemigroup.actualLowerDegreeRelationSubmodule_eq_componentKernel
#check FourGeneratedNumericalSemigroup.ActualDegreeNewToricRelationSpace
#check FourGeneratedNumericalSemigroup.actualDegreeNewToricRelationSpace_finrank
#check FourGeneratedNumericalSemigroup.actualConnectorClassBasis
#check FourGeneratedNumericalSemigroup.actualDegreeToricRelation_generator_card_lower_bound
#check FourGeneratedNumericalSemigroup.generatesDegreeDModuloLower_iff_actual
#check FourGeneratedNumericalSemigroup.exactToricBettiPresentationBridge

variable {k : Type*} [Field k] (D : FourGeneratedNumericalSemigroup)

-- A lower edge multiplied by one monomial has zero degree-d component sum.
example {e d : ℕ} (hed : e < d) (u v : D.FactorizationAt e)
    (w : Fin 4 →₀ ℕ) (r : k) :
    D.degreeComponentCoeffVector (k := k) d
      (MvPolynomial.monomial w r * D.fiberBinomial (k := k) u v) = 0 :=
  D.degreeComponentCoeffVector_monomial_mul_fiberBinomial hed u v w r

-- In the exact-degree branch the shifted endpoints share a component.
example {e d : ℕ} (u v : D.FactorizationAt e) (w : Fin 4 →₀ ℕ)
    (hdeg : D.weightedDegree w + e = d) (hw : w ≠ 0) :
    D.componentOf (D.shiftedFactorization u w hdeg) =
      D.componentOf (D.shiftedFactorization v w hdeg) :=
  D.shiftedFactorizations_sameComponent u v w hdeg hw

-- A nonhomogeneous polynomial multiplier is handled termwise.
example {e d : ℕ} (hed : e < d) (u v : D.FactorizationAt e)
    (p : FourPoly k) :
    D.degreeComponentCoeffVector (k := k) d
      (p * D.fiberBinomial (k := k) u v) = 0 :=
  D.degreeComponentCoeffVector_mul_fiberBinomial hed u v p

-- Cancellation among several lower-ideal terms is covered by ideal closure.
example {e₁ e₂ d : ℕ} (h₁ : e₁ < d) (h₂ : e₂ < d)
    (u₁ v₁ : D.FactorizationAt e₁) (u₂ v₂ : D.FactorizationAt e₂)
    (p q : FourPoly k) :
    D.degreeComponentCoeffVector (k := k) d
      (p * D.fiberBinomial (k := k) u₁ v₁ +
        q * D.fiberBinomial (k := k) u₂ v₂) = 0 := by
  apply D.mem_lowerToricIdeal_componentCoeff_zero d
  apply Ideal.add_mem
  · apply Ideal.mul_mem_left
    apply Ideal.subset_span
    exact ⟨e₁, h₁, u₁, v₁, rfl⟩
  · apply Ideal.mul_mem_left
    apply Ideal.subset_span
    exact ⟨e₂, h₂, u₂, v₂, rfl⟩

example {d : ℕ} (a : D.FiberRelationSpace k d) :
    D.fiberPolynomial (k := k) d a.1 ∈ D.lowerToricIdeal (k := k) d ↔
      a ∈ LinearMap.ker (D.fiberToComponentRelation (k := k) d) :=
  D.fiberPolynomial_mem_lower_iff_componentKernel a

example (d : ℕ) :
    D.ActualLowerDegreeRelationSubmodule (k := k) d =
      LinearMap.ker (D.fiberToComponentRelation (k := k) d) :=
  D.actualLowerDegreeRelationSubmodule_eq_componentKernel d

example {d : ℕ} (hd : D.IsBettiDegree d)
    (hcard : D.componentCount d = 2) :
    Module.finrank k (D.ActualDegreeNewToricRelationSpace k d) = 1 := by
  rw [D.actualDegreeNewToricRelationSpace_finrank_eq_componentCount_sub_one hd,
    hcard]

example {d : ℕ} (hd : D.IsBettiDegree d)
    (hcard : D.componentCount d = 3) :
    Module.finrank k (D.ActualDegreeNewToricRelationSpace k d) = 2 := by
  rw [D.actualDegreeNewToricRelationSpace_finrank_eq_componentCount_sub_one hd,
    hcard]

example {d : ℕ} (hd : D.IsBettiDegree d) :
    Module.Basis (D.ComponentConnector hd) k
      (D.ActualDegreeNewToricRelationSpace k d) :=
  D.actualConnectorClassBasis hd

example {d : ℕ} (hd : D.IsBettiDegree d) :
    D.GeneratesDegreeDModuloLower (k := k)
      (D.connectorRelationFinset (k := k) hd) :=
  (D.generatesDegreeDModuloLower_iff_actual _).2
    (D.actualConnectorRelationFinset_generates hd)

example {d : ℕ} (hd : D.IsBettiDegree d)
    (G : Finset (D.FiberRelationSpace k d))
    (hG : D.GeneratesDegreeDModuloLower (k := k) G) :
    D.bettiContribution d ≤ G.card :=
  D.degreeD_mod_lower_generator_card_lower_bound hd G hG

end

end P23.Semigroup
