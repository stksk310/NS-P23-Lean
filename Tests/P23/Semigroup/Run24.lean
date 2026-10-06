import P23.Semigroup.ToricPresentation
import P23.Semigroup.BettiRelationSpace

namespace P23.Semigroup

open FourGeneratedNumericalSemigroup

#check semigroupPolyMap_monomial
#check semigroupPolyMap_surjective
#check fiberBinomial_mem_toricIdeal
#check toricIdeal_eq_span_fiberBinomials
#check fiberBinomial_mem_lower_of_adj
#check fiberBinomial_mem_lower_of_sameComponent
#check fiberPolynomial_injective
#check fiberPolynomial_mem_toricIdeal_iff
#check fiberToComponentRelation_surjective
#check componentRelationSpace_finrank
#check degreeNewToricRelationSpaceEquiv
#check connectorClassBasis
#check degreeToricRelation_generator_card_lower_bound
#check degreeToricRelation_connector_card_exact
#check toricBettiContribution_eq_componentCount_sub_one
#check toricBettiPresentationBridge

variable {k : Type*} [Field k] (D : FourGeneratedNumericalSemigroup)

example (u : Fin 4 →₀ ℕ) (r : k) :
    D.semigroupPolyMap (MvPolynomial.monomial u r) =
      r • T (k := k) D
        ⟨D.weightedDegree u, (D.mem_Gamma_iff _).2 ⟨u, rfl⟩⟩ :=
  D.semigroupPolyMap_monomial u r

example {d : ℕ} (u v : D.FactorizationAt d) :
    D.fiberBinomial (k := k) u v ∈ D.toricIdeal (k := k) :=
  D.fiberBinomial_mem_toricIdeal u v

example {d : ℕ} (hd : D.IsBettiDegree d) (hcard : D.componentCount d = 2) :
    Module.finrank k (D.DegreeNewToricRelationSpace k d) = 1 := by
  rw [D.toricBettiContribution_eq_componentCount_sub_one hd, hcard]

example {d : ℕ} (hd : D.IsBettiDegree d) (hcard : D.componentCount d = 3) :
    Module.finrank k (D.DegreeNewToricRelationSpace k d) = 2 := by
  rw [D.toricBettiContribution_eq_componentCount_sub_one hd, hcard]

example {d : ℕ} (hd : D.IsBettiDegree d) :
    D.GeneratesDegreeNewRelations (D.connectorRelationFinset (k := k) hd) :=
  D.connectorRelationFinset_generates hd

example {d : ℕ} (hd : D.IsBettiDegree d)
    (G : Finset (D.FiberRelationSpace k d))
    (hG : D.GeneratesDegreeNewRelations G) :
    D.bettiContribution d ≤ G.card :=
  D.degreeToricRelation_generator_card_lower_bound hd G hG

end P23.Semigroup
