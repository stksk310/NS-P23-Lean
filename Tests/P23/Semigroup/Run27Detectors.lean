import P23.Semigroup.ChosenBaseRelationSpace

noncomputable section

open P23.Semigroup P23.Presentation
open FourGeneratedNumericalSemigroup
variable {k : Type*} [Field k] (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
local instance (p : Prop) : Decidable p := Classical.propDecidable p

example (g : D.BaseAdaptedGlobalConnector i) (p : FourPoly k) :
    chosenBaseConnectorCoeff D i g (baseSpecialization D i p) =
      -(D.degreeComponentCoeffVector g.1.1 p) g.2.1 :=
  chosenBaseConnectorCoeff_specialization D i g p
example (g h : D.BaseAdaptedGlobalConnector i) :
    chosenBaseConnectorCoeff (k := k) D i g (D.specializedConnectorPolynomial i h) =
      if g = h then 1 else 0 :=
  chosenBaseConnectorCoeff_specializedConnector D i g h
example (g h : D.BaseAdaptedGlobalConnector i) (hne : g.1.1 ≠ h.1.1) :
    chosenBaseConnectorCoeff (k := k) D i g (D.specializedConnectorPolynomial i h) = 0 :=
  chosenBaseConnectorCoeff_of_degree_ne D i g h hne
example (d : D.BettiDegreeIndex) (g h : D.BaseAdaptedConnector i d.2)
    (hne : g.1 ≠ h.1) :
    chosenBaseConnectorCoeff (k := k) D i ⟨d,g⟩
      (D.specializedConnectorPolynomial i ⟨d,h⟩) = 0 :=
  chosenBaseConnectorCoeff_same_degree_other_target D i d g h hne
example (g h : D.BaseAdaptedGlobalConnector i) (q : TailPoly k)
    (hq : q ∈ polyVariableIdeal) (hi : i ∈ D.combinedSupport h.1.1) :
    chosenBaseConnectorCoeff D i g
      (q * (-MvPolynomial.monomial (D.connectorRightTail i h) 1)) = 0 :=
  chosenBaseConnectorCoeff_mul_external_eq_zero D i g h q hq hi
example (g h : D.BaseAdaptedGlobalConnector i) (q : TailPoly k)
    (hq : q ∈ polyVariableIdeal) (hi : i ∉ D.combinedSupport h.1.1) :
    chosenBaseConnectorCoeff D i g
      (q * (MvPolynomial.monomial (D.connectorLeftTail i h) 1 -
        MvPolynomial.monomial (D.connectorRightTail i h) 1)) = 0 :=
  chosenBaseConnectorCoeff_mul_internal_eq_zero D i g h q hq hi
example (g h : D.BaseAdaptedGlobalConnector i) (w : Fin 3 →₀ ℕ) (c : k)
    (hw : w ≠ 0) (hi : i ∈ D.combinedSupport h.1.1) :
    chosenBaseConnectorCoeff D i g
      (MvPolynomial.monomial w c * (-MvPolynomial.monomial (D.connectorRightTail i h) 1)) = 0 :=
  chosenBaseConnectorCoeff_positive_monomial_mul_external D i g h w c hw hi
example (g : D.BaseAdaptedGlobalConnector i) (p : TailPoly k)
    (hp : p ∈ polyVariableIdeal * chosenBaseDefiningIdeal D i) :
    chosenBaseConnectorCoeff D i g p = 0 :=
  chosenBaseConnectorCoeff_eq_zero_of_mem_mul D i g p hp

end
