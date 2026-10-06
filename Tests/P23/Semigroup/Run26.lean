import P23.Semigroup.BaseAdaptedPresentation
open P23.Semigroup FourGeneratedNumericalSemigroup
variable {k : Type*} [Field k] (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
example {d : ℕ} (hd : D.IsBettiDegree d) (hi : i ∈ D.combinedSupport d) :
    0 < (D.baseUsingFactorization i hd hi).1 i := D.baseUsingFactorization_pos i hd hi
example : D.toricIdeal (k := k) =
    Ideal.span (Set.range (D.baseAdaptedGlobalConnectorBinomial (k := k) i)) :=
  D.toricIdeal_eq_span_baseAdaptedGlobalConnectorBinomials i
example : (D.baseAdaptedConnectorRelationFinset i).card = D.semigroupRho :=
  D.baseAdaptedConnectorRelationFinset_card_eq_rho i
example (g : D.BaseAdaptedGlobalConnector i) (hi : i ∉ D.combinedSupport g.1.1) :
    D.LiveTailBinomial (k := k) i (D.specializedConnectorPolynomial i g) :=
  D.specializedConnector_isLiveBinomial_of_base_not_mem_support i g hi
example : (D.internalBaseConnectorFinset i).card = D.fourBaseBudget i :=
  D.internalBaseConnectorFinset_card i
example : (D.externalBaseConnectorFinset i).card = D.semigroupRho - D.fourBaseBudget i :=
  D.externalBaseConnectorFinset_card i
example (h : D.fourBaseBudget i = 0) : D.IsMonomialChosenBaseIdeal (k := k) i :=
  D.chosenBaseIdeal_monomial_of_budget_eq_zero i h
example (h : D.fourBaseBudget i = 1) : D.OneLiveBinomialGeneration (k := k) i :=
  D.chosenBaseIdeal_one_live_binomial_generation_of_budget_eq_one i h
example (g : D.BaseAdaptedGlobalConnector i) (h : i ∉ D.combinedSupport g.1.1) :
    (D.connectorLeftTail i g).support.card = 1 ∨ (D.connectorRightTail i g).support.card = 1 :=
  D.internal_connector_pure_side i g h
example : chosenBaseDefiningIdeal (k := k) D i =
    Ideal.span (Set.range (D.specializedConnectorPolynomial (k := k) i)) :=
  D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i
example : D.ChosenBaseReduction (k := k) i := D.chosenBaseReduction i
