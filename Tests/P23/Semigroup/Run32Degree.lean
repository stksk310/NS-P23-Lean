import P23.Semigroup.RhoFourTaggedDegree

open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup
open P23.OneTie P23.Presentation
noncomputable section
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}

example (T : TaggedBudgetOneNormalization D i) (g : D.BaseAdaptedGlobalConnector i) :
    tailDegree D i (T.externalTailExponent g) = g.1.1 := T.normalized_external_degree g

example (T : TaggedBudgetOneNormalization D i) (g : D.BaseAdaptedGlobalConnector i) :
    (T.normalizedExternalFactorization g).1 i = 0 :=
  (T.normalized_external_factorization_at_betti_degree g).2.1
