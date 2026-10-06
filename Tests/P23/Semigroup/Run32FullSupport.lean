import P23.Semigroup.RhoFourBorderSupport
import P23.OneTie.ThreeBorderSupport

open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup P23.OneTie
noncomputable section
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

example (T : TaggedBudgetOneNormalization D i) (ht : D.semigroupType = 3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho = 4)
    (g : D.BaseAdaptedGlobalConnector i) : ¬NormalHasFullSupport (T.normalizedOfExternal g) :=
  T.normalized_external_not_full_support ht hn hr g
