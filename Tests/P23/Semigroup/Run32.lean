import P23.Semigroup.RhoFourLocalReduction
open P23.Semigroup P23.OneTie
#check RhoFourResidualPureBase
#check rho_four_residual_pure_at_every_base
#check RhoFourLocalThreeBorderReduction

open FourGeneratedNumericalSemigroup
example {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
    (R : RhoFourResidualPureBase D i) :
    R.chosenBaseEquivalence =
      R.tagged.presentation.chosenBaseEquivCanonicalOneTie.trans R.residual.equivalence := rfl
example (D : FourGeneratedNumericalSemigroup) (ht : D.semigroupType = 3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho = 4) :
    ∀ i, Nonempty (RhoFourResidualPureBase D i) := rho_four_residual_pure_at_every_base D ht hn hr
