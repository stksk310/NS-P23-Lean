import P23.Semigroup.RhoFourResidualTop
open P23.Semigroup P23.OneTie
-- Break caught: a free formal top or an arbitrary unbound coordinate rename
-- cannot provide these actual degree/socle contracts.
#check residualToTail
#check residualDegree_coordinateGenerator
#check residualDegree_mul
#check residual_weighted_tie
#check residual_isApery_iff_standard
#check residualAperySocleIndex
#check rhoFourResidualTopPattern

noncomputable section
open FourGeneratedNumericalSemigroup
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
variable (R : RhoFourResidualPureBase D i)
local instance : NeZero R.residual.a' := ⟨by have := R.residual.a'_ge_two; omega⟩
example : R.residual.roots={residualRootX R,residualRootY R,residualRootZ R} := residual_roots_exact R
example : residualRootX R ≠ residualRootY R ∧ residualRootX R ≠ residualRootZ R ∧
    residualRootY R ≠ residualRootZ R := residualRoot_distinct R
example (j l : Fin 3) : rootByResidualAxis R j * coordinateGenerator l ∉
    standardSet R.residual.roots := residualRoot_mul_not_standard R j l
example (j : Fin 3) : residualTopDegree R=
    aperySocleDegree D i (residualAperySocleIndex R j)+D.tailGen i j := residualAperySocle_top_equation R j
example : Function.Injective (residualAperySocleIndex R) := residualAperySocleIndex_injective R
example (ht : D.semigroupType=3) : TailSocleTopPattern D i := rhoFourResidualTopPattern R ht
example (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) : Nonempty (TwoTailSources D i) :=
  exists_two_tail_sources D i (rhoFourResidualTopPattern R ht) hn
