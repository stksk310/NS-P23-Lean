import P23.Semigroup.RhoFourResidualDegree

open P23.Semigroup P23.OneTie P23.Presentation
open P23.Semigroup.FourGeneratedNumericalSemigroup
noncomputable section
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
variable (T : TaggedBudgetOneNormalization D i)

example (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b
    T.presentation.coordinates.c) : tailDegree D i (canonicalTailExponent T p)=
      T.presentation.coordinates.coordinateDegree (normalExponent p) := canonicalTailExponent_degree T p

-- Break caught: coordinate renaming points the wrong way or ideal membership
-- is used to infer Apéry survival without the exact frozen kernel bridge.
example (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b
    T.presentation.coordinates.c) :
    (canonicalTailExponent T p).mapDomain T.presentation.coordinates.sigma = normalExponent p :=
  canonicalTailExponent_rename T p

example (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b
    T.presentation.coordinates.c) :
    D.IsApery i (tailDegreeGamma D i (canonicalTailExponent T p)) ↔
      p ∈ standardSet T.presentation.roots :=
  chosenBase_canonical_isApery_iff_standard T p

variable (R : RhoFourResidualPureBase D i)
local instance : NeZero R.residual.a' := ⟨by have := R.residual.a'_ge_two; omega⟩
example (j : Fin 3) : residualToTail R (tailToResidual R j)=j :=
  (residualToTail R).apply_symm_apply j
example (p q : Normal R.residual.a' R.residual.b' 0) :
    residualDegree R (p*q)=residualDegree R p+residualDegree R q := residualDegree_mul R p q
example (j : Fin 3) : residualDegree R (coordinateGenerator j)=D.tailGen i (residualToTail R j) :=
  residualDegree_coordinateGenerator R j
example : R.residual.a'*D.tailGen i (residualToTail R 0)=
    R.residual.b'*D.tailGen i (residualToTail R 1) := residual_weighted_tie R
example (p : Normal R.residual.a' R.residual.b' 0) :
    D.IsApery i (tailDegreeGamma D i (residualTailExponent R p)) ↔
      p∈standardSet R.residual.roots := residual_isApery_iff_standard R p
