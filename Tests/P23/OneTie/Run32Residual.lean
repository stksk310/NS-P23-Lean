import P23.OneTie.PureResidualThreeBorder
open P23.OneTie
#check PureResidualThreeBorder
#check pureResidual_roots_exact
#check pureResidual_top_equations
#check pure_three_border_ng_residual
#check pureResidual_presentation_exact

open P23.Artin P23.Presentation
variable {a b : ℕ} [NeZero a] {S : Finset (Normal a b 0)}
example (R : PureResidualThreeBorder S) (hS : S.Nonempty) (ha : IsRootAntichain S) :
    S = R.roots := pureResidual_roots_exact R hS ha
