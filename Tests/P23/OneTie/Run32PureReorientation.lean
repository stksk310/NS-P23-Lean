import P23.OneTie.PureReorientation
open P23.OneTie
#check pureSwapXYMulEquiv
#check pureSwapXYBorder
#check pureXZ_reoriented_threeBorder

example : pureSwapXY (⟨2,5,1,by omega⟩ : Normal 3 2 0) = (⟨1,8,1,by omega⟩ : Normal 2 3 0) := rfl

example : pureXYPolynomialRename (P23.Presentation.tiePolynomial (k := ℚ) 3 2 0) =
    -P23.Presentation.tiePolynomial (k := ℚ) 2 3 0 := pureXYPolynomialRename_tie
