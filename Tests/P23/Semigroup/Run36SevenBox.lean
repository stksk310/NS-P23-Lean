import P23.Monomial.PlainSevenBox

open P23.Monomial
#check SevenBoxShape
#check sevenBoxExponent_injective
#check sevenBoxShape_card
#check sevenBox_standard_iff
#check P23.Monomial.plain_seven_border_exact_box

example (A B C : ℕ) : Fintype.card (SevenBoxShape A B C)=A*B*C+2 := sevenBoxShape_card A B C
example (R : Finset PlainExp) (ha : PlainRootAntichain R) (h3 : R.card=3)
    (hv : PlainVariablesSurvive R) (hc : HasPlainDirectionalCentres R)
    (h7 : (plainBorderFinset R).card=7) :
    ∃ e : Equiv.Perm (Fin 3),∃ A B C,2≤A ∧ 2≤B ∧ 2≤C ∧
      R.image (plainCoordinatePerm e)=plainDominantAxisRoots (A-1) (B-1) (C-1) :=
  plain_seven_border_exact_box R ha h3 hv hc h7
