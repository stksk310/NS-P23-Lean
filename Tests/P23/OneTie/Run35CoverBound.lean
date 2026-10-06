import P23.OneTie.CoverBorderBound
open P23.OneTie
variable {a b c : ℕ} [NeZero a]

example (S : Finset (Normal a b c)) (h : CoverHypotheses S) (h2 : S.card=2) :
    (borderFinset S).card ≤ 4 := by
  exact two_root_nondominant_border_card_le_four S h h2

example (S : Finset (Normal a b c)) (h : CoverHypotheses S) (h3 : S.card=3) :
    (borderFinset S).card ≤ 5 := by
  exact three_root_nondominant_border_card_le_five S h h3

example (S : Finset (Normal a b c)) (h : CoverHypotheses S) :
    (borderFinset S).card ≤ S.card+2 := by
  exact oneTie_nondominant_border_card_le_type_plus_two S h
