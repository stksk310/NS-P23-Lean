import P23.Monomial.PlainDominance

namespace P23.Monomial
noncomputable section

theorem plain_type_three_ng_border_frontier (R : Finset PlainExp)
    (ha : PlainRootAntichain R) (h3 : R.card=3) (hv : PlainVariablesSurvive R)
    (hc : HasPlainDirectionalCentres R) :
    (plainBorderFinset R).card=4 ∨ (plainBorderFinset R).card=6 ∨
      (plainBorderFinset R).card=7 := by
  obtain ⟨p,q,r,hpq,hpr,hqr,rfl⟩ := Finset.card_eq_three.mp h3
  rcases plain_three_root_coordinate_patterns p q r hpq hpr hqr ha hv hc with h | h | h
  · have hh := plain_triangle_pattern_card p q r h
    omega
  · have hh := plain_plane_pattern_card p q r hpq hpr hqr ha h
    omega
  · have hh := plain_dominant_pattern_card p q r hpq hpr hqr ha hc h
    omega

theorem plain_type_three_border_seven_has_dominant_root (R : Finset PlainExp)
    (ha : PlainRootAntichain R) (h3 : R.card=3) (hv : PlainVariablesSurvive R)
    (hc : HasPlainDirectionalCentres R) (h7 : (plainBorderFinset R).card=7) :
    ∃ s, PlainIsDominantRoot R s := by
  obtain ⟨p,q,r,hpq,hpr,hqr,rfl⟩ := Finset.card_eq_three.mp h3
  rcases plain_three_root_coordinate_patterns p q r hpq hpr hqr ha hv hc with h | h | h
  · have hh := plain_triangle_pattern_card p q r h
    omega
  · have hh := plain_plane_pattern_card p q r hpq hpr hqr ha h
    omega
  · exact plain_dominant_axis_pattern_has_dominant p q r hc h

end
end P23.Monomial
