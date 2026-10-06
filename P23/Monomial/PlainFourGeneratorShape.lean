import P23.Monomial.PlainNoFive

/-! Exact triangle extraction from the frozen ordinary coordinate cover. -/
namespace P23.Monomial
noncomputable section

theorem plain_ordered_triangle_roots (p q t : PlainExp)
    (h : p 0+1=q 0 ∧ q 0=t 0 ∧ q 1+1=p 1 ∧ p 1=t 1 ∧
      t 2+1=p 2 ∧ p 2=q 2) :
    ∃ r u v : ℕ, ({p,q,t} : Finset PlainExp)=plainTriangleRoots r u v := by
  have hp : p=plainExp (p 0) (q 1+1) (t 2+1) := by
    rw [plainExp_eq_coordinates]; omega
  have hq : q=plainExp (p 0+1) (q 1) (t 2+1) := by
    rw [plainExp_eq_coordinates]; omega
  have ht : t=plainExp (p 0+1) (q 1+1) (t 2) := by
    rw [plainExp_eq_coordinates]; omega
  exact ⟨p 0,q 1,t 2,plain_three_finset_congr hp hq ht⟩

theorem plain_triangle_pattern_exact_roots (p q t : PlainExp)
    (h : plainTrianglePattern p q t) :
    ∃ r u v : ℕ, ({p,q,t} : Finset PlainExp)=plainTriangleRoots r u v := by
  rcases h with h | h | h | h | h | h
  · exact plain_ordered_triangle_roots p q t h
  · obtain ⟨r,u,v,he⟩ := plain_ordered_triangle_roots p t q h
    refine ⟨r,u,v,?_⟩
    rw [←he]; ext s; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  · obtain ⟨r,u,v,he⟩ := plain_ordered_triangle_roots q p t h
    refine ⟨r,u,v,?_⟩
    rw [←he]; ext s; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  · obtain ⟨r,u,v,he⟩ := plain_ordered_triangle_roots q t p h
    refine ⟨r,u,v,?_⟩
    rw [←he]; ext s; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  · obtain ⟨r,u,v,he⟩ := plain_ordered_triangle_roots t p q h
    refine ⟨r,u,v,?_⟩
    rw [←he]; ext s; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  · obtain ⟨r,u,v,he⟩ := plain_ordered_triangle_roots t q p h
    refine ⟨r,u,v,?_⟩
    rw [←he]; ext s; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto

theorem plain_three_root_four_border_exact_triangle (R : Finset PlainExp)
    (ha : PlainRootAntichain R) (h3 : R.card=3) (hv : PlainVariablesSurvive R)
    (hc : HasPlainDirectionalCentres R) (h4 : (plainBorderFinset R).card=4) :
    ∃ r u v : ℕ, R=plainTriangleRoots r u v ∧
      plainBorderFinset R=plainTriangleBorder r u v := by
  obtain ⟨p,q,t,hpq,hpt,hqt,rfl⟩ := Finset.card_eq_three.mp h3
  have htriangle : plainTrianglePattern p q t := by
    rcases plain_three_root_coordinate_patterns p q t hpq hpt hqt ha hv hc
      with h | h | h
    · exact h
    · have h6 := plain_plane_pattern_card p q t hpq hpt hqt ha h
      omega
    · have h7 := plain_dominant_pattern_card p q t hpq hpt hqt ha hc h
      omega
  obtain ⟨r,u,v,he⟩ := plain_triangle_pattern_exact_roots p q t htriangle
  refine ⟨r,u,v,he,?_⟩
  rw [he]
  exact plainTriangle_border_exact r u v

end
end P23.Monomial
