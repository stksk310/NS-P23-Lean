import P23.Monomial.PlainNoFiveFamilies
import P23.Monomial.PlainPermutation
import P23.Monomial.PlainCentrePatterns

namespace P23.Monomial
noncomputable section

theorem plain_three_finset_congr {p q r p' q' r' : PlainExp}
    (hp : p=p') (hq : q=q') (hr : r=r') :
    ({p,q,r} : Finset PlainExp) = {p',q',r'} := by
  cases hp; cases hq; cases hr; rfl

theorem plain_ordered_triangle_card (p q r : PlainExp)
    (h : p 0+1=q 0 ∧ q 0=r 0 ∧ q 1+1=p 1 ∧ p 1=r 1 ∧
      r 2+1=p 2 ∧ p 2=q 2) :
    (plainBorderFinset {p,q,r}).card = 4 := by
  have hp : p = plainExp (p 0) (q 1+1) (r 2+1) := by
    rw [plainExp_eq_coordinates]; omega
  have hq : q = plainExp (p 0+1) (q 1) (r 2+1) := by
    rw [plainExp_eq_coordinates]; omega
  have hr : r = plainExp (p 0+1) (q 1+1) (r 2) := by
    rw [plainExp_eq_coordinates]; omega
  have he : ({p,q,r} : Finset PlainExp) = plainTriangleRoots (p 0) (q 1) (r 2) :=
    plain_three_finset_congr hp hq hr
  rw [he]
  exact plainTriangle_border_card _ _ _

theorem plain_plane_axis_two_card (p q t : PlainExp)
    (hpq : p ≠ q) (ha : PlainRootAntichain {p,q,t})
    (hz : p 2=0 ∧ q 2=0 ∧ t 0=0 ∧ t 1=0 ∧ 0<t 2) :
    (plainBorderFinset {p,q,t}).card = 6 := by
  have hnpq : ¬(p 0 ≤ q 0 ∧ p 1 ≤ q 1 ∧ p 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    apply hpq
    apply ha p (by simp) q (by simp)
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  have hnqp : ¬(q 0 ≤ p 0 ∧ q 1 ≤ p 1 ∧ q 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    apply hpq
    symm
    apply ha q (by simp) p (by simp)
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  have ht : t = plainExp 0 0 (t 2) := by rw [plainExp_eq_coordinates]; omega
  have hp : p = plainExp (p 0) (p 1) 0 := by rw [plainExp_eq_coordinates]; omega
  have hq : q = plainExp (q 0) (q 1) 0 := by rw [plainExp_eq_coordinates]; omega
  by_cases ho : p 0 < q 0
  · have ho' : q 1 < p 1 := by omega
    have he : ({p,q,t} : Finset PlainExp) = plainPlaneAxisRoots (p 0) (q 0) (q 1) (p 1) (t 2) :=
      plain_three_finset_congr hp hq ht
    rw [he]
    exact plainPlaneAxis_border_card _ _ _ _ _ ho ho' hz.2.2.2.2
  · have ho' : q 0 < p 0 := by omega
    have ho'' : p 1 < q 1 := by omega
    have he : ({p,q,t} : Finset PlainExp) = {q,p,t} := by ext a; simp; tauto
    have he' : ({q,p,t} : Finset PlainExp) = plainPlaneAxisRoots (q 0) (p 0) (p 1) (q 1) (t 2) :=
      plain_three_finset_congr hq hp ht
    rw [he,he']
    exact plainPlaneAxis_border_card _ _ _ _ _ ho' ho'' hz.2.2.2.2

theorem plain_plane_permuted_card (e : Equiv.Perm (Fin 3)) (p q t : PlainExp)
    (hpq : p ≠ q) (ha : PlainRootAntichain {p,q,t})
    (hz : p (e 2)=0 ∧ q (e 2)=0 ∧ t (e 0)=0 ∧ t (e 1)=0 ∧ 0<t (e 2)) :
    (plainBorderFinset {p,q,t}).card = 6 := by
  rw [← plainBorder_card_permutation e {p,q,t}]
  have hi : ({p,q,t} : Finset PlainExp).image (plainCoordinatePerm e) =
      {plainCoordinatePerm e p,plainCoordinatePerm e q,plainCoordinatePerm e t} := by simp
  rw [hi]
  apply plain_plane_axis_two_card
  · exact fun h => hpq ((plainCoordinatePerm e).injective h)
  · rw [← hi]
    exact plainAntichain_coordinatePerm e {p,q,t} ha
  · simpa only [plainCoordinatePerm_apply] using hz

theorem plain_dominant_axis_two_card (p q r : PlainExp)
    (ha : PlainRootAntichain {p,q,r}) (hc : HasPlainDirectionalCentres {p,q,r})
    (hp : 0<p 0 ∧ 0<p 1 ∧ 0<p 2)
    (hq : 0<q 0 ∧ q 1=0 ∧ q 2=0)
    (hr : r 0=0 ∧ 0<r 1 ∧ r 2=0) :
    (plainBorderFinset {p,q,r}).card = 7 := by
  have centre (j : Fin 3) (hj : j ≠ 2) : PlainDirectionalCentre {p,q,r} j p := by
    obtain ⟨c,hc⟩ := hc j
    have hb := hc.2 p (by simp) (by fin_cases j <;> simp_all)
    have hb2 := hb 2
    have hh : p 2 ≤ c 2 := by
      simpa [plainPredecessor_apply,hj,Ne.symm hj] using hb2
    have hm := hc.1
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with h | h | h
    · simpa [h] using hc
    · subst c; omega
    · subst c; omega
  have hqp : q ≠ p := by intro h; have he := congrArg (fun s : PlainExp => s 1) h; omega
  have hrp : r ≠ p := by intro h; have he := congrArg (fun s : PlainExp => s 0) h; omega
  have hx := (plain_centre_other_root_coordinates {p,q,r} ha
    (centre 0 (by decide)) (by simp) hqp hq.1).1
  have hy := (plain_centre_other_root_coordinates {p,q,r} ha
    (centre 1 (by decide)) (by simp) hrp hr.2.1).1
  have hpp : p = plainExp (p 0) (p 1) (p 2) := (plainExp_coordinates p).symm
  have hqq : q = plainExp (p 0+1) 0 0 := by rw [plainExp_eq_coordinates]; omega
  have hrr : r = plainExp 0 (p 1+1) 0 := by rw [plainExp_eq_coordinates]; omega
  have he : ({p,q,r} : Finset PlainExp) = plainDominantAxisRoots (p 0) (p 1) (p 2) :=
    plain_three_finset_congr hpp hqq hrr
  rw [he]
  exact plainDominantAxis_border_card _ _ _ hp.1 hp.2.1 hp.2.2

theorem plain_dominant_permuted_card (e : Equiv.Perm (Fin 3)) (p q r : PlainExp)
    (ha : PlainRootAntichain {p,q,r}) (hc : HasPlainDirectionalCentres {p,q,r})
    (hp : 0<p (e 0) ∧ 0<p (e 1) ∧ 0<p (e 2))
    (hq : 0<q (e 0) ∧ q (e 1)=0 ∧ q (e 2)=0)
    (hr : r (e 0)=0 ∧ 0<r (e 1) ∧ r (e 2)=0) :
    (plainBorderFinset {p,q,r}).card = 7 := by
  rw [← plainBorder_card_permutation e {p,q,r}]
  have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
      {plainCoordinatePerm e p,plainCoordinatePerm e q,plainCoordinatePerm e r} := by simp
  rw [hi]
  apply plain_dominant_axis_two_card
  · rw [← hi]; exact plainAntichain_coordinatePerm e {p,q,r} ha
  · rw [← hi]; exact plainCentres_coordinatePerm e {p,q,r} hc
  · simpa using hp
  · simpa using hq
  · simpa using hr

theorem plain_dominant_pure_axes_card (p q r : PlainExp)
    (hqr : q ≠ r) (ha : PlainRootAntichain {p,q,r})
    (hc : HasPlainDirectionalCentres {p,q,r})
    (hp : 0<p 0 ∧ 0<p 1 ∧ 0<p 2) (hq : plainPureAxis q) (hr : plainPureAxis r) :
    (plainBorderFinset {p,q,r}).card = 7 := by
  have hnc : ¬plainDivides q r := fun h => hqr (ha q (by simp) r (by simp) h)
  have hnc' : ¬plainDivides r q := fun h => hqr (ha r (by simp) q (by simp) h).symm
  have same (j : Fin 3) (hqz : ∀ a, a ≠ j → q a=0)
      (hrz : ∀ a, a ≠ j → r a=0) : False := by
    by_cases hle : q j ≤ r j
    · apply hnc
      intro a
      by_cases he : a=j
      · simpa [he] using hle
      · simp [hqz a he,hrz a he]
    · apply hnc'
      intro a
      by_cases he : a=j
      · simp only [he]; omega
      · simp [hqz a he,hrz a he]
  rcases hq with hq | hq | hq <;> rcases hr with hr | hr | hr
  · exfalso
    apply same 0
    all_goals intro j hj; fin_cases j <;> simp_all
  · exact plain_dominant_axis_two_card p q r ha hc hp hq hr
  · apply plain_dominant_permuted_card (Equiv.swap (1 : Fin 3) 2) p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · apply plain_dominant_permuted_card (Equiv.swap (0 : Fin 3) 1) p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · exfalso
    apply same 1
    all_goals intro j hj; fin_cases j <;> simp_all
  · apply plain_dominant_permuted_card
      ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1)) p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · apply plain_dominant_permuted_card
      ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)) p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · apply plain_dominant_permuted_card (Equiv.swap (0 : Fin 3) 2) p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · exfalso
    apply same 2
    all_goals intro j hj; fin_cases j <;> simp_all

theorem plain_triangle_pattern_card (p q r : PlainExp) (h : plainTrianglePattern p q r) :
    (plainBorderFinset {p,q,r}).card = 4 := by
  rcases h with h | h | h | h | h | h
  · have he : ({p,q,r} : Finset PlainExp) = {p,q,r} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    exact plain_ordered_triangle_card p q r h
  · have he : ({p,q,r} : Finset PlainExp) = {p,r,q} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    exact plain_ordered_triangle_card p r q h
  · have he : ({p,q,r} : Finset PlainExp) = {q,p,r} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    exact plain_ordered_triangle_card q p r h
  · have he : ({p,q,r} : Finset PlainExp) = {q,r,p} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    exact plain_ordered_triangle_card q r p h
  · have he : ({p,q,r} : Finset PlainExp) = {r,p,q} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    exact plain_ordered_triangle_card r p q h
  · have he : ({p,q,r} : Finset PlainExp) = {r,q,p} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    exact plain_ordered_triangle_card r q p h

theorem plain_plane_pattern_card (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) (ha : PlainRootAntichain {p,q,r})
    (h : plainPlaneSplitPattern p q r) : (plainBorderFinset {p,q,r}).card = 6 := by
  rcases h with h | h | h | h | h | h | h | h | h
  · have he : ({p,q,r} : Finset PlainExp) = {q,r,p} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    apply plain_plane_permuted_card (Equiv.swap (0 : Fin 3) 2) q r p hqr
    · simpa only [← he] using ha
    · simp [Equiv.swap_apply_def]
      omega
  · have he : ({p,q,r} : Finset PlainExp) = {p,r,q} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    apply plain_plane_permuted_card (Equiv.swap (0 : Fin 3) 2) p r q hpr
    · simpa only [← he] using ha
    · simp [Equiv.swap_apply_def]
      omega
  · have he : ({p,q,r} : Finset PlainExp) = {p,q,r} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    apply plain_plane_permuted_card (Equiv.swap (0 : Fin 3) 2) p q r hpq
    · simpa only [← he] using ha
    · simp [Equiv.swap_apply_def]
      omega
  · have he : ({p,q,r} : Finset PlainExp) = {q,r,p} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    apply plain_plane_permuted_card (Equiv.swap (1 : Fin 3) 2) q r p hqr
    · simpa only [← he] using ha
    · simp [Equiv.swap_apply_def]
      omega
  · have he : ({p,q,r} : Finset PlainExp) = {p,r,q} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    apply plain_plane_permuted_card (Equiv.swap (1 : Fin 3) 2) p r q hpr
    · simpa only [← he] using ha
    · simp [Equiv.swap_apply_def]
      omega
  · have he : ({p,q,r} : Finset PlainExp) = {p,q,r} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    apply plain_plane_permuted_card (Equiv.swap (1 : Fin 3) 2) p q r hpq
    · simpa only [← he] using ha
    · simp [Equiv.swap_apply_def]
      omega
  · have he : ({p,q,r} : Finset PlainExp) = {q,r,p} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    apply plain_plane_permuted_card (Equiv.refl (Fin 3)) q r p hqr
    · simpa only [← he] using ha
    · simp [Equiv.swap_apply_def]
      omega
  · have he : ({p,q,r} : Finset PlainExp) = {p,r,q} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    apply plain_plane_permuted_card (Equiv.refl (Fin 3)) p r q hpr
    · simpa only [← he] using ha
    · simp [Equiv.swap_apply_def]
      omega
  · have he : ({p,q,r} : Finset PlainExp) = {p,q,r} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    apply plain_plane_permuted_card (Equiv.refl (Fin 3)) p q r hpq
    · simpa only [← he] using ha
    · simp [Equiv.swap_apply_def]
      omega

theorem plain_dominant_pattern_card (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) (ha : PlainRootAntichain {p,q,r})
    (hc : HasPlainDirectionalCentres {p,q,r}) (h : plainDominantAxisPattern p q r) :
    (plainBorderFinset {p,q,r}).card = 7 := by
  rcases h with h | h | h
  · obtain ⟨h0,h1,h2,hb,hc'⟩ := h
    have he : ({p,q,r} : Finset PlainExp) = {p,q,r} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    exact plain_dominant_pure_axes_card p q r (hqr)
      (by simpa only [← he] using ha) (by simpa only [← he] using hc)
      ⟨h0,h1,h2⟩ hb hc'
  · obtain ⟨h0,h1,h2,hb,hc'⟩ := h
    have he : ({p,q,r} : Finset PlainExp) = {q,r,p} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    exact plain_dominant_pure_axes_card q r p (Ne.symm hpr)
      (by simpa only [← he] using ha) (by simpa only [← he] using hc)
      ⟨h0,h1,h2⟩ hb hc'
  · obtain ⟨h0,h1,h2,hb,hc'⟩ := h
    have he : ({p,q,r} : Finset PlainExp) = {r,p,q} := by ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    rw [he]
    exact plain_dominant_pure_axes_card r p q (hpq)
      (by simpa only [← he] using ha) (by simpa only [← he] using hc)
      ⟨h0,h1,h2⟩ hb hc'

/-- Corrected Run29 J: all three variables survive; no direction is vacuous. -/
theorem plain_three_root_no_five (R : Finset PlainExp) (ha : PlainRootAntichain R)
    (h3 : R.card = 3) (hv : PlainVariablesSurvive R) (hc : HasPlainDirectionalCentres R) :
    (plainBorderFinset R).card ≠ 5 := by
  obtain ⟨p,q,r,hpq,hpr,hqr,rfl⟩ := Finset.card_eq_three.mp h3
  rcases plain_three_root_coordinate_patterns p q r hpq hpr hqr ha hv hc with h | h | h
  · have hcard := plain_triangle_pattern_card p q r h
    omega
  · have hcard := plain_plane_pattern_card p q r hpq hpr hqr ha h
    omega
  · have hcard := plain_dominant_pattern_card p q r hpq hpr hqr ha hc h
    omega

end
end P23.Monomial
