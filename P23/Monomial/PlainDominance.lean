import P23.Monomial.PlainNoFive

namespace P23.Monomial
noncomputable section

/-- Every nonsocle standard monomial lies below this selected root. -/
def PlainIsDominantRoot (R : Finset PlainExp) (s : PlainExp) : Prop :=
  s ∈ R ∧ ∀ p, p ∈ plainStandardSet R → p ∉ R → plainDivides p s

theorem plain_dominant_of_all_centres (R : Finset PlainExp) (s : PlainExp)
    (hs : s ∈ R) (hc : ∀ j, PlainDirectionalCentre R j s) :
    PlainIsDominantRoot R s := by
  refine ⟨hs, ?_⟩
  rintro p ⟨r, hr, hpr⟩ hpn
  have hne : p ≠ r := by intro he; exact hpn (he ▸ hr)
  have hex : ∃ j, p j < r j := by
    by_contra hn
    push_neg at hn
    apply hne
    ext j
    exact le_antisymm (hpr j) (hn j)
  obtain ⟨j,hj⟩ := hex
  apply plainDivides_trans (q := plainPredecessor j r)
  · intro i
    by_cases hi : j=i
    · subst i; simp only [plainPredecessor_apply,ite_true]; omega
    · simpa [plainPredecessor_apply,hi] using hpr i
  · exact (hc j).2 r hr (by omega)

theorem plain_dominant_coordinatePerm (e : Equiv.Perm (Fin 3))
    (R : Finset PlainExp) (s : PlainExp) (h : PlainIsDominantRoot R s) :
    PlainIsDominantRoot (R.image (plainCoordinatePerm e)) (plainCoordinatePerm e s) := by
  refine ⟨Finset.mem_image.mpr ⟨s,h.1,rfl⟩,?_⟩
  intro p hp hn
  let q := (plainCoordinatePerm e).symm p
  have hq : plainCoordinatePerm e q = p := (plainCoordinatePerm e).apply_symm_apply p
  have hqs := (plainStandard_coordinatePerm_iff e R q).mp (hq.symm ▸ hp)
  have hqn : q ∉ R := by
    intro hqr
    exact hn (Finset.mem_image.mpr ⟨q,hqr,hq⟩)
  have hd := (plainDivides_coordinatePerm_iff e q s).mpr (h.2 q hqs hqn)
  simpa [hq] using hd

set_option maxHeartbeats 1600000 in
theorem plain_positive_two_axes_dominant (p q r : PlainExp)
    (hc : HasPlainDirectionalCentres {p,q,r})
    (hp : 0<p 0 ∧ 0<p 1 ∧ 0<p 2)
    (hq : plainPureAxis q) (hr : plainPureAxis r) :
    PlainIsDominantRoot {p,q,r} p := by
  apply plain_dominant_of_all_centres _ p (by simp)
  intro j
  obtain ⟨s,hs⟩ := hc j
  have hd := hs.2 p (by simp) (by fin_cases j <;> simp_all)
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have hm := hs.1
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with he | he | he
  · simpa [he] using hs
  · subst s
    rcases hq with hq | hq | hq <;> fin_cases j <;>
      simp [plainPredecessor_apply] at h0 h1 h2 <;> omega
  · subst s
    rcases hr with hr | hr | hr <;> fin_cases j <;>
      simp [plainPredecessor_apply] at h0 h1 h2 <;> omega

theorem plain_dominant_axis_pattern_has_dominant (p q r : PlainExp)
    (hc : HasPlainDirectionalCentres {p,q,r}) (h : plainDominantAxisPattern p q r) :
    ∃ s, PlainIsDominantRoot {p,q,r} s := by
  rcases h with h | h | h
  · exact ⟨p,plain_positive_two_axes_dominant p q r hc ⟨h.1,h.2.1,h.2.2.1⟩
      h.2.2.2.1 h.2.2.2.2⟩
  · have he : ({p,q,r} : Finset PlainExp) = {q,r,p} := by ext s; simp; tauto
    rw [he] at hc ⊢
    exact ⟨q,plain_positive_two_axes_dominant q r p hc ⟨h.1,h.2.1,h.2.2.1⟩
      h.2.2.2.1 h.2.2.2.2⟩
  · have he : ({p,q,r} : Finset PlainExp) = {r,p,q} := by ext s; simp; tauto
    rw [he] at hc ⊢
    exact ⟨r,plain_positive_two_axes_dominant r p q hc ⟨h.1,h.2.1,h.2.2.1⟩
      h.2.2.2.1 h.2.2.2.2⟩

end
end P23.Monomial
