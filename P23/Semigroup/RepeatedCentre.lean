import P23.Semigroup.DominantAperyPivot
import P23.Semigroup.AlmostSymmetric

namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup
variable {D : FourGeneratedNumericalSemigroup} {i j : Fin 4}

/-- The exact pivot at two different generators cancels without division. -/
theorem repeated_dominant_pf_centre_genus
    (Bi : DominantAperyBase D i) (Bj : DominantAperyBase D j)
    (he : Bi.centerPF=Bj.centerPF) (hij : i≠j) :
    2*D.genus=D.pseudoFrobeniusNat Bi.centerPF+D.semigroupType := by
  have hi := dominant_base_pivot Bi
  have hj := dominant_base_pivot Bj
  rw [←he] at hj
  have hn : D.n i≠D.n j := fun h=>hij (D.injective h)
  have hnz : (D.n i:ℤ)≠(D.n j:ℤ) := by exact_mod_cast hn
  have hp : ((D.n i:ℤ)-(D.n j:ℤ)) *
      (2*(D.genus:ℤ)-Bi.centerPF.1-(D.semigroupType:ℤ))=0 := by nlinarith [hi,hj]
  have hc := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hnz)
  have hz : 2*(D.genus:ℤ)=Bi.centerPF.1+(D.semigroupType:ℤ) := by
    linarith
  rw [←D.pseudoFrobeniusNat_cast Bi.centerPF] at hz
  exact_mod_cast hz

theorem repeated_dominant_pf_centre_implies_almostSymmetric
    (Bi : DominantAperyBase D i) (Bj : DominantAperyBase D j)
    (he : Bi.centerPF=Bj.centerPF) (hij : i≠j) : D.IsAlmostSymmetric := by
  apply D.almostSymmetric_iff_two_genus_eq.mpr
  have hc := repeated_dominant_pf_centre_genus Bi Bj he hij
  have hf := D.pseudoFrobeniusNat_le_frobenius Bi.centerPF
  have hg := D.frobenius_type_le_two_genus
  omega

/-- Pigeonhole on the actual PF centres; NG is not an assumption here. -/
theorem four_dominant_bases_imply_almostSymmetric
    (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hall : ∀ i : Fin 4, Nonempty (DominantAperyBase D i)) : D.IsAlmostSymmetric := by
  classical
  let B (i : Fin 4) : DominantAperyBase D i := Classical.choice (hall i)
  let f : Fin 4 → D.PseudoFrobeniusIndex := fun i=>(B i).centerPF
  have hn : ¬Function.Injective f := by
    intro hi
    have hc := Fintype.card_le_of_injective f hi
    change 4≤D.semigroupType at hc
    omega
  have hp : ∃ i j : Fin 4, i≠j ∧ f i=f j := by
    by_contra h
    apply hn
    intro i j he
    by_contra hij
    exact h ⟨i,j,hij,he⟩
  obtain ⟨i,j,hij,he⟩ := hp
  exact repeated_dominant_pf_centre_implies_almostSymmetric (B i) (B j) he hij

end
end P23.Semigroup
