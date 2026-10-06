import P23.Semigroup.AperyGenus
import P23.Semigroup.DominantAperyBase
import P23.Semigroup.GapReflection

namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup
open scoped BigOperators
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}

/-- Actual Apéry divisors, indexed by the intrinsic finite Apéry subtype. -/
def aperyDivisorFinset (B : DominantAperyBase D i) : Finset (D.AperyIndex i) := by
  classical
  exact Finset.univ.filter (fun w=>AperyDivides w B.center.1)

@[simp] theorem mem_aperyDivisorFinset (B : DominantAperyBase D i) (w : D.AperyIndex i) :
    w∈aperyDivisorFinset B ↔ AperyDivides w B.center.1 := by
  classical
  simp [aperyDivisorFinset]

theorem aperyDivisor_complement (B : DominantAperyBase D i) (w : D.AperyIndex i) :
    w∉aperyDivisorFinset B ↔ IsAperySocle w ∧ w≠B.center.1 := by
  rw [mem_aperyDivisorFinset]
  exact B.dominance w

def pfAperyPoint (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (f : D.PseudoFrobeniusIndex) : D.AperyIndex i :=
  (D.pseudoFrobeniusEquivAperySocle i f).1

theorem pfAperyPoint_injective (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :
    Function.Injective (pfAperyPoint D i) := by
  intro f g he
  apply (D.pseudoFrobeniusEquivAperySocle i).injective
  exact Subtype.ext he

theorem pfAperyPoint_degree (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (f : D.PseudoFrobeniusIndex) : (pfAperyPoint D i f).1.1=(f.1+(D.n i:ℤ)).toNat := by
  have h := aperySocle_pf_degree (D.pseudoFrobeniusEquivAperySocle i f)
  rw [Equiv.symm_apply_apply] at h
  change ((pfAperyPoint D i f).1.1:ℤ)=f.1+(D.n i:ℤ) at h
  rw [←h]
  simp

theorem pfAperyPoint_degree_int (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (f : D.PseudoFrobeniusIndex) : ((pfAperyPoint D i f).1.1:ℤ)=f.1+(D.n i:ℤ) := by
  have h := aperySocle_pf_degree (D.pseudoFrobeniusEquivAperySocle i f)
  rw [Equiv.symm_apply_apply] at h
  exact h

theorem dominant_center_pf_point (B : DominantAperyBase D i) :
    pfAperyPoint D i B.centerPF=B.center.1 := by
  apply Subtype.ext
  apply Subtype.ext
  have h := pfAperyPoint_degree_int D i B.centerPF
  have hc := B.centerDegreeEq
  exact_mod_cast h.trans hc.symm

def exceptionalAperyFinset (B : DominantAperyBase D i) : Finset (D.AperyIndex i) :=
  Finset.univ \ aperyDivisorFinset B

theorem exceptionalApery_eq_pf_image (B : DominantAperyBase D i) :
    exceptionalAperyFinset B=(Finset.univ.erase B.centerPF).image (pfAperyPoint D i) := by
  classical
  ext w
  simp only [exceptionalAperyFinset,Finset.mem_sdiff,Finset.mem_univ,true_and,
    aperyDivisor_complement,Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true]
  constructor
  · rintro ⟨hw,hn⟩
    let s : D.AperySocleIndex i := ⟨w,hw⟩
    let f := (D.pseudoFrobeniusEquivAperySocle i).symm s
    have hf : pfAperyPoint D i f=w := by
      change ((D.pseudoFrobeniusEquivAperySocle i)
        ((D.pseudoFrobeniusEquivAperySocle i).symm s)).1=w
      simp [s]
    refine ⟨f,?_,hf⟩
    intro he
    rw [he,dominant_center_pf_point B] at hf
    exact hn hf.symm
  · rintro ⟨f,hf,rfl⟩
    refine ⟨(D.pseudoFrobeniusEquivAperySocle i f).2,?_⟩
    intro he
    apply hf
    apply pfAperyPoint_injective D i
    exact he.trans (dominant_center_pf_point B).symm

theorem exceptionalApery_card (B : DominantAperyBase D i) :
    (exceptionalAperyFinset B).card=D.semigroupType-1 := by
  classical
  rw [exceptionalApery_eq_pf_image,
    Finset.card_image_of_injective _ (pfAperyPoint_injective D i)]
  simp [semigroupType]

theorem aperyDivisor_card_int (B : DominantAperyBase D i) :
    ((aperyDivisorFinset B).card:ℤ)=(D.n i:ℤ)-(D.semigroupType:ℤ)+1 := by
  classical
  have hc := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (aperyDivisorFinset B))
  change (exceptionalAperyFinset B).card+(aperyDivisorFinset B).card=
    Fintype.card (D.AperyIndex i) at hc
  rw [exceptionalApery_card] at hc
  have hq : Fintype.card (D.AperyIndex i)=D.n i := by
    simpa [Nat.card_eq_fintype_card] using aperyIndex_card D i
  rw [hq] at hc
  have ht := D.semigroupType_pos
  have hz := congrArg (fun n : ℕ=>(n:ℤ)) hc
  rw [Nat.cast_add,Int.natCast_sub (by omega)] at hz
  push_cast at hz
  omega

def dominantMultiplier (B : DominantAperyBase D i) (w : ↥(aperyDivisorFinset B)) : D.Gamma :=
  Classical.choose ((mem_aperyDivisorFinset B w.1).mp w.2)

theorem dominantMultiplier_eq (B : DominantAperyBase D i) (w : ↥(aperyDivisorFinset B)) :
    B.center.1.1=w.1.1+dominantMultiplier B w :=
  Classical.choose_spec ((mem_aperyDivisorFinset B w.1).mp w.2)

theorem dominantMultiplier_isApery (B : DominantAperyBase D i)
    (w : ↥(aperyDivisorFinset B)) : D.IsApery i (dominantMultiplier B w) := by
  rintro ⟨g,hg⟩
  apply B.center.1.2
  refine ⟨w.1.1+g,?_⟩
  rw [dominantMultiplier_eq B w,hg]
  abel

def dominantReflectionPoint (B : DominantAperyBase D i)
    (w : ↥(aperyDivisorFinset B)) : ↥(aperyDivisorFinset B) := by
  let v : D.AperyIndex i := ⟨dominantMultiplier B w,dominantMultiplier_isApery B w⟩
  refine ⟨v,(mem_aperyDivisorFinset B v).mpr ⟨w.1.1,?_⟩⟩
  exact (dominantMultiplier_eq B w).trans (add_comm _ _)

theorem dominantReflectionPoint_degree (B : DominantAperyBase D i)
    (w : ↥(aperyDivisorFinset B)) :
    B.center.1.1.1=w.1.1.1+(dominantReflectionPoint B w).1.1.1 :=
  congrArg Subtype.val (dominantMultiplier_eq B w)

theorem dominantReflectionPoint_involutive (B : DominantAperyBase D i) :
    Function.Involutive (dominantReflectionPoint B) := by
  intro w
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have h1 := dominantReflectionPoint_degree B w
  have h2 := dominantReflectionPoint_degree B (dominantReflectionPoint B w)
  omega

def dominantReflection (B : DominantAperyBase D i) :
    ↥(aperyDivisorFinset B) ≃ ↥(aperyDivisorFinset B) :=
  ⟨dominantReflectionPoint B,dominantReflectionPoint B,
    dominantReflectionPoint_involutive B,dominantReflectionPoint_involutive B⟩

theorem dominantReflection_degree (B : DominantAperyBase D i)
    (w : ↥(aperyDivisorFinset B)) :
    B.center.1.1.1=w.1.1.1+(dominantReflection B w).1.1.1 :=
  dominantReflectionPoint_degree B w

theorem dominant_divisor_sum_doubled (B : DominantAperyBase D i) :
    2*(∑ w ∈ aperyDivisorFinset B,(w.1.1:ℤ))=
      ((aperyDivisorFinset B).card:ℤ)*(B.center.1.1.1:ℤ) := by
  classical
  have hs := (dominantReflection B).sum_comp
    (fun w : ↥(aperyDivisorFinset B)=>(w.1.1.1:ℤ))
  have hp : (∑ w : ↥(aperyDivisorFinset B),
      ((w.1.1.1:ℤ)+((dominantReflection B w).1.1.1:ℤ)))=
      ((aperyDivisorFinset B).card:ℤ)*(B.center.1.1.1:ℤ) := by
    calc
      _=∑ _w : ↥(aperyDivisorFinset B),(B.center.1.1.1:ℤ) := by
        apply Finset.sum_congr rfl
        intro w _
        exact_mod_cast (dominantReflection_degree B w).symm
      _=_ := by simp
  rw [Finset.sum_add_distrib,hs] at hp
  have hc : (∑ w : ↥(aperyDivisorFinset B),(w.1.1.1:ℤ)) =
      ∑ w ∈ aperyDivisorFinset B,(w.1.1:ℤ) :=
    Finset.sum_coe_sort (aperyDivisorFinset B) (fun w : D.AperyIndex i => (w.1.1:ℤ))
  rw [hc] at hp
  nlinarith

theorem exceptional_apery_sum (B : DominantAperyBase D i) :
    (∑ w ∈ exceptionalAperyFinset B,(w.1.1:ℤ))=
      D.pseudoFrobeniusSum-B.centerPF.1+((D.semigroupType:ℤ)-1)*(D.n i:ℤ) := by
  classical
  rw [exceptionalApery_eq_pf_image,
    Finset.sum_image (pfAperyPoint_injective D i).injOn]
  simp_rw [pfAperyPoint_degree_int]
  rw [Finset.sum_add_distrib,D.pseudoFrobeniusSum_erase]
  have ht : 1≤D.semigroupType := D.semigroupType_pos
  simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ B.centerPF),
    Finset.card_univ, nsmul_eq_mul]
  change _ + ((D.semigroupType-1:ℕ):ℤ)*(D.n i:ℤ) = _
  rw [Int.natCast_sub ht]
  rfl

theorem dominant_apery_sum_formula (B : DominantAperyBase D i) :
    2*(∑ w : D.AperyIndex i,(w.1.1:ℤ))=
      ((D.n i:ℤ)-(D.semigroupType:ℤ)+1)*(B.centerPF.1+(D.n i:ℤ))+
      2*(D.pseudoFrobeniusSum-B.centerPF.1+((D.semigroupType:ℤ)-1)*(D.n i:ℤ)) := by
  classical
  have hp := Finset.sum_sdiff (f:=fun w : D.AperyIndex i=>(w.1.1:ℤ))
    (Finset.subset_univ (aperyDivisorFinset B))
  change (∑ w ∈ exceptionalAperyFinset B,(w.1.1:ℤ))+
    (∑ w ∈ aperyDivisorFinset B,(w.1.1:ℤ))=(∑ w : D.AperyIndex i,(w.1.1:ℤ)) at hp
  have hd := dominant_divisor_sum_doubled B
  rw [aperyDivisor_card_int B,B.centerDegreeEq] at hd
  rw [exceptional_apery_sum B] at hp
  nlinarith

theorem dominant_base_pivot (B : DominantAperyBase D i) :
    (D.n i:ℤ)*(2*(D.genus:ℤ)-B.centerPF.1-(D.semigroupType:ℤ))=
      2*D.pseudoFrobeniusSum-((D.semigroupType:ℤ)+1)*B.centerPF.1 := by
  have hg := D.apery_genus_formula_doubled i
  have hs := dominant_apery_sum_formula B
  nlinarith

end
end P23.Semigroup
