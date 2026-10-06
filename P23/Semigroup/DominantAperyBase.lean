import P23.Semigroup.TaggedDominantBase

namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.OneTie P23.Artin P23.Presentation
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}

def AperyDivides (w s : D.AperyIndex i) : Prop := ∃ g : D.Gamma,s.1=w.1+g

def IsAperySocle (w : D.AperyIndex i) : Prop :=
  ∀ j : Fin 3, ¬D.IsApery i (w.1+D.tail i j)

theorem aperySocle_pf_degree (s : D.AperySocleIndex i) :
    (s.1.1.1:ℤ)=((D.pseudoFrobeniusEquivAperySocle i).symm s).1+(D.n i:ℤ) := by
  change (s.1.1.1:ℤ)=((s.1.1.1:ℤ)-(D.n i:ℤ))+(D.n i:ℤ)
  ring

/-- An actual Apéry socle is maximal for actual semigroup divisibility. -/
theorem aperySocle_divides_iff_eq (w : D.AperyIndex i) (hw : IsAperySocle w)
    (s : D.AperyIndex i) : AperyDivides w s ↔ w=s := by
  constructor
  · rintro ⟨g,hg⟩
    by_cases hz : g=0
    · apply Subtype.ext; simpa [hz] using hg.symm
    let f := (D.pseudoFrobeniusEquivAperySocle i).symm ⟨w,hw⟩
    obtain ⟨v,hv⟩ := f.2.2 g hz
    have hf := aperySocle_pf_degree (D:=D) (i:=i) ⟨w,hw⟩
    have hg' := congrArg (fun x : D.Gamma => (x.1:ℤ)) hg
    have hnot := s.2
    exfalso
    apply hnot
    refine ⟨v,Subtype.ext ?_⟩
    change s.1.1=D.n i+v.1
    simp only [AddSubmonoid.coe_add] at hg'
    change (w.1.1:ℤ)=f.1+(D.n i:ℤ) at hf
    omega
  · rintro rfl
    exact ⟨0,by simp⟩

theorem canonicalRoot_mul_not_standard (T : TaggedBudgetOneNormalization D i)
    (s : ↥T.presentation.roots) (j : Fin 3) :
    s.1*coordinateGenerator j∉standardSet T.presentation.roots := by
  rintro ⟨t,ht,hd⟩
  have hsdiv : s.1∣t := dvd_trans ⟨coordinateGenerator j,rfl⟩ hd
  have he : t=s.1 := by
    by_contra hn
    exact T.presentation.roots_antichain s.1 s.2 t ht (Ne.symm hn) hsdiv
  subst t
  obtain ⟨r,hr⟩ := hd
  have hdeg := congrArg (canonicalDegree T) hr
  rw [canonicalDegree_mul,canonicalDegree_mul,canonicalDegree_coordinateGenerator] at hdeg
  have hp := D.tailGen_positive i (T.presentation.coordinates.sigma.symm j)
  omega

def canonicalRootAperySocleIndex (T : TaggedBudgetOneNormalization D i)
    (s : ↥T.presentation.roots) : D.AperySocleIndex i := by
  let w : D.AperyIndex i := ⟨tailDegreeGamma D i (canonicalTailExponent T s.1),
    (chosenBase_canonical_isApery_iff_standard T s.1).mpr ⟨s.1,s.2,dvd_refl _⟩⟩
  refine ⟨w,?_⟩
  intro j hj
  have he : tailDegreeGamma D i (canonicalTailExponent T
      (s.1*coordinateGenerator (T.presentation.coordinates.sigma j)))=w.1+D.tail i j := by
    apply Subtype.ext
    change canonicalDegree T (s.1*coordinateGenerator (T.presentation.coordinates.sigma j))=
      canonicalDegree T s.1+D.tailGen i j
    rw [canonicalDegree_mul,canonicalDegree_coordinateGenerator]
    simp
  have hs := (chosenBase_canonical_isApery_iff_standard T
    (s.1*coordinateGenerator (T.presentation.coordinates.sigma j))).mp (he.symm ▸ hj)
  exact canonicalRoot_mul_not_standard T s _ hs

@[simp] theorem canonicalRootAperySocleIndex_degree (T : TaggedBudgetOneNormalization D i)
    (s : ↥T.presentation.roots) :
    (canonicalRootAperySocleIndex T s).1.1.1=canonicalDegree T s.1 := rfl

def canonicalRootPF (T : TaggedBudgetOneNormalization D i) (s : ↥T.presentation.roots) :
    D.PseudoFrobeniusIndex :=
  (D.pseudoFrobeniusEquivAperySocle i).symm (canonicalRootAperySocleIndex T s)

theorem canonicalRootPF_degree (T : TaggedBudgetOneNormalization D i)
    (s : ↥T.presentation.roots) :
    (canonicalDegree T s.1:ℤ)=(canonicalRootPF T s).1+(D.n i:ℤ) :=
  aperySocle_pf_degree (canonicalRootAperySocleIndex T s)

theorem canonicalAperyRepresentative_exists (T : TaggedBudgetOneNormalization D i)
    (w : D.AperyIndex i) :
    ∃ p, p∈standardSet T.presentation.roots ∧ canonicalDegree T p=w.1.1 := by
  obtain ⟨u,hu⟩ := exists_tailExponent_of_isApery D i w.2
  refine ⟨canonicalSourceNormal T u,?_,(canonicalSourceNormal_degree T u).trans hu⟩
  apply (chosenBase_canonical_isApery_iff_standard T _).mp
  have he : tailDegreeGamma D i (canonicalTailExponent T (canonicalSourceNormal T u))=w.1 :=
    Subtype.ext ((canonicalSourceNormal_degree T u).trans hu)
  rw [he]
  exact w.2

def canonicalAperyRepresentative (T : TaggedBudgetOneNormalization D i)
    (w : D.AperyIndex i) :
    {p : Normal T.presentation.coordinates.a T.presentation.coordinates.b T.presentation.coordinates.c //
      p∈standardSet T.presentation.roots} :=
  ⟨(canonicalAperyRepresentative_exists T w).choose,
    (canonicalAperyRepresentative_exists T w).choose_spec.1⟩

theorem canonicalAperyRepresentative_degree (T : TaggedBudgetOneNormalization D i)
    (w : D.AperyIndex i) : canonicalDegree T (canonicalAperyRepresentative T w).1=w.1.1 :=
  (canonicalAperyRepresentative_exists T w).choose_spec.2

theorem canonical_divides_implies_semigroup_divides (T : TaggedBudgetOneNormalization D i)
    (p s : Normal T.presentation.coordinates.a T.presentation.coordinates.b T.presentation.coordinates.c)
    (hd : p∣s) : ∃ g : D.Gamma,canonicalDegree T s=canonicalDegree T p+g.1 := by
  obtain ⟨r,rfl⟩ := hd
  exact ⟨tailDegreeGamma D i (canonicalTailExponent T r),canonicalDegree_mul T p r⟩

theorem canonical_dominant_actual_decomposition (T : TaggedBudgetOneNormalization D i)
    (s : ↥T.presentation.roots) (hd : IsDominantRoot T.presentation.roots s.1)
    (w : D.AperyIndex i) :
    ¬AperyDivides w (canonicalRootAperySocleIndex T s).1 ↔
      IsAperySocle w ∧ w≠(canonicalRootAperySocleIndex T s).1 := by
  classical
  constructor
  · intro hn
    constructor
    · by_contra hw
      let p := canonicalAperyRepresentative T w
      have hpr : p.1∉T.presentation.roots := by
        intro hp
        have hs := (canonicalRootAperySocleIndex T ⟨p.1,hp⟩).2
        have he : (canonicalRootAperySocleIndex T ⟨p.1,hp⟩).1=w := by
          apply Subtype.ext; apply Subtype.ext
          exact canonicalAperyRepresentative_degree T w
        exact hw (he ▸ hs)
      have hdiv : p.1∣s.1 := by
        have hp : p.1∈Normal.divisorDownset s.1 ∪
            (↑(T.presentation.roots.erase s.1) : Set _) :=
          Eq.mp (congrArg (fun U : Set _ => p.1∈U) hd.2) p.2
        rcases hp with hp | hp
        · exact hp
        · exact False.elim (hpr (Finset.mem_of_mem_erase hp))
      obtain ⟨g,hg⟩ := canonical_divides_implies_semigroup_divides T p.1 s.1 hdiv
      apply hn
      refine ⟨g,Subtype.ext ?_⟩
      change canonicalDegree T s.1=w.1.1+g.1
      rwa [canonicalAperyRepresentative_degree T w] at hg
    · intro he
      apply hn
      exact (aperySocle_divides_iff_eq w (he.symm ▸ (canonicalRootAperySocleIndex T s).2) _).mpr he
  · rintro ⟨hw,hne⟩ hdiv
    exact hne ((aperySocle_divides_iff_eq w hw _).mp hdiv)

structure DominantAperyBase (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  tagged : TaggedBudgetOneNormalization D i
  canonicalRoot : ↥tagged.presentation.roots
  canonicalDominant : IsDominantRoot tagged.presentation.roots canonicalRoot.1
  center : D.AperySocleIndex i
  center_eq : center=canonicalRootAperySocleIndex tagged canonicalRoot
  centerPF : D.PseudoFrobeniusIndex
  centerDegreeEq : (center.1.1.1:ℤ)=centerPF.1+(D.n i:ℤ)
  dominance : ∀ w : D.AperyIndex i,¬AperyDivides w center.1 ↔ IsAperySocle w ∧ w≠center.1

def TaggedBudgetOneDominantRoot.toDominantAperyBase (B : TaggedBudgetOneDominantRoot D i) :
    DominantAperyBase D i where
  tagged := B.tagged
  canonicalRoot := B.root
  canonicalDominant := B.dominant
  center := canonicalRootAperySocleIndex B.tagged B.root
  center_eq := rfl
  centerPF := canonicalRootPF B.tagged B.root
  centerDegreeEq := canonicalRootPF_degree B.tagged B.root
  dominance := canonical_dominant_actual_decomposition B.tagged B.root B.dominant

end
end P23.Semigroup
