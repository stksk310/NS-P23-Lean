import P23.Semigroup.LocalDominance
import P23.Semigroup.RhoFourResidualSource

namespace P23.Semigroup
noncomputable section
open P23.OneTie P23.Artin P23.Presentation

/-- The dominant root is indexed by the very tagged presentation used for degree transport. -/
structure TaggedBudgetOneDominantRoot (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  tagged : TaggedBudgetOneNormalization D i
  root : ↥tagged.presentation.roots
  dominant : IsDominantRoot tagged.presentation.roots root
  typeEq : tagged.presentation.roots.card=D.semigroupType
  kernelMuEqRho : idealGeneratorMu (finitePresentationIdeal (k:=ℚ) tagged.presentation.roots)=D.semigroupRho

theorem taggedBudgetOneDominantRoot_on (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (T : TaggedBudgetOneNormalization D i) (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupType+4≤D.semigroupRho) :
    ∃ s : ↥T.presentation.roots, IsDominantRoot T.presentation.roots s := by
  let B := T.presentation
  have he : B.roots.card=D.semigroupType :=
    (quotientType_eq_rootCard (k:=ℚ) B.roots B.roots_nonempty
      B.coordinates.liveDomain B.roots_live B.roots_antichain).symm.trans
      (B.canonicalOneTieType_eq_chosenBaseType.trans (chosenBaseType_eq_semigroupType D i))
  have hc : B.roots.card=2 ∨ B.roots.card=3 := by rwa [he]
  have hng := B.canonicalOneTie_ng_iff.mp
    (semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein D i hn)
  have hm : B.roots.card + 4 ≤ idealGeneratorMu (finitePresentationIdeal (k:=ℚ) B.roots) := by
    rwa [he,B.canonicalKernelMu_eq_rho]
  obtain ⟨s,hs,hd⟩ := oneTie_ng_kernel_mu_ge_type_plus_four_has_dominant B.roots
    B.roots_nonempty B.coordinates.liveDomain B.roots_live B.roots_antichain hc hng hm
  exact ⟨⟨s,hs⟩,hd⟩

theorem taggedBudgetOneDominantRoot (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i=1) (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupType+4≤D.semigroupRho) :
    Nonempty (TaggedBudgetOneDominantRoot D i) := by
  obtain ⟨T⟩ := taggedBudgetOneNormalization D i hB
  obtain ⟨s,hd⟩ := taggedBudgetOneDominantRoot_on D i T ht hn hr
  refine ⟨⟨T,s,hd,?_,T.presentation.canonicalKernelMu_eq_rho⟩⟩
  exact (quotientType_eq_rootCard (k:=ℚ) T.presentation.roots T.presentation.roots_nonempty
    T.presentation.coordinates.liveDomain T.presentation.roots_live T.presentation.roots_antichain).symm.trans
    (T.presentation.canonicalOneTieType_eq_chosenBaseType.trans (chosenBaseType_eq_semigroupType D i))

end
end P23.Semigroup
