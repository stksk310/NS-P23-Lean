import P23.Semigroup.RhoFourTaggedDegree
import P23.OneTie.ThreeBorderSupport

/-! Actual rho-four normalized border support restrictions. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.OneTie P23.Presentation P23.Artin
set_option maxHeartbeats 800000
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}

namespace TaggedBudgetOneNormalization
variable (T : TaggedBudgetOneNormalization D i)

theorem normalized_external_not_full_support (ht : D.semigroupType = 3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho = 4)
    (g : D.BaseAdaptedGlobalConnector i) : ¬NormalHasFullSupport (T.normalizedOfExternal g) := by
  classical
  intro hf
  let u := T.normalizedExternalFactorization g
  let E := D.componentOf u
  have htail (j : Fin 3) : 0 < u.1 (D.tailIndex i j) := by
    change 0 < extendTailExponent i (T.externalTailExponent g) (i.succAbove j)
    rw [extendTailExponent_tail]
    change 0 < (normalExponent (T.normalizedOfExternal g)).mapDomain
      T.presentation.coordinates.sigma.symm j
    rw [Finsupp.mapDomain_equiv_apply]
    change 0 < normalExponent (T.normalizedOfExternal g) (T.presentation.coordinates.sigma j)
    generalize T.presentation.coordinates.sigma j = l
    fin_cases l
    · simpa using hf.1
    · simpa using hf.2.1
    · simpa using hf.2.2
  have hall (j : Fin 3) : D.tailIndex i j ∈ D.componentSupport E :=
    D.mem_componentSupport_iff.mpr ⟨u,rfl,htail j⟩
  have hE3 : 3 ≤ (D.componentSupport E).card := by
    have hs : Finset.univ.image (D.tailIndex i) ⊆ D.componentSupport E := by
      intro j hj
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hj
      exact hall l
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ (D.tailIndex i).injective] at hc
    simpa using hc
  have hc2 := rho_four_betti_two_components D ht hn hr g.1.2
  have hex : ∃ C : D.BettiComponent g.1.1, C ≠ E := by
    have hc : 1 < Fintype.card (D.BettiComponent g.1.1) := by
      change 1 < D.componentCount g.1.1
      omega
    obtain ⟨C,C',hne⟩ := Fintype.one_lt_card_iff.mp hc
    by_cases hC : C = E
    · exact ⟨C', fun h => hne (hC.trans h.symm)⟩
    · exact ⟨C,hC⟩
  obtain ⟨C,hCE⟩ := hex
  have hCsub : D.componentSupport C ⊆ {i} := by
    intro j hj
    apply Finset.mem_singleton.mpr
    by_contra hji
    let l := (tailIndexEquiv D i).symm ⟨j,hji⟩
    have hl : D.tailIndex i l = j := tailIndexEquiv_symm_apply D i j hji
    have hjE : j ∈ D.componentSupport E := hl ▸ hall l
    exact Finset.disjoint_left.mp (D.componentSupport_disjoint hCE) hj hjE
  have hC1 : (D.componentSupport C).card = 1 := by
    have hlo := Finset.card_pos.mpr (D.componentSupport_nonempty_of_isBetti g.1.2 C)
    have hhi := Finset.card_le_card hCsub
    simp only [Finset.card_singleton] at hhi
    omega
  have hsum : (D.componentSupport C).card + (D.componentSupport E).card ≤ 4 := by
    rw [← Finset.card_union_of_disjoint (D.componentSupport_disjoint hCE)]
    simpa using Finset.card_le_card (Finset.subset_univ
      (D.componentSupport C ∪ D.componentSupport E))
  have hE : (D.componentSupport E).card = 3 := by omega
  exact rho_four_no_support_partition_one_plus_three D ht hn hr g.1.2 ⟨C,E,hC1,hE⟩

theorem rho_four_normalized_border_no_full_support (ht : D.semigroupType = 3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho = 4)
    {q : Normal T.presentation.coordinates.a T.presentation.coordinates.b T.presentation.coordinates.c}
    (hq : q ∈ borderFinset T.presentation.roots) : ¬NormalHasFullSupport q := by
  rw [← T.external_image_exact_border] at hq
  obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hq
  exact T.normalized_external_not_full_support ht hn hr g

theorem rho_four_border_support_card_le_two (ht : D.semigroupType = 3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho = 4)
    {q : Normal T.presentation.coordinates.a T.presentation.coordinates.b T.presentation.coordinates.c}
    (hq : q ∈ borderFinset T.presentation.roots) : (normalSupport q).card ≤ 2 :=
  normalSupport_card_le_two_of_not_full q (T.rho_four_normalized_border_no_full_support ht hn hr hq)

def canonicalBridge (ht : D.semigroupType = 3) (hn : SemigroupNearlyGorenstein D) :
    ChosenBaseCanonicalOneTieBridge D i :=
  let B := T.presentation
  ⟨B,B.coordinates.liveDomain,B.roots_live,B.roots_antichain,B.roots_nonempty,
    B.chosenBaseEquivCanonicalOneTie,
    B.canonicalOneTieType_eq_chosenBaseType.trans ((chosenBaseType_eq_semigroupType D i).trans ht),
    B.canonicalOneTie_ng_iff.mp (semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein D i hn),
    B.canonicalKernelMu_eq_rho,B.border_card⟩
end TaggedBudgetOneNormalization

structure RhoFourThreeBorderLocalReduction (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  tagged : TaggedBudgetOneNormalization D i
  canonical : ChosenBaseCanonicalOneTieBridge D i
  sameNormalization : canonical.normalization = tagged.presentation
  borderThree : (borderFinset tagged.presentation.roots).card = 3
  supportAtMostTwo : ∀ q ∈ borderFinset tagged.presentation.roots, (normalSupport q).card ≤ 2
  noPureX : ∀ q ∈ borderFinset tagged.presentation.roots, ¬NormalIsPureX q

abbrev RhoFourTaggedCanonicalBaseBridge := RhoFourThreeBorderLocalReduction

theorem rho_four_three_border_local_reduction (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (ht : D.semigroupType = 3) (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho = 4) :
    Nonempty (RhoFourThreeBorderLocalReduction D i) := by
  obtain ⟨T⟩ := taggedBudgetOneNormalization D i (rho_four_all_budgets_eq_one D ht hn hr i)
  refine ⟨⟨T,T.canonicalBridge ht hn,rfl,?_,?_,?_⟩⟩
  · rw [T.presentation.border_card,hr]
  · exact fun _ hq => T.rho_four_border_support_card_le_two ht hn hr hq
  · exact fun _ hq => border_not_pure_x T.presentation.roots_nonempty T.presentation.roots_live hq
end
end P23.Semigroup
