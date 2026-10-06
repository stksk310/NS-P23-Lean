import P23.Semigroup.RhoFourSaturation

/-! Actual external connector tags retained through one-tie normalization.
Normalization is not assumed to preserve support. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.OneTie P23.Presentation P23.Artin
open scoped BigOperators
set_option maxHeartbeats 800000

variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}

structure TaggedBudgetOneNormalization (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  internalTag : D.BaseAdaptedGlobalConnector i
  internal : D.IsInternalBaseConnector i internalTag
  uniqueInternal : ∀ g, D.IsInternalBaseConnector i g → g = internalTag
  presentation : BudgetOneNormalizedPresentation D i
  live_eq : presentation.live = D.specializedConnectorPolynomial i internalTag
  raw_eq : presentation.rawExponents = (D.externalBaseConnectorFinset i).image
    (fun g => (D.connectorRightTail i g).mapDomain presentation.coordinates.sigma)
  budget : D.fourBaseBudget i = 1

namespace TaggedBudgetOneNormalization
variable (T : TaggedBudgetOneNormalization D i)
abbrev externalTags (_T : TaggedBudgetOneNormalization D i) := D.externalBaseConnectorFinset i
def rawOfExternal (g : D.BaseAdaptedGlobalConnector i) : Fin 3 →₀ ℕ :=
  (D.connectorRightTail i g).mapDomain T.presentation.coordinates.sigma
def normalizedOfExternal (g : D.BaseAdaptedGlobalConnector i) :
    Normal T.presentation.coordinates.a T.presentation.coordinates.b T.presentation.coordinates.c :=
  normalizeExponent _ _ _ (T.rawOfExternal g)

theorem external_card : T.externalTags.card = D.semigroupRho - 1 := by
  rw [externalBaseConnectorFinset_card, T.budget]

theorem raw_external_injective : Set.InjOn T.rawOfExternal T.externalTags := by
  intro g hg h hh he
  have hg' : i ∈ D.combinedSupport g.1.1 := by
    simpa [externalBaseConnectorFinset, IsInternalBaseConnector] using hg
  have hh' : i ∈ D.combinedSupport h.1.1 := by
    simpa [externalBaseConnectorFinset, IsInternalBaseConnector] using hh
  have hw : D.connectorRightTail i g = D.connectorRightTail i h :=
    Finsupp.mapDomain_injective T.presentation.coordinates.sigma.injective he
  apply specializedConnectorPolynomial_injective (k := ℚ) D i
  rw [D.specializedConnectorPolynomial_external i g hg',
    D.specializedConnectorPolynomial_external i h hh', hw]

theorem normalized_external_injective : Set.InjOn T.normalizedOfExternal T.externalTags := by
  intro g hg h hh he
  apply T.raw_external_injective hg hh
  apply T.presentation.normalization_injective
  · rw [T.raw_eq]; exact Finset.mem_image.mpr ⟨g,hg,rfl⟩
  · rw [T.raw_eq]; exact Finset.mem_image.mpr ⟨h,hh,rfl⟩
  · exact he

theorem external_image_exact_border :
    T.externalTags.image T.normalizedOfExternal = borderFinset T.presentation.roots := by
  rw [← T.presentation.generators_exact_border]
  change _ = T.presentation.rawExponents.image (normalizeExponent _ _ _)
  rw [T.raw_eq, Finset.image_image]
  rfl
end TaggedBudgetOneNormalization

theorem taggedBudgetOneNormalization (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 1) : Nonempty (TaggedBudgetOneNormalization D i) := by
  classical
  obtain ⟨g,hg,hu⟩ := D.existsUnique_internal_connector_of_budget_one i hB
  let p : TailPoly ℚ := D.specializedConnectorPolynomial i g
  obtain ⟨L⟩ := liveTailTieData_exists D i p
    (D.specializedConnector_isLiveBinomial_of_base_not_mem_support i g hg)
  obtain ⟨C⟩ := oneTieCoordinates_exists L
  let E := (D.externalBaseConnectorFinset i).image
    (fun h => (D.connectorRightTail i h).mapDomain C.sigma)
  have hEinj : Set.InjOn (fun h => (D.connectorRightTail i h).mapDomain C.sigma)
      (D.externalBaseConnectorFinset i) := by
    intro h hh j hj he
    have hh' : i ∈ D.combinedSupport h.1.1 := by
      simpa [externalBaseConnectorFinset, IsInternalBaseConnector] using hh
    have hj' : i ∈ D.combinedSupport j.1.1 := by
      simpa [externalBaseConnectorFinset, IsInternalBaseConnector] using hj
    have hw := Finsupp.mapDomain_injective C.sigma.injective he
    apply specializedConnectorPolynomial_injective (k := ℚ) D i
    rw [D.specializedConnectorPolynomial_external i h hh',
      D.specializedConnectorPolynomial_external i j hj', hw]
  have hcard : E.card = D.semigroupRho - 1 := by
    rw [Finset.card_image_iff.mpr hEinj, D.externalBaseConnectorFinset_card i, hB]
  have hspan : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) =
      renamedChosenBaseIdeal C := by
    let R := Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ))
    have he (h : D.BaseAdaptedGlobalConnector i) : renameToOneTie C
        (-MvPolynomial.monomial (D.connectorRightTail i h) 1) =
        -MvPolynomial.monomial ((D.connectorRightTail i h).mapDomain C.sigma) 1 := by
      simp [renameToOneTie, MvPolynomial.rename_monomial]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro q hq
      rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        apply tiePolynomial_mem_renamedChosenBaseIdeal C
        rw [D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i]
        exact Ideal.subset_span ⟨g,rfl⟩
      · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hd
        have hh' : i ∈ D.combinedSupport h.1.1 := by
          simpa [externalBaseConnectorFinset, IsInternalBaseConnector] using hh
        have hm : D.specializedConnectorPolynomial (k := ℚ) i h ∈ chosenBaseDefiningIdeal D i := by
          rw [D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i]
          exact Ideal.subset_span ⟨h,rfl⟩
        have hi := Ideal.mem_map_of_mem (renameToOneTie C).toRingHom hm
        change renameToOneTie C (D.specializedConnectorPolynomial i h) ∈ renamedChosenBaseIdeal C at hi
        rw [D.specializedConnectorPolynomial_external i h hh', he] at hi
        change MvPolynomial.monomial ((D.connectorRightTail i h).mapDomain C.sigma) 1 ∈
          renamedChosenBaseIdeal C
        simpa only [neg_neg] using neg_mem hi
    · change (chosenBaseDefiningIdeal D i).map (renameToOneTie C).toRingHom ≤ R
      rw [D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i, Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro q ⟨q',⟨h,rfl⟩,rfl⟩
      change renameToOneTie C (D.specializedConnectorPolynomial i h) ∈ R
      by_cases hh : D.IsInternalBaseConnector i h
      · rw [hu h hh]
        change renameToOneTie C p ∈ R
        have ht : tiePolynomial C.a C.b C.c ∈ R :=
          Ideal.subset_span (Finset.mem_insert_self _ _)
        rcases renameToOneTie_live C with ht' | ht'
        · rwa [ht']
        · rw [ht']; exact neg_mem ht
      · have hd : (D.connectorRightTail i h).mapDomain C.sigma ∈ E :=
          Finset.mem_image.mpr ⟨h, by simp [externalBaseConnectorFinset, hh], rfl⟩
        have hm : MvPolynomial.monomial ((D.connectorRightTail i h).mapDomain C.sigma) 1 ∈ R :=
          Ideal.subset_span (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_,hd,rfl⟩))
        rw [D.specializedConnectorPolynomial_external i h (not_not.mp hh), he]
        exact neg_mem hm
  have hpos : 0 < D.semigroupRho := by
    have hle : (D.internalBaseConnectorFinset i).card ≤ Fintype.card (D.BaseAdaptedGlobalConnector i) :=
      Finset.card_le_univ _
    rw [D.internalBaseConnectorFinset_card i, hB, D.baseAdaptedGlobalConnector_card_eq_rho i] at hle
    omega
  letI := chosenBase_normal_survivorQuotient_finite C E hspan
  let B : BudgetOneNormalizedPresentation D i :=
    ⟨p,C,E,hspan,hcard,hpos,normal_survivors_finite _⟩
  exact ⟨⟨g,hg,hu,B,rfl,rfl,hB⟩⟩
end
end P23.Semigroup
