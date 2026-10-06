import P23.Semigroup.RhoFiveMonomialAlternative
import P23.Monomial.PlainTypeTwoBound
import P23.Monomial.PlainTypeThreeFrontier

namespace P23.Semigroup
noncomputable section
open P23.Monomial P23.Presentation

/-- Actual exponent presentation, not an arbitrary chosen root configuration. -/
structure BudgetZeroPlainModel (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  budgetZero : D.fourBaseBudget i=0
  generators : Finset PlainExp
  idealEq : plainMonomialIdeal ℚ generators=chosenBaseDefiningIdeal D i
  generatorCard : generators.card=D.semigroupRho
  minimal : HasMinimalGeneratorCard (plainMonomialIdeal ℚ generators) generators.card
  survivorsFinite : (plainSurvivors ℚ generators).Finite

theorem budgetZeroPlainModel (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (h0 : D.fourBaseBudget i=0) : Nonempty (BudgetZeroPlainModel D i) := by
  obtain ⟨G,hI,hc,hm⟩ := chosenBase_plain_exponentPresentation_of_budget_zero D i h0
  exact ⟨⟨h0,G,hI,hc,hm,chosenBase_plainSurvivors_finite D i G hI⟩⟩

namespace BudgetZeroPlainModel
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4} (M : BudgetZeroPlainModel D i)
abbrev roots := plainSurvivorRoots ℚ M.generators M.survivorsFinite
theorem roots_nonempty : M.roots.Nonempty :=
  plainSurvivorRoots_nonempty ℚ M.generators M.survivorsFinite
    (chosenBase_plain_unit_survives D i M.generators M.idealEq)
theorem roots_antichain : PlainRootAntichain M.roots :=
  plainSurvivorRoots_antichain ℚ M.generators M.survivorsFinite
theorem variables_survive : PlainVariablesSurvive M.roots :=
  chosenBase_plain_variables_survive D i M.generators M.idealEq M.survivorsFinite
theorem generators_eq_border : M.generators=plainBorderFinset M.roots :=
  plainGenerators_eq_border ℚ M.generators M.survivorsFinite
    (plainGenerators_antichain_of_minimal ℚ M.generators M.minimal)
def chosenBaseEquivPlain : ChosenBaseQuotient (k:=ℚ) D i ≃ₐ[ℚ] PlainMonomialArtin ℚ M.roots :=
  chosenBasePlainQuotientEquiv D i M.generators M.idealEq M.survivorsFinite M.generators_eq_border
theorem rootCard_eq_chosenBaseType : M.roots.card=chosenBaseType (k:=ℚ) D i :=
  (plainDirectType_eq_rootCard M.roots M.roots_nonempty M.roots_antichain).symm.trans
    (chosenPlain_type_eq M.roots M.roots_nonempty M.chosenBaseEquivPlain)
theorem rootCard_eq_semigroupType : M.roots.card=D.semigroupType :=
  M.rootCard_eq_chosenBaseType.trans (chosenBaseType_eq_semigroupType D i)
theorem borderCard_eq_rho : (plainBorderFinset M.roots).card=D.semigroupRho :=
  (congrArg Finset.card M.generators_eq_border).symm.trans M.generatorCard
theorem centres_of_ng (hcard : 2≤M.roots.card) (hn : SemigroupNearlyGorenstein D) :
    HasPlainDirectionalCentres M.roots := by
  have hng := (chosenPlain_ng_iff M.roots M.roots_nonempty M.chosenBaseEquivPlain).mp
    (semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein D i hn)
  have htrace : PlainVariablesInTrace ℚ M.roots M.variables_survive := by
    intro j
    apply hng
    apply plain_PX_mem_augmentation
    intro he
    have he' := congrArg (fun p : PlainExp => p j) he
    simpa using he'
  exact plain_hasDirectionalCentres_of_variablesInTrace M.roots M.roots_nonempty hcard
    M.roots_antichain M.variables_survive htrace
end BudgetZeroPlainModel

theorem budget_zero_type_two_mu_le_five_Q (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (h0 : D.fourBaseBudget i=0) (ht : chosenBaseType (k:=ℚ) D i=2) :
    idealGeneratorMu (chosenBaseDefiningIdeal (k:=ℚ) D i) ≤ 5 := by
  obtain ⟨M⟩ := budgetZeroPlainModel D i h0
  have h2 : M.roots.card=2 := M.rootCard_eq_chosenBaseType.trans ht
  have hb := plain_type_two_border_card_le_five M.roots M.roots_antichain h2 M.variables_survive
  rw [M.borderCard_eq_rho] at hb
  rwa [chosenBaseDefiningIdeal_mu_eq_rho]

theorem budget_zero_type_two_mu_le_five {k : Type*} [Field k]
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (h0 : D.fourBaseBudget i=0) (ht : chosenBaseType (k:=k) D i=2) :
    idealGeneratorMu (chosenBaseDefiningIdeal (k:=k) D i) ≤ 5 := by
  have htQ : chosenBaseType (k:=ℚ) D i=2 :=
    (chosenBaseType_eq_semigroupType (k:=ℚ) D i).trans
      ((chosenBaseType_eq_semigroupType (k:=k) D i).symm.trans ht)
  have hb := budget_zero_type_two_mu_le_five_Q D i h0 htQ
  rw [chosenBaseDefiningIdeal_mu_eq_rho] at hb
  rwa [chosenBaseDefiningIdeal_mu_eq_rho]

theorem budget_zero_type_two_rho_le_five (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (h0 : D.fourBaseBudget i=0) (ht : D.semigroupType=2) : D.semigroupRho≤5 := by
  have h := budget_zero_type_two_mu_le_five_Q D i h0
    ((chosenBaseType_eq_semigroupType D i).trans ht)
  rwa [chosenBaseDefiningIdeal_mu_eq_rho] at h

structure BudgetZeroTypeThreeFrontier (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  model : BudgetZeroPlainModel D i
  typeThree : model.roots.card=3
  rhoFrontier : D.semigroupRho=4 ∨ D.semigroupRho=6 ∨ D.semigroupRho=7

theorem budgetZeroTypeThreeFrontier (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (h0 : D.fourBaseBudget i=0) (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) :
    Nonempty (BudgetZeroTypeThreeFrontier D i) := by
  obtain ⟨M⟩ := budgetZeroPlainModel D i h0
  have h3 : M.roots.card=3 := M.rootCard_eq_semigroupType.trans ht
  have hc := M.centres_of_ng (by omega) hn
  have hf := plain_type_three_ng_border_frontier M.roots M.roots_antichain h3 M.variables_survive hc
  rw [M.borderCard_eq_rho] at hf
  exact ⟨⟨M,h3,hf⟩⟩

structure BudgetZeroTypeThreeSevenDominant (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  frontier : BudgetZeroTypeThreeFrontier D i
  rhoSeven : D.semigroupRho=7
  root : ↥frontier.model.roots
  dominant : PlainIsDominantRoot frontier.model.roots root

theorem budgetZeroTypeThreeSevenDominant (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (h0 : D.fourBaseBudget i=0) (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : 7≤D.semigroupRho) : Nonempty (BudgetZeroTypeThreeSevenDominant D i) := by
  obtain ⟨F⟩ := budgetZeroTypeThreeFrontier D i h0 ht hn
  have h7 : D.semigroupRho=7 := by have := F.rhoFrontier; omega
  have hc := F.model.centres_of_ng (by have := F.typeThree; omega) hn
  have hb : (plainBorderFinset F.model.roots).card=7 := F.model.borderCard_eq_rho.trans h7
  obtain ⟨s,hs,hd⟩ := plain_type_three_border_seven_has_dominant_root
    F.model.roots F.model.roots_antichain F.typeThree F.model.variables_survive hc hb
  exact ⟨⟨F,h7,⟨s,hs⟩,⟨hs,hd⟩⟩⟩

end
end P23.Semigroup
