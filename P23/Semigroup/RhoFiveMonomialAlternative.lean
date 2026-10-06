import P23.Semigroup.ChosenBasePlainTrace
import P23.Monomial.PlainHV

/-! Budget-zero monomial obstruction. These conclusions do not exclude rho=5:
they say that, under rho=5, all four chosen-base budgets equal one. -/
namespace P23.Semigroup
noncomputable section
open P23.Monomial P23.Presentation

theorem chosenBase_budget_zero_type_three_ng_mu_ne_five
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hz : D.fourBaseBudget i=0) (ht : chosenBaseType (k := ℚ) D i=3)
    (hn : ChosenBaseNearlyGorenstein (k := ℚ) D i) :
    idealGeneratorMu (chosenBaseDefiningIdeal (k := ℚ) D i) ≠ 5 := by
  obtain ⟨G,hI,hcard,hm⟩ := chosenBase_plain_exponentPresentation_of_budget_zero D i hz
  have hf := chosenBase_plainSurvivors_finite D i G hI
  have h0 := chosenBase_plain_unit_survives D i G hI
  let R := plainSurvivorRoots ℚ G hf
  have hR : R.Nonempty := plainSurvivorRoots_nonempty ℚ G hf h0
  have ha : PlainRootAntichain R := plainSurvivorRoots_antichain ℚ G hf
  have hG := plainGenerators_eq_border ℚ G hf (plainGenerators_antichain_of_minimal ℚ G hm)
  let E := chosenBasePlainQuotientEquiv D i G hI hf hG
  have hv : PlainVariablesSurvive R := chosenBase_plain_variables_survive D i G hI hf
  have hed : plainEmbeddingDimension ℚ R hR=3 :=
    (plain_embeddingDimension_eq_three_iff_variablesSurvive R hR).mpr hv
  have htype : plainDirectType ℚ R hR=3 :=
    (chosenPlain_type_eq R hR E).trans ht
  have hng : PlainDirectNearlyGorenstein ℚ R hR :=
    (chosenPlain_ng_iff R hR E).mp hn
  have hno := plainMonomial_typeThree_nearlyGorenstein_mu_ne_five G hf h0 hm hed htype hng
  rwa [hI] at hno

theorem budget_zero_type_three_ng_rho_ne_five
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hz : D.fourBaseBudget i=0) (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) : D.semigroupRho ≠ 5 := by
  have h := chosenBase_budget_zero_type_three_ng_mu_ne_five D i hz
    ((chosenBaseType_eq_semigroupType D i).trans ht)
    (semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein D i hn)
  rwa [chosenBaseDefiningIdeal_mu_eq_rho] at h

theorem rho_five_budget_positive (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupRho=5) (i : Fin 4) : 0<D.fourBaseBudget i := by
  by_contra h
  have hz : D.fourBaseBudget i=0 := by omega
  exact budget_zero_type_three_ng_rho_ne_five D i hz ht hn hr

theorem rho_five_all_budgets_eq_one (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupRho=5) (i : Fin 4) : D.fourBaseBudget i=1 := by
  have h0 := rho_five_budget_positive D ht hn hr 0
  have h1 := rho_five_budget_positive D ht hn hr 1
  have h2 := rho_five_budget_positive D ht hn hr 2
  have h3 := rho_five_budget_positive D ht hn hr 3
  have hs := D.fourBaseBudget_sum_le_four
  rw [Fin.sum_univ_four] at hs
  have he0 : D.fourBaseBudget 0=1 := by omega
  have he1 : D.fourBaseBudget 1=1 := by omega
  have he2 : D.fourBaseBudget 2=1 := by omega
  have he3 : D.fourBaseBudget 3=1 := by omega
  fin_cases i
  · exact he0
  · exact he1
  · exact he2
  · exact he3

/-- Scope-explicit output package: no rho exclusion, AS or Main conclusion. -/
structure MonomialFiveGeneratorObstruction (D : FourGeneratedNumericalSemigroup) : Prop where
  budgetZeroNotFive : ∀ i, D.fourBaseBudget i=0 → D.semigroupRho ≠ 5
  rhoFivePositive : D.semigroupRho=5 → ∀ i, 0<D.fourBaseBudget i
  rhoFiveAllOne : D.semigroupRho=5 → ∀ i, D.fourBaseBudget i=1

theorem monomialFiveGeneratorObstruction (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) :
    MonomialFiveGeneratorObstruction D where
  budgetZeroNotFive := fun i hz => budget_zero_type_three_ng_rho_ne_five D i hz ht hn
  rhoFivePositive := fun hr i => rho_five_budget_positive D ht hn hr i
  rhoFiveAllOne := fun hr i => rho_five_all_budgets_eq_one D ht hn hr i

end
end P23.Semigroup
