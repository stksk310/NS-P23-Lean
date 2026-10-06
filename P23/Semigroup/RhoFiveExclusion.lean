import P23.Semigroup.RhoFiveMonomialAlternative
import P23.Semigroup.ChosenBaseCanonicalQuotient
import P23.Presentation.HL5Quotient

/-! Exact rho-five exclusion by composition of frozen Runs19,28,29.
No new geometry, trace, minimality or rho-four argument is introduced.
The semigroup NG hypothesis retains the frozen PF NG-vector scope. -/
namespace P23.Semigroup
noncomputable section
open P23.OneTie P23.Artin P23.Presentation

/-- Unified live-domain wrapper around the two frozen quotient H-L5 APIs. -/
theorem canonicalQuotient_HL5_border_ne_four_of_liveDomain
    {a b c : ℕ} [NeZero a] (S : Finset (Normal a b c))
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S)
    (htype : quotientType ℚ S (nonempty_of_isLiveTie S hlive) hdom hlive = 3)
    (hng : QuotientNearlyGorenstein ℚ S
      (nonempty_of_isLiveTie S hlive) hdom hlive) :
    (borderFinset S).card ≠ 4 := by
  rcases hdom with ⟨ha, hbc⟩
  rcases hbc with ⟨hb,hc⟩ | ⟨hb,hc⟩
  · exact mixed_quotient_HL5_border_ne_four
      (k := ℚ) S ha hb hc hlive hanti htype hng
  · subst c
    exact pure_quotient_HL5_border_ne_four
      (k := ℚ) S ha hb hlive hanti htype hng

/-- H-L5 consumes only the intrinsic canonical fields, not its border count. -/
theorem chosenBaseCanonicalOneTie_HL5_border_ne_four
    {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
    (B : ChosenBaseCanonicalOneTieBridge D i) :
    (borderFinset B.normalization.roots).card ≠ 4 :=
  canonicalQuotient_HL5_border_ne_four_of_liveDomain B.normalization.roots
    B.liveDomain B.liveTie B.rootAntichain
    B.canonicalTypeThree B.canonicalNearlyGorenstein

/-- The independent frozen border-count field gives four under rho five. -/
theorem chosenBaseCanonicalOneTie_border_card_eq_four_of_rho_five
    {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
    (B : ChosenBaseCanonicalOneTieBridge D i) (hr : D.semigroupRho = 5) :
    (borderFinset B.normalization.roots).card = 4 := by
  rw [B.borderCardEqRhoSubOne,hr]

/-- A single budget-one base gives the required border-form contradiction. -/
theorem budget_one_type_three_ng_rho_ne_five
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 1) (ht : D.semigroupType = 3)
    (hng : SemigroupNearlyGorenstein D) : D.semigroupRho ≠ 5 := by
  intro hr
  obtain ⟨B⟩ := chosenBaseCanonicalOneTieBridge D i hB ht hng
  exact chosenBaseCanonicalOneTie_HL5_border_ne_four B
    (chosenBaseCanonicalOneTie_border_card_eq_four_of_rho_five B hr)

/-- Exact bounded exclusion; this is not the full type-three lower bound. -/
theorem type_three_ng_semigroupRho_ne_five
    (D : FourGeneratedNumericalSemigroup) (ht : D.semigroupType = 3)
    (hng : SemigroupNearlyGorenstein D) : D.semigroupRho ≠ 5 := by
  intro hr
  have hB : D.fourBaseBudget 0 = 1 := rho_five_all_budgets_eq_one D ht hng hr 0
  exact budget_one_type_three_ng_rho_ne_five D 0 hB ht hng hr

/-- Stable assembly boundary, without rho-four or lower-bound conclusions. -/
structure RhoFiveExclusion (D : FourGeneratedNumericalSemigroup) : Prop where
  allBudgetsOne : D.semigroupRho = 5 → ∀ i, D.fourBaseBudget i = 1
  normalizesBudgetOne : ∀ i, D.fourBaseBudget i = 1 →
    Nonempty (ChosenBaseCanonicalOneTieBridge D i)
  canonicalBorderNotFour : ∀ i (B : ChosenBaseCanonicalOneTieBridge D i),
    (borderFinset B.normalization.roots).card ≠ 4
  rhoFiveBorderFour : ∀ i (B : ChosenBaseCanonicalOneTieBridge D i),
    D.semigroupRho = 5 → (borderFinset B.normalization.roots).card = 4
  rhoNeFive : D.semigroupRho ≠ 5

theorem rhoFiveExclusion (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 3) (hng : SemigroupNearlyGorenstein D) :
    RhoFiveExclusion D where
  allBudgetsOne := fun hr i => rho_five_all_budgets_eq_one D ht hng hr i
  normalizesBudgetOne := fun i hB => chosenBaseCanonicalOneTieBridge D i hB ht hng
  canonicalBorderNotFour := fun _ B => chosenBaseCanonicalOneTie_HL5_border_ne_four B
  rhoFiveBorderFour := fun _ B hr => chosenBaseCanonicalOneTie_border_card_eq_four_of_rho_five B hr
  rhoNeFive := type_three_ng_semigroupRho_ne_five D ht hng

end
end P23.Semigroup
