import P23.Semigroup.RhoFourMonomialBase
import P23.Semigroup.ChosenBaseCanonicalQuotient

/-! Rho-four support saturation and actual every-base canonical packages.
This layer does not exclude rho four or classify normalized three borders. -/
namespace P23.Semigroup
noncomputable section
open scoped BigOperators
open FourGeneratedNumericalSemigroup P23.OneTie

variable (D : FourGeneratedNumericalSemigroup)
  (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho=4)
include ht hn hr

theorem rho_four_all_budgets_eq_one (i : Fin 4) : D.fourBaseBudget i=1 := by
  have h0 := Nat.pos_of_ne_zero (rho_four_budget_zero_impossible D 0 ht hn hr)
  have h1 := Nat.pos_of_ne_zero (rho_four_budget_zero_impossible D 1 ht hn hr)
  have h2 := Nat.pos_of_ne_zero (rho_four_budget_zero_impossible D 2 ht hn hr)
  have h3 := Nat.pos_of_ne_zero (rho_four_budget_zero_impossible D 3 ht hn hr)
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

theorem rho_four_budget_sum_eq_four : (∑ i : Fin 4,D.fourBaseBudget i)=4 := by
  simp [rho_four_all_budgets_eq_one D ht hn hr]

theorem rho_four_budget_singleton_sum_eq_four :
    (∑ d : D.BudgetDegree,D.singletonComponentCount d.1)=4 := by
  have hs := rho_four_budget_sum_eq_four D ht hn hr
  rw [D.fourBaseBudget_doubleCount] at hs
  have hle : (∑ d : D.BudgetDegree,(4-D.supportCard d.1)*D.bettiContribution d.1) ≤
      ∑ d : D.BudgetDegree,D.singletonComponentCount d.1 := by
    apply Finset.sum_le_sum
    intro d _
    exact D.localSupportInequality d.2.1
  have hupper := D.budget_singleton_sum_le_four
  omega

theorem rho_four_singleton_bound_saturated : Fintype.card D.SingletonBettiOccurrence=4 := by
  have hb : Fintype.card D.BudgetSingletonOccurrence=4 :=
    D.budgetSingletonOccurrence_card_eq_sum.trans (rho_four_budget_singleton_sum_eq_four D ht hn hr)
  have hle := Fintype.card_le_of_injective D.budgetSingletonToOccurrence
    D.budgetSingletonToOccurrence_injective
  have hu := D.singletonBettiOccurrence_card_le_four
  omega

theorem rho_four_budget_singletons_exhaust_all :
    Function.Surjective D.budgetSingletonToOccurrence := by
  have hb : Fintype.card D.BudgetSingletonOccurrence=4 :=
    D.budgetSingletonOccurrence_card_eq_sum.trans (rho_four_budget_singleton_sum_eq_four D ht hn hr)
  have ha := rho_four_singleton_bound_saturated D ht hn hr
  exact ((Fintype.bijective_iff_injective_and_card D.budgetSingletonToOccurrence).mpr
    ⟨D.budgetSingletonToOccurrence_injective,hb.trans ha.symm⟩).2

theorem rho_four_singleton_occurrence_in_budget (o : D.SingletonBettiOccurrence) :
    D.supportCard o.degree<4 := by
  obtain ⟨b,he⟩ := rho_four_budget_singletons_exhaust_all D ht hn hr o
  have hd : b.1.1=o.degree := congrArg SingletonBettiOccurrence.degree he
  have hb := b.1.2.2
  rwa [hd] at hb

private theorem rho_four_budget_degree_local_equality (d : D.BudgetDegree) :
    (4-D.supportCard d.1)*(D.componentCount d.1-1)=D.singletonComponentCount d.1 := by
  classical
  have hle := D.localSupportInequality d.2.1
  by_contra hne
  have hstrict : (4-D.supportCard d.1)*(D.componentCount d.1-1)<
      D.singletonComponentCount d.1 := by omega
  have hslt : (∑ x : D.BudgetDegree,(4-D.supportCard x.1)*D.bettiContribution x.1)<
      ∑ x : D.BudgetDegree,D.singletonComponentCount x.1 := by
    apply Finset.sum_lt_sum
    · intro x _
      exact D.localSupportInequality x.2.1
    · exact ⟨d,Finset.mem_univ d,hstrict⟩
  have hs := rho_four_budget_sum_eq_four D ht hn hr
  rw [D.fourBaseBudget_doubleCount] at hs
  have he := rho_four_budget_singleton_sum_eq_four D ht hn hr
  omega

theorem rho_four_local_support_equality {d : ℕ} (hd : D.IsBettiDegree d) :
    (4-D.supportCard d)*(D.componentCount d-1)=D.singletonComponentCount d := by
  classical
  by_cases hv : D.supportCard d<4
  · exact rho_four_budget_degree_local_equality D ht hn hr ⟨d,hd,hv⟩
  · have hv4 : D.supportCard d=4 := by have := D.supportCard_le_four d; omega
    have hell : D.singletonComponentCount d=0 := by
      unfold singletonComponentCount
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro C _ hC
      exact hv (rho_four_singleton_occurrence_in_budget D ht hn hr ⟨d,hd,C,hC⟩)
    rw [hv4,hell]
    simp

theorem rho_four_betti_two_components {d : ℕ} (hd : D.IsBettiDegree d) :
    D.componentCount d=2 := by
  have hc2 : 2≤D.componentCount d := hd
  have hcv := D.componentCount_le_supportCard_of_isBetti hd
  have hv4 := D.supportCard_le_four d
  have htwice := D.twice_componentCount_le_supportCard_add_singletons hd
  have he := rho_four_local_support_equality D ht hn hr hd
  rw [←he] at htwice
  interval_cases hv : D.supportCard d <;> omega

omit ht hn hr in
private theorem component_support_card_pair_le_four {d : ℕ}
    (C E : D.BettiComponent d) (hCE : C≠E) :
    (D.componentSupport C).card+(D.componentSupport E).card≤4 := by
  classical
  have hsub : D.componentSupport C∪D.componentSupport E ⊆ D.combinedSupport d :=
    Finset.union_subset (D.componentSupport_subset_combinedSupport C)
      (D.componentSupport_subset_combinedSupport E)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (D.componentSupport_disjoint hCE)] at hcard
  exact hcard.trans (D.supportCard_le_four d)

theorem rho_four_no_support_partition_one_plus_three {d : ℕ} (hd : D.IsBettiDegree d) :
    ¬∃ C E : D.BettiComponent d,
      (D.componentSupport C).card=1 ∧ (D.componentSupport E).card=3 := by
  classical
  rintro ⟨C,E,hC,hE⟩
  have hCE : C≠E := by intro h; subst E; omega
  have hsub : D.componentSupport C∪D.componentSupport E ⊆ D.combinedSupport d :=
    Finset.union_subset (D.componentSupport_subset_combinedSupport C)
      (D.componentSupport_subset_combinedSupport E)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (D.componentSupport_disjoint hCE),hC,hE] at hcard
  have hv : D.supportCard d=4 := by
    have hu := D.supportCard_le_four d
    change 1+3≤D.supportCard d at hcard
    omega
  have hlocal := rho_four_local_support_equality D ht hn hr hd
  have hell : 0<D.singletonComponentCount d := by
    unfold singletonComponentCount
    apply Finset.card_pos.mpr
    exact ⟨C,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hC⟩⟩
  rw [hv] at hlocal
  omega

theorem rho_four_no_three_or_four_component_betti_degree {d : ℕ}
    (hd : D.IsBettiDegree d) : D.componentCount d≠3 ∧ D.componentCount d≠4 := by
  have := rho_four_betti_two_components D ht hn hr hd
  omega

theorem rho_four_betti_support_partition {d : ℕ} (hd : D.IsBettiDegree d)
    (C E : D.BettiComponent d) (hCE : C≠E) :
    ((D.componentSupport C).card=1 ∧ (D.componentSupport E).card=1) ∨
    ((D.componentSupport C).card=1 ∧ (D.componentSupport E).card=2) ∨
    ((D.componentSupport C).card=2 ∧ (D.componentSupport E).card=1) ∨
    ((D.componentSupport C).card=2 ∧ (D.componentSupport E).card=2) := by
  have hC := Finset.card_pos.mpr (D.componentSupport_nonempty_of_isBetti hd C)
  have hE := Finset.card_pos.mpr (D.componentSupport_nonempty_of_isBetti hd E)
  have hpair := component_support_card_pair_le_four D C E hCE
  have hno := rho_four_no_support_partition_one_plus_three D ht hn hr hd
  have hnoCE : ¬((D.componentSupport C).card=1 ∧ (D.componentSupport E).card=3) :=
    fun h => hno ⟨C,E,h⟩
  have hnoEC : ¬((D.componentSupport E).card=1 ∧ (D.componentSupport C).card=3) :=
    fun h => hno ⟨E,C,h⟩
  omega

structure RhoFourCanonicalBaseBridge (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  canonical : ChosenBaseCanonicalOneTieBridge D i
  borderThree : (borderFinset canonical.normalization.roots).card=3

omit ht hn hr in
theorem rho_four_canonical_base_bridge (i : Fin 4)
    (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho=4) :
    Nonempty (RhoFourCanonicalBaseBridge D i) := by
  obtain ⟨B⟩ := chosenBaseCanonicalOneTieBridge D i
    (rho_four_all_budgets_eq_one D ht hn hr i) ht hn
  refine ⟨⟨B,?_⟩⟩
  rw [B.borderCardEqRhoSubOne,hr]

structure RhoFourStructuralReduction (D : FourGeneratedNumericalSemigroup) : Prop where
  sourcePatterns : ∀ i, ∀ P : TailSocleTopPattern D i, Nonempty (TwoTailSources D i)
  noMonomialBase : ∀ i, D.fourBaseBudget i≠0
  budgetsOne : ∀ i, D.fourBaseBudget i=1
  budgetSum : (∑ i : Fin 4,D.fourBaseBudget i)=4
  singletonSaturation : Fintype.card D.SingletonBettiOccurrence=4
  allSingletonsInBudget : ∀ o : D.SingletonBettiOccurrence, D.supportCard o.degree<4
  localEquality : ∀ d, D.IsBettiDegree d →
    (4-D.supportCard d)*(D.componentCount d-1)=D.singletonComponentCount d
  twoComponents : ∀ d, D.IsBettiDegree d → D.componentCount d=2
  noOnePlusThree : ∀ d, D.IsBettiDegree d → ¬∃ C E : D.BettiComponent d,
    (D.componentSupport C).card=1 ∧ (D.componentSupport E).card=3
  canonicalAtEveryBase : ∀ i, Nonempty (RhoFourCanonicalBaseBridge D i)

theorem rhoFourStructuralReduction : RhoFourStructuralReduction D where
  sourcePatterns := fun i P => exists_two_tail_sources D i P hn
  noMonomialBase := fun i => rho_four_budget_zero_impossible D i ht hn hr
  budgetsOne := rho_four_all_budgets_eq_one D ht hn hr
  budgetSum := rho_four_budget_sum_eq_four D ht hn hr
  singletonSaturation := rho_four_singleton_bound_saturated D ht hn hr
  allSingletonsInBudget := rho_four_singleton_occurrence_in_budget D ht hn hr
  localEquality := fun _ hd => rho_four_local_support_equality D ht hn hr hd
  twoComponents := fun _ hd => rho_four_betti_two_components D ht hn hr hd
  noOnePlusThree := fun _ hd => rho_four_no_support_partition_one_plus_three D ht hn hr hd
  canonicalAtEveryBase := fun i => rho_four_canonical_base_bridge D i ht hn hr

end
end P23.Semigroup
