import P23.Semigroup.LocalDominance
import P23.Semigroup.PlainLocalFrontier

/-! Stable Run35 per-base API. Budget at least two is deliberately unresolved. -/
namespace P23.Semigroup
noncomputable section

inductive HighRhoChosenBaseLocalAlternative (D : FourGeneratedNumericalSemigroup) (i : Fin 4) : Prop
  | budgetOneDominant (h : Nonempty (BudgetOneDominantCanonicalRoot D i))
  | budgetZeroTypeThreeSevenDominant (h : Nonempty (BudgetZeroTypeThreeSevenDominant D i))
  | budgetAtLeastTwo (h : 2≤D.fourBaseBudget i)

theorem highRhoChosenBaseLocalAlternative (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) : HighRhoChosenBaseLocalAlternative D i := by
  by_cases h0 : D.fourBaseBudget i=0
  · rcases ht with ht | ht
    · have hb := budget_zero_type_two_rho_le_five D i h0 ht
      omega
    · apply HighRhoChosenBaseLocalAlternative.budgetZeroTypeThreeSevenDominant
      exact budgetZeroTypeThreeSevenDominant D i h0 ht hn (by omega)
  · by_cases h1 : D.fourBaseBudget i=1
    · exact .budgetOneDominant (budgetOneDominantCanonicalRoot D i h1 ht hn hr)
    · exact .budgetAtLeastTwo (by omega)

structure Run35LocalAsForcingSummary (D : FourGeneratedNumericalSemigroup) : Prop where
  typeTwoBudgetZero : ∀ i, D.fourBaseBudget i=0 → D.semigroupType=2 → D.semigroupRho≤5
  typeThreeBudgetZero : ∀ i, D.fourBaseBudget i=0 → D.semigroupType=3 →
    SemigroupNearlyGorenstein D → Nonempty (BudgetZeroTypeThreeFrontier D i)
  highRhoAlternative : ∀ i, (D.semigroupType=2 ∨ D.semigroupType=3) →
    SemigroupNearlyGorenstein D → D.semigroupType+4≤D.semigroupRho →
    HighRhoChosenBaseLocalAlternative D i

theorem run35LocalAsForcingSummary (D : FourGeneratedNumericalSemigroup) :
    Run35LocalAsForcingSummary D where
  typeTwoBudgetZero := budget_zero_type_two_rho_le_five D
  typeThreeBudgetZero := budgetZeroTypeThreeFrontier D
  highRhoAlternative := highRhoChosenBaseLocalAlternative D

end
end P23.Semigroup
