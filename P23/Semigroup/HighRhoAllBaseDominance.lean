import P23.Semigroup.MonomialSevenExclusion
import P23.Semigroup.DominantAperyBase

namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup
open scoped BigOperators

theorem highRho_budget_positive (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) (i : Fin 4) : 0<D.fourBaseBudget i := by
  by_contra hh
  have hz : D.fourBaseBudget i=0 := by omega
  rcases ht with ht | ht
  · have hb := budget_zero_type_two_rho_le_five D i hz ht; omega
  · have hb := budget_zero_type_three_rho_le_six D i hz ht hn; omega

theorem highRho_all_budgets_eq_one (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) (i : Fin 4) : D.fourBaseBudget i=1 := by
  have h0 := highRho_budget_positive D ht hn hr 0
  have h1 := highRho_budget_positive D ht hn hr 1
  have h2 := highRho_budget_positive D ht hn hr 2
  have h3 := highRho_budget_positive D ht hn hr 3
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

theorem highRho_budget_at_least_two_impossible (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) (i : Fin 4) (hB : 2≤D.fourBaseBudget i) : False := by
  have := highRho_all_budgets_eq_one D ht hn hr i
  omega

theorem highRho_dominantAperyBase (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) (i : Fin 4) :
    Nonempty (DominantAperyBase D i) := by
  obtain ⟨B⟩ := taggedBudgetOneDominantRoot D i (highRho_all_budgets_eq_one D ht hn hr i) ht hn hr
  exact ⟨B.toDominantAperyBase⟩

/-- Local upper-side output only: all bases have actual dominant Apéry/PF centres. -/
structure HighRhoAllBaseDominance (D : FourGeneratedNumericalSemigroup) : Prop where
  allBudgetsOne : ∀ i : Fin 4,D.fourBaseBudget i=1
  allDominant : ∀ i : Fin 4,Nonempty (DominantAperyBase D i)

theorem highRho_allBaseDominance (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=2 ∨ D.semigroupType=3) (hn : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType+4≤D.semigroupRho) : HighRhoAllBaseDominance D :=
  ⟨highRho_all_budgets_eq_one D ht hn hr,highRho_dominantAperyBase D ht hn hr⟩

/-- Stable scope-explicit Run36 summary; no genus or global upper theorem. -/
structure Run36Summary (D : FourGeneratedNumericalSemigroup) : Prop where
  plainTypeThreeBound : ∀ i : Fin 4,D.fourBaseBudget i=0 → D.semigroupType=3 →
    SemigroupNearlyGorenstein D → D.semigroupRho≤6
  highRhoDominance : (D.semigroupType=2 ∨ D.semigroupType=3) →
    SemigroupNearlyGorenstein D → D.semigroupType+4≤D.semigroupRho → HighRhoAllBaseDominance D

theorem run36Summary (D : FourGeneratedNumericalSemigroup) : Run36Summary D :=
  ⟨budget_zero_type_three_rho_le_six D,highRho_allBaseDominance D⟩

end
end P23.Semigroup
