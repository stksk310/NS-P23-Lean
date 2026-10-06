import P23.Semigroup.BettiFibers
import P23.Semigroup.FourBaseBudget

/-!
# Run 23 regression

This file begins as the RED import test. Focused theorem and concrete
regressions are added as the production API is implemented.
-/

open P23.Semigroup

#check FourGeneratedNumericalSemigroup.FactorizationAt
#check FourGeneratedNumericalSemigroup.factorizationGraph
#check FourGeneratedNumericalSemigroup.localSupportInequality
#check FourGeneratedNumericalSemigroup.singletonComponent_degree_unique
#check FourGeneratedNumericalSemigroup.fourBaseBudget_sum_le_four
#check FourGeneratedNumericalSemigroup.factorizationGraph_adj
#check FourGeneratedNumericalSemigroup.componentSupport_disjoint
#check FourGeneratedNumericalSemigroup.factorization_eq_single_of_singleton_component
#check FourGeneratedNumericalSemigroup.singletonBettiOccurrence_card_le_four
#check FourGeneratedNumericalSemigroup.fourBaseBudget_doubleCount
#check FourGeneratedNumericalSemigroup.connectorCount
#check FourGeneratedNumericalSemigroup.componentConnectorGraph_connected
#check FourGeneratedNumericalSemigroup.fourBaseBettiCombinatorics

-- Explanatory regression for the seven support partitions in the human proof.
example : (4 - 2) * (2 - 1) ≤ 2 := by omega -- 1+1
example : (4 - 3) * (2 - 1) ≤ 1 := by omega -- 1+2
example : (4 - 4) * (2 - 1) ≤ 1 := by omega -- 1+3
example : (4 - 4) * (2 - 1) ≤ 0 := by omega -- 2+2
example : (4 - 3) * (3 - 1) ≤ 3 := by omega -- 1+1+1
example : (4 - 4) * (3 - 1) ≤ 2 := by omega -- 1+1+2
example : (4 - 4) * (4 - 1) ≤ 4 := by omega -- 1+1+1+1
