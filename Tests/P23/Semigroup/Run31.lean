import P23.Semigroup.RhoFourSaturation

namespace P23.Semigroup
open scoped BigOperators
open P23.OneTie
variable (D : FourGeneratedNumericalSemigroup) (ht : D.semigroupType=3)
  (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho=4)

example (i : Fin 4) : D.fourBaseBudget i=1 := rho_four_all_budgets_eq_one D ht hn hr i
example : (∑ i : Fin 4,D.fourBaseBudget i)=4 := rho_four_budget_sum_eq_four D ht hn hr
example : Fintype.card D.SingletonBettiOccurrence=4 :=
  rho_four_singleton_bound_saturated D ht hn hr

example (o : D.SingletonBettiOccurrence) : D.supportCard o.degree<4 :=
  rho_four_singleton_occurrence_in_budget D ht hn hr o

example {d : ℕ} (hd : D.IsBettiDegree d) :
    (4-D.supportCard d)*(D.componentCount d-1)=D.singletonComponentCount d :=
  rho_four_local_support_equality D ht hn hr hd

example {d : ℕ} (hd : D.IsBettiDegree d) : D.componentCount d=2 :=
  rho_four_betti_two_components D ht hn hr hd

example {d : ℕ} (hd : D.IsBettiDegree d) :
    ¬∃ C E : D.BettiComponent d,
      (D.componentSupport C).card=1 ∧ (D.componentSupport E).card=3 :=
  rho_four_no_support_partition_one_plus_three D ht hn hr hd

example {d : ℕ} (hd : D.IsBettiDegree d) (C E : D.BettiComponent d) (hCE : C≠E) :
    ((D.componentSupport C).card=1 ∧ (D.componentSupport E).card=1) ∨
    ((D.componentSupport C).card=1 ∧ (D.componentSupport E).card=2) ∨
    ((D.componentSupport C).card=2 ∧ (D.componentSupport E).card=1) ∨
    ((D.componentSupport C).card=2 ∧ (D.componentSupport E).card=2) :=
  rho_four_betti_support_partition D ht hn hr hd C E hCE

example (i : Fin 4) : Nonempty (RhoFourCanonicalBaseBridge D i) :=
  rho_four_canonical_base_bridge D i ht hn hr

example (i : Fin 4) (B : RhoFourCanonicalBaseBridge D i) :
    (borderFinset B.canonical.normalization.roots).card=3 := B.borderThree

example : RhoFourStructuralReduction D := rhoFourStructuralReduction D ht hn hr

end P23.Semigroup
