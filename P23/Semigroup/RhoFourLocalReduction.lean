import P23.Semigroup.RhoFourBorderSupport
import P23.OneTie.ReorientedPureResidual

/-! Every-base local residual reduction. Source realizability is not asserted. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.OneTie P23.Presentation P23.Artin

structure RhoFourResidualPureBase (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  tagged : TaggedBudgetOneNormalization D i
  residual : ReorientedPureResidual tagged.presentation.roots
  pureTie : tagged.presentation.coordinates.c = 0
  borderThree : (borderFinset tagged.presentation.roots).card = 3
  noFullSupport : ∀ q ∈ borderFinset tagged.presentation.roots, ¬NormalHasFullSupport q
  noPureX : ∀ q ∈ borderFinset tagged.presentation.roots, ¬NormalIsPureX q

namespace RhoFourResidualPureBase
def chosenBaseEquivalence {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
    (R : RhoFourResidualPureBase D i) :
    letI : NeZero R.residual.a' := ⟨by have := R.residual.a'_ge_two; omega⟩
    ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] FinitePolynomialQuotient ℚ R.residual.roots :=
  R.tagged.presentation.chosenBaseEquivCanonicalOneTie.trans R.residual.equivalence
end RhoFourResidualPureBase

theorem rho_four_residual_pure_at_every_base (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 3) (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho = 4) :
    ∀ i, Nonempty (RhoFourResidualPureBase D i) := by
  intro i
  obtain ⟨T⟩ := taggedBudgetOneNormalization D i (rho_four_all_budgets_eq_one D ht hn hr i)
  let B := T.presentation
  let C := T.canonicalBridge ht hn
  have hcard : (borderFinset B.roots).card = 3 := by rw [B.border_card,hr]
  have hnf : ∀ q ∈ borderFinset B.roots, ¬NormalHasFullSupport q :=
    fun _ hq => T.rho_four_normalized_border_no_full_support ht hn hr hq
  have ht' : quotientType ℚ B.roots B.roots_nonempty B.coordinates.liveDomain B.roots_live = 3 := C.canonicalTypeThree
  have hn' : QuotientNearlyGorenstein ℚ B.roots B.roots_nonempty B.coordinates.liveDomain B.roots_live := C.canonicalNearlyGorenstein
  obtain ⟨R⟩ := three_border_ng_reoriented_residual B.roots B.roots_nonempty B.coordinates.liveDomain
    B.roots_live B.roots_antichain ht' hcard hnf hn'
  have hpure : B.coordinates.c = 0 := by
    by_contra hnz
    exact rho_four_mixed_canonical_impossible B.roots B.roots_nonempty B.coordinates.liveDomain
      B.roots_live B.roots_antichain (by omega) ht' hcard hnf hn'
  exact ⟨⟨T,R,hpure,hcard,hnf,
    fun _ hq => border_not_pure_x B.roots_nonempty B.roots_live hq⟩⟩

structure RhoFourLocalThreeBorderReduction (D : FourGeneratedNumericalSemigroup) where
  atBase : ∀ i, RhoFourResidualPureBase D i

theorem rho_four_local_three_border_reduction (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 3) (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho = 4) :
    Nonempty (RhoFourLocalThreeBorderReduction D) := by
  classical
  exact ⟨⟨fun i => Classical.choice (rho_four_residual_pure_at_every_base D ht hn hr i)⟩⟩
end
end P23.Semigroup
