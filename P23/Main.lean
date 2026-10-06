import P23.Semigroup.OriginalBranches

/-!
# Original P23: stable final theorem surface

The original P23 branch theorem is Lean-certified under the project's
formal PF NG-vector predicate `SemigroupNearlyGorenstein`.

This module only assembles frozen high-level theorems. It does not claim
formalization of the equivalence with the one-dimensional semigroup-ring
trace definition, the independent almost-symmetric rho <= 7 theorem, or
the derived global e = 4 nearly-Gorenstein rho <= 7 corollary.
-/

namespace P23

open P23.Semigroup

/-- At type two or three, PF-NG and rho >= type + 4 force almost symmetry. -/
theorem high_relation_number_forces_almost_symmetric
    (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 2 ∨ D.semigroupType = 3)
    (hng : SemigroupNearlyGorenstein D)
    (hr : D.semigroupType + 4 ≤ D.semigroupRho) : D.IsAlmostSymmetric :=
  P23.Semigroup.highRho_implies_almostSymmetric D ht hng hr

/-- Original type-two branch, under the formal project PF-NG predicate. -/
theorem type_two_nearly_gorenstein_not_almost_symmetric
    (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 2) (hng : SemigroupNearlyGorenstein D)
    (hna : ¬ D.IsAlmostSymmetric) : D.semigroupRho = 4 ∨ D.semigroupRho = 5 :=
  P23.Semigroup.type_two_ng_notAS_rho_eq_four_or_five D ht hng hna

/-- Original type-three branch, under the formal project PF-NG predicate. -/
theorem type_three_nearly_gorenstein_not_almost_symmetric
    (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 3) (hng : SemigroupNearlyGorenstein D)
    (hna : ¬ D.IsAlmostSymmetric) : D.semigroupRho = 6 :=
  P23.Semigroup.type_three_ng_notAS_rho_eq_six D ht hng hna

/-- Both original P23 branches with their exact hypotheses accessible separately. -/
structure OriginalP23Theorem (D : FourGeneratedNumericalSemigroup) : Prop where
  typeTwo : D.semigroupType = 2 → SemigroupNearlyGorenstein D →
    ¬ D.IsAlmostSymmetric → D.semigroupRho = 4 ∨ D.semigroupRho = 5
  typeThree : D.semigroupType = 3 → SemigroupNearlyGorenstein D →
    ¬ D.IsAlmostSymmetric → D.semigroupRho = 6

/-- Final original P23 theorem package; no external semantic equivalence is assumed. -/
theorem original_p23 (D : FourGeneratedNumericalSemigroup) : OriginalP23Theorem D :=
  ⟨type_two_nearly_gorenstein_not_almost_symmetric D,
    type_three_nearly_gorenstein_not_almost_symmetric D⟩

/-- A downstream case-split form of the two original branches. -/
theorem original_p23_of_type_two_or_three
    (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 2 ∨ D.semigroupType = 3)
    (hng : SemigroupNearlyGorenstein D) (hna : ¬ D.IsAlmostSymmetric) :
    (D.semigroupType = 2 ∧ (D.semigroupRho = 4 ∨ D.semigroupRho = 5)) ∨
      (D.semigroupType = 3 ∧ D.semigroupRho = 6) := by
  rcases ht with ht | ht
  · exact Or.inl ⟨ht, type_two_nearly_gorenstein_not_almost_symmetric D ht hng hna⟩
  · exact Or.inr ⟨ht, type_three_nearly_gorenstein_not_almost_symmetric D ht hng hna⟩

end P23
