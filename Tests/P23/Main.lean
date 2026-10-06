import P23.Main

open P23.Semigroup

-- Downstream contract: only Main is imported; exact public hypotheses are unchanged.
example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 2) (hng : SemigroupNearlyGorenstein D)
    (hna : ¬ D.IsAlmostSymmetric) : D.semigroupRho = 4 ∨ D.semigroupRho = 5 :=
  P23.type_two_nearly_gorenstein_not_almost_symmetric D ht hng hna

example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 3) (hng : SemigroupNearlyGorenstein D)
    (hna : ¬ D.IsAlmostSymmetric) : D.semigroupRho = 6 :=
  P23.type_three_nearly_gorenstein_not_almost_symmetric D ht hng hna

example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 2 ∨ D.semigroupType = 3)
    (hng : SemigroupNearlyGorenstein D) (hr : D.semigroupType + 4 ≤ D.semigroupRho) :
    D.IsAlmostSymmetric :=
  P23.high_relation_number_forces_almost_symmetric D ht hng hr

example (D : FourGeneratedNumericalSemigroup) : P23.OriginalP23Theorem D :=
  P23.original_p23 D

example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 2 ∨ D.semigroupType = 3)
    (hng : SemigroupNearlyGorenstein D) (hna : ¬ D.IsAlmostSymmetric) :
    (D.semigroupType = 2 ∧ (D.semigroupRho = 4 ∨ D.semigroupRho = 5)) ∨
      (D.semigroupType = 3 ∧ D.semigroupRho = 6) :=
  P23.original_p23_of_type_two_or_three D ht hng hna

-- Both package fields remain directly usable without an internal theorem API.
example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 2) (hng : SemigroupNearlyGorenstein D)
    (hna : ¬ D.IsAlmostSymmetric) : D.semigroupRho = 4 ∨ D.semigroupRho = 5 :=
  (P23.original_p23 D).typeTwo ht hng hna

example (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 3) (hng : SemigroupNearlyGorenstein D)
    (hna : ¬ D.IsAlmostSymmetric) : D.semigroupRho = 6 :=
  (P23.original_p23 D).typeThree ht hng hna
