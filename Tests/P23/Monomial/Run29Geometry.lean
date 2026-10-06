import P23.Monomial.PlainGeometry
open P23.Monomial

-- Detects lost downward closure and unguarded/truncated predecessor equations.
example (R : Finset PlainExp) (p q : PlainExp) (hq : q ∈ plainStandardSet R)
    (hpq : plainDivides p q) : p ∈ plainStandardSet R :=
  plainStandard_downward R hq hpq

example (p : PlainExp) (j : Fin 3) (h : 0 < p j) :
    plainPredecessor j p + plainUnitVector j = p :=
  plainPredecessor_add_unitVector j p h

example (R : Finset PlainExp) (p : PlainExp) :
    p ∈ plainBorderFinset R ↔ ¬p ∈ plainStandardSet R ∧
      ∀ j : Fin 3, 0 < p j → plainPredecessor j p ∈ plainStandardSet R :=
  mem_plainBorderFinset_iff R p

example (R : Finset PlainExp) (h : PlainVariablesSurvive R) (j : Fin 3) :
    ∃ s ∈ R, 0 < s j := plain_direction_active R h j
