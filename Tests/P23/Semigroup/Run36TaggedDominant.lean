import P23.Semigroup.TaggedDominantBase
#check P23.Semigroup.TaggedBudgetOneDominantRoot
#check P23.Semigroup.taggedBudgetOneDominantRoot

open P23.Semigroup P23.OneTie
example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (T : TaggedBudgetOneNormalization D i) (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupType+4≤D.semigroupRho) :
    ∃ s : ↥T.presentation.roots,IsDominantRoot T.presentation.roots s :=
  taggedBudgetOneDominantRoot_on D i T ht hn hr
