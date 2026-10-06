import P23.Semigroup.DominantAperyBase
noncomputable section
#check P23.Semigroup.canonicalRootAperySocleIndex
#check P23.Semigroup.canonicalAperyRepresentative
#check P23.Semigroup.DominantAperyBase

open P23.Semigroup P23.OneTie
example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (T : TaggedBudgetOneNormalization D i) (s : ↥T.presentation.roots) :
    D.AperySocleIndex i := canonicalRootAperySocleIndex T s

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (T : TaggedBudgetOneNormalization D i) (s : ↥T.presentation.roots) :
    (canonicalDegree T s.1:ℤ)=(canonicalRootPF T s).1+(D.n i:ℤ) := canonicalRootPF_degree T s

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (T : TaggedBudgetOneNormalization D i) (w : D.AperyIndex i) :
    canonicalDegree T (canonicalAperyRepresentative T w).1=w.1.1 :=
  canonicalAperyRepresentative_degree T w

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (T : TaggedBudgetOneNormalization D i)
    (p s : Normal T.presentation.coordinates.a T.presentation.coordinates.b T.presentation.coordinates.c)
    (hd : p∣s) : ∃ g : D.Gamma,canonicalDegree T s=canonicalDegree T p+g.1 :=
  canonical_divides_implies_semigroup_divides T p s hd

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (T : TaggedBudgetOneNormalization D i) (s : ↥T.presentation.roots)
    (hd : IsDominantRoot T.presentation.roots s.1) (w : D.AperyIndex i) :
    ¬AperyDivides w (canonicalRootAperySocleIndex T s).1 ↔
      IsAperySocle w ∧ w≠(canonicalRootAperySocleIndex T s).1 :=
  canonical_dominant_actual_decomposition T s hd w
