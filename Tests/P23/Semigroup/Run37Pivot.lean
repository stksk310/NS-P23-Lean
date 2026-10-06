import P23.Semigroup.DominantAperyPivot
open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup
#check aperyDivisorFinset
#check aperyDivisor_complement
#check dominantReflection
#check dominantReflection_degree
#check dominant_divisor_sum_doubled
#check exceptional_apery_sum
#check dominant_apery_sum_formula
#check dominant_base_pivot

variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
example (B : DominantAperyBase D i) :
    (D.n i:ℤ)*(2*(D.genus:ℤ)-B.centerPF.1-(D.semigroupType:ℤ)) =
      2*D.pseudoFrobeniusSum-((D.semigroupType:ℤ)+1)*B.centerPF.1 :=
  dominant_base_pivot B
example (B : DominantAperyBase D i) (w : ↥(aperyDivisorFinset B)) :
    dominantReflection B (dominantReflection B w)=w :=
  (dominantReflection B).left_inv w
