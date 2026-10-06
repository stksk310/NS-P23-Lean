import P23.Semigroup.RepeatedCentre
open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup
#check repeated_dominant_pf_centre_genus
#check repeated_dominant_pf_centre_implies_almostSymmetric
#check four_dominant_bases_imply_almostSymmetric

variable {D : FourGeneratedNumericalSemigroup} {i j : Fin 4}
example (Bi : DominantAperyBase D i) (Bj : DominantAperyBase D j)
    (he : Bi.centerPF=Bj.centerPF) (hij : i≠j) : D.IsAlmostSymmetric :=
  repeated_dominant_pf_centre_implies_almostSymmetric Bi Bj he hij
example (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hall : ∀ i : Fin 4, Nonempty (DominantAperyBase D i)) : D.IsAlmostSymmetric :=
  four_dominant_bases_imply_almostSymmetric ht hall
