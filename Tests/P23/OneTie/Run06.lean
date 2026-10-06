import P23.OneTie.Phase1GeometryClosure

namespace P23.OneTie

#check topDeletionMixedBelow_border_exact
#check topDeletionMixedBelow_border_card
#check topDeletionMixedLast_border_exact
#check topDeletionMixedLast_border_card
#check topDeletionPure_border_exact
#check topDeletionPure_border_card
#check typeThreeTopDeletion_border_card
#check topDeletion_border_card_ne_four
#check pureFibreProduct_border_exact
#check pureFibreProduct_border_card
#check pureFibreProduct_border_card_ne_four
#check pureFibreProductShape_border_exact
#check pureFibreProductShape_border_card
#check borderFinset_swapYZ_card
#check borderFinset_swapYZ_exact
#check mixed_four_border_has_dominant
#check pure_four_border_dominant_or_residual
#check phaseOne_four_border_geometry

/-! Mixed top deletion below the last layer, at the load-bearing `r = a-2`
endpoint. -/
example (S : Finset (Normal 4 1 1)) (hS : S.Nonempty)
    (hstd : standardSet S =
      Normal.divisorDownset (mixedCore (a := 4) (b := 1) (c := 1)
        2 1 1 (by omega)) \
      {mixedCore (a := 4) (b := 1) (c := 1) 2 1 1 (by omega)}) :
    (borderFinset S).card = 5 := by
  exact topDeletionMixedBelow_border_card S (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hS hstd

/-! Mixed top deletion on the last x-layer. -/
example (S : Finset (Normal 3 1 1)) (hS : S.Nonempty)
    (hstd : standardSet S =
      Normal.divisorDownset (mixedCore (a := 3) (b := 1) (c := 1)
        2 1 1 (by omega)) \
      {mixedCore (a := 3) (b := 1) (c := 1) 2 1 1 (by omega)}) :
    (borderFinset S).card = 3 := by
  exact topDeletionMixedLast_border_card S (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hS hstd

/-! Pure top deletion, including its last-layer wrapped endpoint. -/
example (S : Finset (Normal 4 2 0)) (hS : S.Nonempty)
    (hstd : standardSet S =
      Normal.divisorDownset (pureCore (a := 4) (b := 2) 3 2 1 (by omega)) \
      {pureCore (a := 4) (b := 2) 3 2 1 (by omega)}) :
    (borderFinset S).card = 3 := by
  exact topDeletionPure_border_card S (by omega) (by omega) (by omega)
    (by omega) (by omega) hS hstd

/-! Direct pure fibre-product count with the endpoint `k = 1`. -/
example :
    (borderFinset (pureFibreProductSocles (a := 3) (b := 2)
      0 2 1 1 1 (by omega) (by omega))).card = 5 := by
  exact pureFibreProduct_border_card (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-! The same direct count for the nonprimitive pure tie `(a,b) = (4,2)`. -/
example :
    (borderFinset (pureFibreProductSocles (a := 4) (b := 2)
      0 2 1 1 2 (by omega) (by omega))).card = 5 := by
  exact pureFibreProduct_border_card (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-! Run-04 load-bearing row endpoints used by elimination. -/
example : (borderFinset (m2KSocles (a := 4) (by omega) 2 1 1 (by omega))).card = 3 := by
  rw [m2K_border_card (a := 4) (by omega) (by omega) (by omega) (by omega)]
  simp

example : (borderFinset (m5YSocles (a := 3) (b := 2) (c := 1)
    (by omega) 1)).card = 3 := by
  simpa using m5Y_border_card (a := 3) (b := 2) (c := 1)
    (by omega) (by omega) (by omega) (by omega)

/-! Reflection transports the actual parameter type and exact border card. -/
example :
    (borderFinset (swapYZFinset
      (m2ZSocles (a := 4) (by omega) 1 1 2 (by omega)))).card =
    (borderFinset (m2ZSocles (a := 4) (by omega) 1 1 2 (by omega))).card := by
  exact borderFinset_swapYZ_card _

/-! The two pure residual four-border rows. -/
example : (borderFinset (p4ZSocles (a := 3) (b := 2) (by omega) 1)).card = 4 := by
  exact p4Z_border_card (by omega) (by omega) (by omega)

example : (borderFinset (p5ZSocles (a := 3) (b := 2) (by omega) 1)).card = 4 := by
  exact p5Z_border_card (by omega) (by omega) (by omega)

/-! Concrete-parameter instances of the two Phase-1 closure APIs. -/
example (S : Finset (Normal 3 1 1))
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (hcentres : HasDirectionalCentres S)
    (hborder : (borderFinset S).card = 4) :
    ∃ C ∈ S, IsDominantRoot S C := by
  exact mixed_four_border_has_dominant S (by omega) (by omega) (by omega)
    hcard hlive hanti hcentres hborder

example (S : Finset (Normal 3 2 0))
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (hcentres : HasDirectionalCentres S)
    (hborder : (borderFinset S).card = 4) :
    (∃ C ∈ S, IsDominantRoot S C) ∨ IsPureResidualFourBorderShape S := by
  exact pure_four_border_dominant_or_residual S (by omega) (by omega)
    hcard hlive hanti hcentres hborder

end P23.OneTie
