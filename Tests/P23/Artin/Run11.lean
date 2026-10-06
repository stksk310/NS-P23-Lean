import P23.OneTie.DominantLastLayer
import P23.OneTie.DominantReduction
import P23.Artin.HL5Direct

/-!
# Run 11 regression: arbitrary dominant reduction and direct-model H-L5

The declarations checked here are load-bearing symbolic APIs.  Concrete
endpoint examples are added beside each implementation layer.
-/

open P23 OneTie

#check P23.OneTie.mixedDominantLast_border_exact
#check P23.OneTie.mixedDominantLast_border_card
#check P23.OneTie.pureDominantSoclesLastCore
#check P23.OneTie.pureDominantBorder_lastCore_exact
#check P23.OneTie.pureDominantBorder_lastCore_card
#check P23.OneTie.pureDominantBorder_lastCore_card_ne_four

#check P23.OneTie.dominant_extra_root_mem_principalBorder
#check P23.OneTie.dominant_erase_card_eq_two
#check P23.OneTie.mixed_dominant_tie_mem_core
#check P23.OneTie.mixed_dominant_four_border_survivor
#check P23.OneTie.pure_dominant_three_branch_reduction
#check P23.OneTie.pure_dominant_border_card_ne_four_general

#check P23.Artin.mixed_dominant_four_border_not_variablesInTrace
#check P23.Artin.mixed_directModel_HL5
#check P23.Artin.pure_directModel_HL5
#check P23.Artin.directModel_HL5

namespace P23.Run11Regression

open P23.OneTie

/-! Endpoint and nonprimitive checks for the new last-layer families. -/

example :
    (borderFinset
      (mixedDominantSoclesLast (a := 2) (b := 1) (c := 1) 1 1)).card = 6 := by
  simpa using mixedDominantLast_border_card
    (a := 2) (b := 1) (c := 1) (u := 1) (v := 1) (by omega) (by omega)
      (by omega) (by omega) (by omega)

example :
    (borderFinset
      (mixedDominantSoclesLast (a := 4) (b := 2) (c := 3) 2 3)).card = 6 := by
  simpa using mixedDominantLast_border_card
    (a := 4) (b := 2) (c := 3) (u := 2) (v := 3) (by omega) (by omega)
      (by omega) (by omega) (by omega)

example :
    (borderFinset
      (pureDominantSoclesLastCore (a := 2) (b := 2) 2 0)).card = 5 := by
  simpa using pureDominantBorder_lastCore_card
    (a := 2) (b := 2) (u := 2) (v := 0) (by omega) (by omega) (by omega)

example :
    (borderFinset
      (pureDominantSoclesLastCore (a := 2) (b := 2) 3 1)).card = 6 := by
  simpa using pureDominantBorder_lastCore_card
    (a := 2) (b := 2) (u := 3) (v := 1) (by omega) (by omega) (by omega)

example :
    (borderFinset
      (pureDominantSoclesLastCore (a := 4) (b := 3) 4 1)).card = 6 := by
  simpa using pureDominantBorder_lastCore_card
    (a := 4) (b := 3) (u := 4) (v := 1) (by omega) (by omega) (by omega)

/-! Concrete below-last survivor/card checks, including rejection of YP. -/

example :
    (borderFinset
      (mixedSoclesYZ (a := 2) (b := 1) (c := 1) 0 1 1 (by omega))).card = 4 := by
  simpa [indicator] using mixedBorderYZ_card
    (a := 2) (b := 1) (c := 1) (r := 0) (u := 1) (v := 1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset
      (mixedSoclesYQ (a := 3) (b := 2) (c := 1) 0 2 1 (by omega))).card = 4 := by
  simpa [indicator] using mixedBorderYQ_card
    (a := 3) (b := 2) (c := 1) (r := 0) (u := 2) (v := 1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset
      (mixedSoclesZP (a := 3) (b := 1) (c := 2) 0 1 2 (by omega))).card = 4 := by
  simpa [indicator] using mixedBorderZP_card
    (a := 3) (b := 1) (c := 2) (r := 0) (u := 1) (v := 2)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset
      (mixedSoclesPQ (a := 3) (b := 1) (c := 1) 1 2 2 (by omega))).card = 4 := by
  simpa [indicator] using mixedBorderPQ_card
    (a := 3) (b := 1) (c := 1) (r := 1) (u := 2) (v := 2)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset
      (mixedSoclesYP (a := 2) (b := 1) (c := 1) 0 1 1 (by omega))).card ≠ 4 := by
  rw [mixedBorderYP_card (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)]
  simp [indicator]

/-! The frozen below/extra families and new core family cover both endpoints. -/

example :
    (borderFinset
      (pureDominantSoclesBelow (a := 3) (b := 2) 0 2 0 (by omega))).card = 5 := by
  simpa using pureDominantBorder_below_card
    (a := 3) (b := 2) (r := 0) (u := 2) (v := 0)
      (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset (pureDominantSoclesLast (a := 2) (b := 2) 1)).card = 6 := by
  simpa using pureDominantBorder_last_card
    (a := 2) (b := 2) (v := 1) (by omega) (by omega)

/-! Assembly smoke tests: these use only the public Run-11 conclusions. -/

example {k : Type*} [Field k] {S : Finset (Normal 2 1 1)}
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (htrace : P23.Artin.VariablesInTrace k S hlive) :
    (borderFinset S).card ≠ 4 :=
  P23.Artin.mixed_directModel_HL5 S (by omega) (by omega) (by omega)
    hcard hlive hanti htrace

example {k : Type*} [Field k] {S : Finset (Normal 2 2 0)}
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (htrace : P23.Artin.VariablesInTrace k S hlive) :
    (borderFinset S).card ≠ 4 :=
  P23.Artin.pure_directModel_HL5 S (by omega) (by omega)
    hcard hlive hanti htrace

end P23.Run11Regression

