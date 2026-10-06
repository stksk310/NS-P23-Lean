import P23.OneTie.MixedCases
import P23.OneTie.PureCases

-- RED contract for Run 03 Target A: a nonempty socle finset has an exact
-- finite border representation.
#check P23.OneTie.mem_borderFinset_iff
#check P23.OneTie.mixedPrincipalBorder_last
#check P23.OneTie.mixedPrincipalBorder_below
#check P23.OneTie.mixedPrincipalBorder_last_card
#check P23.OneTie.mixedPrincipalBorder_below_card
#check P23.OneTie.purePrincipalBorder_below
#check P23.OneTie.purePrincipalBorder_last
#check P23.OneTie.purePrincipalBorder_below_card
#check P23.OneTie.purePrincipalBorder_last_card
#check P23.OneTie.pure_xH_endpoint
#check P23.OneTie.mixedBorderYZ_card
#check P23.OneTie.mixedBorderYP_card
#check P23.OneTie.mixedBorderYQ_card
#check P23.OneTie.mixedBorderZP_card
#check P23.OneTie.mixedBorderZQ_card
#check P23.OneTie.mixedBorderPQ_card
#check P23.OneTie.wrappedPredecessor_zY_c_eq_one
#check P23.OneTie.mixedDominant_card_eq_four_survivors
#check P23.OneTie.pureDominantBorder_below_exact
#check P23.OneTie.pureDominantBorder_last_exact
#check P23.OneTie.pureDominant_card_of_pos
#check P23.OneTie.pureDominant_card_of_zero
#check P23.OneTie.pureDominant_card_ne_four

namespace P23.OneTie.Run03Regression

open Normal

abbrev N := Normal 3 1 1

def unitSocle : N := ⟨0, 0, 0, by decide⟩
def unitSocles : Finset N := {unitSocle}
def xBorder : N := ⟨1, 0, 0, by decide⟩

example : unitSocles.Nonempty := by simp [unitSocles]

example : xBorder ∈ borderFinset unitSocles := by
  rw [mem_borderFinset_iff (by simp [unitSocles])]
  simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
    unitSocles, unitSocle, xBorder, Normal.predecessor,
    Normal.exact_divides_iff, Normal.DividesCriterion,
    Normal.xPredecessor]

-- The empty-socle edge stays deliberately outside the exact theorem: the
-- candidate finset is empty while the vacuous predecessor criterion admits 1.
example : (1 : N) ∉ borderFinset ∅ := by
  rw [borderFinset, mem_borderCandidateFinset_iff]
  simp [standardFinset]

example : IsMinimalBorder (standardSet (∅ : Finset N)) 1 := by
  simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
    Normal.predecessor]

-- Mixed principal last layer.
example :
    (borderFinset
      ({mixedCore (a := 3) (b := 1) (c := 1) 2 1 1 (by decide)} :
        Finset (Normal 3 1 1))).card = 2 := by
  simpa using mixedPrincipalBorder_last_card
    (a := 3) (b := 1) (c := 1) (r := 2) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Below-last with h=1 and simultaneously b=c=d=e=1.
example :
    (borderFinset
      ({mixedCore (a := 3) (b := 1) (c := 1) 0 1 1 (by decide)} :
        Finset (Normal 3 1 1))).card = 4 := by
  simpa using mixedPrincipalBorder_below_card
    (a := 3) (b := 1) (c := 1) (r := 0) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Endpoint r=a-2, equivalently h=a-1.
example :
    (borderFinset
      ({mixedCore (a := 3) (b := 1) (c := 1) 1 1 1 (by decide)} :
        Finset (Normal 3 1 1))).card = 4 := by
  simpa using mixedPrincipalBorder_below_card
    (a := 3) (b := 1) (c := 1) (r := 1) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Pure principal below-last, v=0 and endpoint r=a-2.
example :
    (borderFinset
      ({pureCore (a := 3) (b := 2) 1 2 0 (by decide)} :
        Finset (Normal 3 2 0))).card = 2 := by
  simpa using purePrincipalBorder_below_card
    (a := 3) (b := 2) (r := 1) (u := 2) (v := 0)
    (by decide) (by decide) (by decide) (by decide)

-- Pure principal last layer, v=1.
example :
    (borderFinset
      ({pureCore (a := 3) (b := 2) 2 1 1 (by decide)} :
        Finset (Normal 3 2 0))).card = 2 := by
  simpa using purePrincipalBorder_last_card
    (a := 3) (b := 2) (r := 2) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide)

example :
    pureH (a := 3) (b := 2) 1 2 (by decide) *
        (Normal.xGenerator : Normal 3 2 0) =
      mixedY (a := 3) (b := 2) (c := 0) 2 := by
  exact pure_xH_endpoint
    (a := 3) (b := 2) (r := 1) (u := 2)
    (by decide) (by decide) (by decide) (by decide)

-- All six dominant mixed choices at the simultaneous h=1, b=c=d=e=1 edge.
example :
    (borderFinset (mixedSoclesYZ (a := 3) (b := 1) (c := 1)
      0 1 1 (by decide))).card = 4 := by
  simpa [indicator] using mixedBorderYZ_card
    (a := 3) (b := 1) (c := 1) (r := 0) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example :
    (borderFinset (mixedSoclesYP (a := 3) (b := 1) (c := 1)
      0 1 1 (by decide))).card = 5 := by
  simpa [indicator] using mixedBorderYP_card
    (a := 3) (b := 1) (c := 1) (r := 0) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example :
    (borderFinset (mixedSoclesYQ (a := 3) (b := 1) (c := 1)
      0 1 1 (by decide))).card = 4 := by
  simpa [indicator] using mixedBorderYQ_card
    (a := 3) (b := 1) (c := 1) (r := 0) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Explicit reflected Y/Q case.
example :
    (borderFinset (mixedSoclesZP (a := 3) (b := 1) (c := 1)
      0 1 1 (by decide))).card = 4 := by
  simpa [indicator] using mixedBorderZP_card
    (a := 3) (b := 1) (c := 1) (r := 0) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example :
    (borderFinset (mixedSoclesZQ (a := 3) (b := 1) (c := 1)
      0 1 1 (by decide))).card = 5 := by
  simpa [indicator] using mixedBorderZQ_card
    (a := 3) (b := 1) (c := 1) (r := 0) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example :
    (borderFinset (mixedSoclesPQ (a := 3) (b := 1) (c := 1)
      0 1 1 (by decide))).card = 5 := by
  simpa [indicator] using mixedBorderPQ_card
    (a := 3) (b := 1) (c := 1) (r := 0) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- The endpoint P,Q survivor: h=a-1 and both residual exponents are positive.
example :
    (borderFinset (mixedSoclesPQ (a := 3) (b := 1) (c := 1)
      1 2 2 (by decide))).card = 4 := by
  simpa [indicator] using mixedBorderPQ_card
    (a := 3) (b := 1) (c := 1) (r := 1) (u := 2) (v := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Pure dominant v=0/v=1 and the r=a-2 endpoint in the below-last branch.
example :
    (borderFinset (pureDominantSoclesBelow (a := 3) (b := 2)
      1 2 0 (by decide))).card = 5 := by
  simpa using pureDominantBorder_below_card
    (a := 3) (b := 2) (r := 1) (u := 2) (v := 0)
    (by decide) (by decide) (by decide) (by decide)

example :
    (borderFinset (pureDominantSoclesBelow (a := 3) (b := 2)
      1 2 1 (by decide))).card = 6 := by
  simpa using pureDominantBorder_below_card
    (a := 3) (b := 2) (r := 1) (u := 2) (v := 1)
    (by decide) (by decide) (by decide) (by decide)

example :
    (borderFinset (pureDominantSoclesLast (a := 3) (b := 2) 0)).card = 5 := by
  simpa using pureDominantBorder_last_card (a := 3) (b := 2) (v := 0)
    (by decide) (by decide)

example :
    (borderFinset (pureDominantSoclesLast (a := 3) (b := 2) 1)).card = 6 := by
  simpa using pureDominantBorder_last_card (a := 3) (b := 2) (v := 1)
    (by decide) (by decide)

end P23.OneTie.Run03Regression

