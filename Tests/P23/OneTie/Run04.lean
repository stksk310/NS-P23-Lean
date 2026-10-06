import P23.OneTie.SemanticBorder
import P23.OneTie.NonDominantRows

namespace P23.OneTie

/-! Run-04 public semantic API. -/

#check IsDivisibilityMinimalKilled
#check standardSet_dvd_closed
#check properDivisor_factors_through_predecessor
#check isMinimalBorder_iff_isDivisibilityMinimalKilled
#check mixed_isMinimalBorder_iff_isDivisibilityMinimalKilled
#check pure_isMinimalBorder_iff_isDivisibilityMinimalKilled

example (S : Finset (Normal 5 2 3)) (m : Normal 5 2 3) :
    IsMinimalBorder (standardSet S) m ↔
      IsDivisibilityMinimalKilled (standardSet S) m := by
  exact mixed_isMinimalBorder_iff_isDivisibilityMinimalKilled S m
    (by omega) (by omega) (by omega)

example (S : Finset (Normal 4 2 0)) (m : Normal 4 2 0) :
    IsMinimalBorder (standardSet S) m ↔
      IsDivisibilityMinimalKilled (standardSet S) m := by
  exact pure_isMinimalBorder_iff_isDivisibilityMinimalKilled S m
    (by omega) (by omega)

/-! M2 exact rows and load-bearing endpoint cases. -/

#check m2K_border_exact
#check m2K_border_card
#check m2K_endpoint_xK
#check m2K_endpoint_xQ
#check m2Z_border_exact
#check m2Z_border_card
#check m2Z_endpoint_xQ

example :
    (borderFinset (m2KSocles (a := 5) (r := 3) (u := 2) (v := 4)
      (by omega) (by omega))).card = 3 := by
  simpa using m2K_border_card (a := 5) (r := 3) (u := 2) (v := 4)
    (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset (m2KSocles (a := 6) (r := 2) (u := 2) (v := 3)
      (by omega) (by omega))).card = 5 := by
  simpa using m2K_border_card (a := 6) (r := 2) (u := 2) (v := 3)
    (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset (m2ZSocles (a := 5) (r := 3) (u := 2) (v := 4)
      (by omega) (by omega))).card = 5 := by
  simpa using m2Z_border_card (a := 5) (r := 3) (u := 2) (v := 4)
    (by omega) (by omega) (by omega) (by omega)

/-! M3K/M4Y exact rows. -/

#check m3K_border_exact
#check m3K_border_card
#check m3K_endpoint_xK
#check m4Y_border_exact
#check m4Y_border_card

example :
    (borderFinset (m3KSocles (a := 2) (b := 3) (c := 2) (v := 4)
      (by omega))).card = 5 := by
  simpa using m3K_border_card (a := 2) (b := 3) (c := 2) (v := 4)
    (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset (m4YSocles (a := 5) (u := 2) (v := 0)
      (by omega))).card = 5 := by
  simpa using m4Y_border_card (a := 5) (u := 2) (v := 0)
    (by omega) (by omega)

/-! M5 and pure exact rows. -/

#check m5Y_border_exact
#check m5Y_border_card
#check m5Y_c_eq_one_redundancy_yz
#check m5Y_c_eq_one_redundancy_xz
#check m5Z_border_exact
#check m5Z_border_card
#check p4Z_border_exact
#check p4Z_border_card
#check p5Z_border_exact
#check p5Z_border_card
#check nonDominantRowCardSummary

example :
    (borderFinset (m5YSocles (a := 5) (b := 2) (c := 1) (v := 3)
      (by omega))).card = 3 := by
  simpa using m5Y_border_card (a := 5) (b := 2) (c := 1) (v := 3)
    (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset (m5YSocles (a := 5) (b := 2) (c := 3) (v := 2)
      (by omega))).card = 5 := by
  simpa using m5Y_border_card (a := 5) (b := 2) (c := 3) (v := 2)
    (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset (m5ZSocles (a := 4) (b := 2) (c := 2) (v := 1)
      (by omega))).card = 5 := by
  simpa using m5Z_border_card (a := 4) (b := 2) (c := 2) (v := 1)
    (by omega) (by omega) (by omega) (by omega)

example :
    (borderFinset (p4ZSocles (a := 4) (b := 2) (V := 1)
      (by omega))).card = 4 := by
  simpa using p4Z_border_card (a := 4) (b := 2) (V := 1)
    (by omega) (by omega) (by omega)

example :
    (borderFinset (p5ZSocles (a := 4) (b := 2) (v := 1)
      (by omega))).card = 4 := by
  simpa using p5Z_border_card (a := 4) (b := 2) (v := 1)
    (by omega) (by omega) (by omega)

/-! Nonprimitive live tie (`x^4=y^2z^2`) remains in scope. -/
example :
    (borderFinset (m5ZSocles (a := 4) (b := 2) (c := 2) (v := 2)
      (by omega))).card = 5 := by
  simpa using m5Z_border_card (a := 4) (b := 2) (c := 2) (v := 2)
    (by omega) (by omega) (by omega) (by omega)

end P23.OneTie
