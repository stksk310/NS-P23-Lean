import P23.Monomial.PlainNoFiveFamilies
namespace P23.Monomial
example (r u v : ℕ) : (plainBorderFinset (plainTriangleRoots r u v)).card = 4 :=
  plainTriangle_border_card r u v
example (r u v : ℕ) (hr : 0<r) (hu : 0<u) (hv : 0<v) :
    (plainBorderFinset (plainDominantAxisRoots r u v)).card = 7 :=
  plainDominantAxis_border_card r u v hr hu hv
example (r u s v h : ℕ) (hru : r<u) (hsv : s<v) (hh : 0<h) :
    (plainBorderFinset (plainPlaneAxisRoots r u s v h)).card = 6 :=
  plainPlaneAxis_border_card r u s v h hru hsv hh
end P23.Monomial
