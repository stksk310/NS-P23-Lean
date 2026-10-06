import P23.Monomial.PlainPermutation
namespace P23.Monomial
example (e : Equiv.Perm (Fin 3)) (R : Finset PlainExp) :
    (plainBorderFinset (R.image (plainCoordinatePerm e))).card = (plainBorderFinset R).card :=
  plainBorder_card_permutation e R
end P23.Monomial
