import P23.Semigroup.MonomialSevenExclusion
#check P23.Semigroup.budget_zero_type_three_rho_le_six
#check P23.Semigroup.budget_zero_type_three_rho_seven_impossible

open P23.Semigroup
example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hz : D.fourBaseBudget i=0) (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) : D.semigroupRho≤6 :=
  budget_zero_type_three_rho_le_six D i hz ht hn

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hz : D.fourBaseBudget i=0) (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (h7 : D.semigroupRho=7) : False :=
  budget_zero_type_three_rho_seven_impossible D i hz ht hn h7

open P23.Monomial P23.Algebra
example {D : FourGeneratedNumericalSemigroup} {i : Fin 4} {A B C : ℕ}
    (M : BudgetZeroPlainModel D i) (e : Equiv.Perm (Fin 3))
    (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (he : M.roots.image (plainCoordinatePerm e)=plainDominantAxisRoots (A-1) (B-1) (C-1)) :
    D.n i=A*B*C+2 := sevenBoxApery_card M e hA hB hC he

example {D : FourGeneratedNumericalSemigroup} {i : Fin 4} {A B C : ℕ}
    (M : BudgetZeroPlainModel D i) (e : Equiv.Perm (Fin 3))
    (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (he : M.roots.image (plainCoordinatePerm e)=plainDominantAxisRoots (A-1) (B-1) (C-1))
    (p : SevenBoxShape A B C) :
    ((sevenBoxAperyEquiv M e hA hB hC he).trans (D.aperyResidueEquiv i)) p=
      sevenBoxResidue (D.tailGen i (e 0):ZMod (D.n i))
        (D.tailGen i (e 1):ZMod (D.n i)) (D.tailGen i (e 2):ZMod (D.n i)) p :=
  sevenBox_actual_residue M e hA hB hC he p
