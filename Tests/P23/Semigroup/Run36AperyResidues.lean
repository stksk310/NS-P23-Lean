import P23.Semigroup.AperyResidues
import Mathlib

open P23.Semigroup
open P23.Semigroup.FourGeneratedNumericalSemigroup

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :
    Function.Injective (aperyResidue D i) := aperyResidue_injective D i
example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :
    Function.Surjective (aperyResidue D i) := aperyResidue_surjective D i
#check aperyResidueEquiv
example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :
    Nat.card (D.AperyIndex i) = D.n i := aperyIndex_card D i
