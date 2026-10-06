import P23.Algebra.CyclicBoxCharacter

open P23.Algebra
#check cyclicCharacter_two_torsion
#check geometric_sum_zero_nsmul
#check cyclicCharacter_translation_sum_zero
#check cyclicCharacter_box_product
#check nonzero_two_torsion_eq_half

open scoped BigOperators
example {q : ℕ} [NeZero q] (h : ZMod q) (hn : h≠0) (hh : h+h=0) :
    2∣q ∧ h=((q/2:ℕ):ZMod q) := nonzero_two_torsion_eq_half h hn hh
example {q : ℕ} [NeZero q] (h : ZMod q) (hn : h≠0) (hh : h+h=0) :
    cyclicCharacter h=-1 := cyclicCharacter_two_torsion h hn hh
example {q : ℕ} [NeZero q] (n : ℕ) (w : ZMod q)
    (hz : cyclicGeometricSum n w=0) : n • w=0 := geometric_sum_zero_nsmul n w hz
example {q : ℕ} [NeZero q] (S : Finset (ZMod q)) (h : ZMod q)
    (hn : h≠0) (hh : h+h=0) (ht : S.image (fun w=>w+h)=S) :
    ∑ w∈S,cyclicCharacter w=0 := cyclicCharacter_translation_sum_zero S h hn hh ht
example {q : ℕ} [NeZero q] (A B C : ℕ) (X Y Z : ZMod q) :
    cyclicBoxSum A B C X Y Z=cyclicGeometricSum A X*cyclicGeometricSum B Y*cyclicGeometricSum C Z :=
  cyclicCharacter_box_product A B C X Y Z
