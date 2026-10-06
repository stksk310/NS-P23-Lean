import P23.Algebra.SevenBoxResidueObstruction
#check P23.Algebra.sevenBox_residue_bijective_impossible

open P23.Algebra
example {q A B C : ℕ} [NeZero q] (ha : 2≤A) (hb : 2≤B) (hc : 2≤C)
    (X Y Z : ZMod q)
    (he : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z)) : False :=
  sevenBox_residue_bijective_impossible ha hb hc X Y Z he

open scoped BigOperators
example {q A B C : ℕ} [NeZero q] (ha : 0<A) (hb : 0<B) (hc : 0<C)
    (X Y Z : ZMod q) (he : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z)) :
    cyclicGeometricSum A X≠0 ∧ cyclicGeometricSum B Y≠0 :=
  sevenBox_character_XY_nonzero ha hb hc X Y Z he
example {q A B C : ℕ} [NeZero q] (X Y Z : ZMod q)
    (he : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (hh : ((A:ZMod q)*X-(B:ZMod q)*Y)+((A:ZMod q)*X-(B:ZMod q)*Y)=0) :
    (boxResidues (A:=A) (B:=B) (C:=C) X Y Z).image
      (fun w=>w+((A:ZMod q)*X-(B:ZMod q)*Y))=boxResidues (A:=A) (B:=B) (C:=C) X Y Z :=
  boxResidues_half_translation X Y Z he hh
example {q A B C : ℕ} [NeZero q] (X Y Z : ZMod q)
    (hi : Function.Injective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z)) :
    (∑ w∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z,cyclicCharacter w)=cyclicBoxSum A B C X Y Z :=
  boxResidues_character_sum X Y Z hi

example {q A B C : ℕ} [NeZero q] (ha : 2≤A) (hb : 2≤B) (hc : 2≤C)
    (X Y Z : ZMod q) (hi : Function.Injective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (hs : ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z-
      (A:ZMod q)*X=(B:ZMod q)*Y) : False := sevenBox_swap_impossible ha hb hc X Y Z hi hs

example {q A B C : ℕ} [NeZero q] (ha : 2≤A) (hb : 2≤B) (hc : 2≤C)
    (X Y Z : ZMod q) (he : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (hr : ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z-
      (A:ZMod q)*X=(A:ZMod q)*X)
    (hs : ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z-
      (B:ZMod q)*Y=(B:ZMod q)*Y) : False := sevenBox_fixed_impossible ha hb hc X Y Z he hr hs

example {q A B C : ℕ} [NeZero q] (ha : 0<A) (hb : 0<B) (hc : 0<C)
    (X Y Z : ZMod q) (hi : Function.Injective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (hz : C • Z=0) : addOrderOf Z=C := sevenBox_z_order ha hb hc X Y Z hi hz

-- Explicit arithmetic stage: the exact z-order and q=ABC+2 force C=2.
example {q A B C : ℕ} [NeZero q] (ha : 0<A) (hb : 0<B) (hc : 2≤C)
    (X Y Z : ZMod q) (hi : Function.Injective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (hz : C • Z=0) (hq : q=A*B*C+2) : C=2 := by
  have hord := sevenBox_z_order ha hb (by omega) X Y Z hi hz
  have hdq : C∣q := by simpa [hord,ZMod.card] using (addOrderOf_dvd_card (x:=Z))
  have hp : C∣A*B*C := ⟨A*B,by ring⟩
  have hh : C∣A*B*C+2 := hq ▸ hdq
  have hd2 : C∣2 := by simpa using (Nat.dvd_sub hh hp)
  have := Nat.le_of_dvd (by decide : 0<2) hd2
  omega

example {q : ℕ} [NeZero q] (Z : ZMod q) (hz : Z≠0) (hh : 2 • Z=0) :
    Z=((q/2:ℕ):ZMod q) :=
  (nonzero_two_torsion_eq_half Z hz (by simpa [two_nsmul,two_mul] using hh)).2

example {q A B C : ℕ} [NeZero q] (ha : 0<A) (hb : 0<B) (hc : 0<C)
    (X Y Z : ZMod q) (he : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z)) :
    let T := ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z
    (T-(A:ZMod q)*X=(B:ZMod q)*Y) ∨
      (T-(A:ZMod q)*X=(A:ZMod q)*X ∧ T-(B:ZMod q)*Y=(B:ZMod q)*Y) :=
  sevenBox_reflection_cases ha hb hc X Y Z he
