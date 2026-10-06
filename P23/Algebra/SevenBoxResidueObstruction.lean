import P23.Monomial.PlainSevenBox
import P23.Algebra.CyclicBoxCharacter

namespace P23.Algebra
noncomputable section
open P23.Monomial
open scoped BigOperators
variable {q A B C : ℕ} [NeZero q]

def boxWeight (X Y Z : ZMod q) (p : Fin A × Fin B × Fin C) : ZMod q :=
  (p.1.val : ZMod q)*X+(p.2.1.val : ZMod q)*Y+(p.2.2.val : ZMod q)*Z

def sevenBoxResidue (X Y Z : ZMod q) : SevenBoxShape A B C → ZMod q
  | .inl p => boxWeight X Y Z p
  | .inr j => if j=0 then (A:ZMod q)*X else (B:ZMod q)*Y

def boxResidues (X Y Z : ZMod q) : Finset (ZMod q) :=
  Finset.univ.image (boxWeight (A:=A) (B:=B) (C:=C) X Y Z)

theorem boxResidues_mem (X Y Z : ZMod q)
    (hb : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (w : ZMod q) : w∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z ↔
      w≠(A:ZMod q)*X ∧ w≠(B:ZMod q)*Y := by
  classical
  constructor
  · intro hw
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hw
    constructor
    · intro he
      have hh := hb.1 (a₁:=Sum.inl p) (a₂:=Sum.inr 0) (by
        simpa [sevenBoxResidue] using hp.trans he)
      cases hh
    · intro he
      have hh := hb.1 (a₁:=Sum.inl p) (a₂:=Sum.inr 1) (by
        simpa [sevenBoxResidue] using hp.trans he)
      cases hh
  · rintro ⟨hr,hs⟩
    obtain ⟨p,hp⟩ := hb.2 w
    cases p with
    | inl p => exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,hp⟩
    | inr j => fin_cases j <;> simp [sevenBoxResidue] at hp
               · exact False.elim (hr hp.symm)
               · exact False.elim (hs hp.symm)

theorem boxWeight_reflection (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (X Y Z : ZMod q) (p : Fin A × Fin B × Fin C) :
    boxWeight X Y Z (p.1.rev,p.2.1.rev,p.2.2.rev)=
      ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z-
        boxWeight X Y Z p := by
  have hx : p.1.rev.val+p.1.val=A-1 := by simp [Fin.rev]; omega
  have hy : p.2.1.rev.val+p.2.1.val=B-1 := by simp [Fin.rev]; omega
  have hz : p.2.2.rev.val+p.2.2.val=C-1 := by simp [Fin.rev]; omega
  have hx' : (p.1.rev.val:ZMod q)+(p.1.val:ZMod q)=((A-1:ℕ):ZMod q) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod q)) hx
  have hy' : (p.2.1.rev.val:ZMod q)+(p.2.1.val:ZMod q)=((B-1:ℕ):ZMod q) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod q)) hy
  have hz' : (p.2.2.rev.val:ZMod q)+(p.2.2.val:ZMod q)=((C-1:ℕ):ZMod q) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod q)) hz
  unfold boxWeight
  linear_combination hx'*X+hy'*Y+hz'*Z

theorem boxResidues_reflection (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (X Y Z : ZMod q) (w : ZMod q) :
    (((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z-w)
      ∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z ↔
      w∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z := by
  classical
  let T := ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z
  have forward (w : ZMod q) (hw : w∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z) :
      T-w∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z := by
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨(p.1.rev,p.2.1.rev,p.2.2.rev),Finset.mem_univ _,
      (boxWeight_reflection hA hB hC X Y Z p).trans (by rw [hp])⟩
  constructor
  · intro hw
    have hh := forward (T-w) hw
    simpa [T] using hh
  · exact forward w

theorem sevenBox_extensions (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (X Y Z : ZMod q)
    (hb : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z)) :
    (A:ZMod q)*X≠(B:ZMod q)*Y ∧ (A:ZMod q)*X≠0 ∧ (B:ZMod q)*Y≠0 := by
  have hxy : (A:ZMod q)*X≠(B:ZMod q)*Y := by
    intro he
    have hh := hb.1 (a₁:=Sum.inr 0) (a₂:=Sum.inr 1) (by simpa [sevenBoxResidue] using he)
    have : (0 : Fin 2)=1 := Sum.inr.inj hh
    omega
  have hzero : (0 : ZMod q)∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z :=
    Finset.mem_image.mpr ⟨(⟨0,hA⟩,⟨0,hB⟩,⟨0,hC⟩),Finset.mem_univ _,by simp [boxWeight]⟩
  have hz := (boxResidues_mem X Y Z hb 0).mp hzero
  exact ⟨hxy,Ne.symm hz.1,Ne.symm hz.2⟩

theorem sevenBox_reflection_cases (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (X Y Z : ZMod q)
    (hb : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z)) :
    let T := ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z
    (T-(A:ZMod q)*X=(B:ZMod q)*Y) ∨
      (T-(A:ZMod q)*X=(A:ZMod q)*X ∧ T-(B:ZMod q)*Y=(B:ZMod q)*Y) := by
  classical
  dsimp
  let T := ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z
  have nmem (w : ZMod q) (hw : w=(A:ZMod q)*X ∨ w=(B:ZMod q)*Y) :
      T-w=(A:ZMod q)*X ∨ T-w=(B:ZMod q)*Y := by
    have hn : ¬w∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z := by
      rw [boxResidues_mem X Y Z hb]; tauto
    have hn' : ¬T-w∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z := by
      exact fun h=>hn ((boxResidues_reflection hA hB hC X Y Z w).mp h)
    rw [boxResidues_mem X Y Z hb] at hn'
    tauto
  rcases nmem ((A:ZMod q)*X) (Or.inl rfl) with hr | hr
  · right
    refine ⟨hr,?_⟩
    rcases nmem ((B:ZMod q)*Y) (Or.inr rfl) with hs | hs
    · have he : (A:ZMod q)*X=(B:ZMod q)*Y := by linear_combination hs-hr
      exact False.elim ((sevenBox_extensions hA hB hC X Y Z hb).1 he)
    · exact hs
  · exact Or.inl hr

theorem sevenBox_swap_impossible (hA : 2≤A) (hB : 2≤B) (hC : 2≤C)
    (X Y Z : ZMod q)
    (hinj : Function.Injective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (hs : ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z-
      (A:ZMod q)*X=(B:ZMod q)*Y) : False := by
  have ha : ((A-1:ℕ):ZMod q)+1=(A:ZMod q) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ZMod q)) (Nat.sub_add_cancel (by omega : 1≤A))
  have hb : ((B-1:ℕ):ZMod q)+1=(B:ZMod q) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ZMod q)) (Nat.sub_add_cancel (by omega : 1≤B))
  have hrel : X+Y=((C-1:ℕ):ZMod q)*Z := by linear_combination -hs+ha*X+hb*Y
  have he := hinj (a₁:=Sum.inl (⟨1,by omega⟩,⟨1,by omega⟩,⟨0,by omega⟩))
    (a₂:=Sum.inl (⟨0,by omega⟩,⟨0,by omega⟩,⟨C-1,by omega⟩))
    (by simpa [sevenBoxResidue,boxWeight] using hrel)
  have he' := congrArg (fun p : SevenBoxShape A B C =>
    match p with | .inl p => p.1.val | .inr _ => 0) he
  simp at he'

theorem boxResidues_half_translation (X Y Z : ZMod q)
    (hb : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (h2 : ((A:ZMod q)*X-(B:ZMod q)*Y)+((A:ZMod q)*X-(B:ZMod q)*Y)=0) :
    (boxResidues (A:=A) (B:=B) (C:=C) X Y Z).image
      (fun w=>w+((A:ZMod q)*X-(B:ZMod q)*Y))=boxResidues (A:=A) (B:=B) (C:=C) X Y Z := by
  classical
  let r := (A:ZMod q)*X
  let s := (B:ZMod q)*Y
  have hswap : r+(r-s)=s := by dsimp [r,s]; linear_combination h2
  have hswap' : s+(r-s)=r := by ring
  ext w
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v,hv,rfl⟩
    have hv' := (boxResidues_mem X Y Z hb v).mp hv
    apply (boxResidues_mem X Y Z hb _).mpr
    constructor
    · intro he; apply hv'.2
      have : v=s := by dsimp [r,s] at *; linear_combination he
      exact this
    · intro he; apply hv'.1
      have : v=r := by dsimp [r,s] at *; linear_combination he-h2
      exact this
  · intro hw
    refine ⟨w+(r-s),?_,?_⟩
    · have hw' := (boxResidues_mem X Y Z hb w).mp hw
      apply (boxResidues_mem X Y Z hb _).mpr
      constructor
      · intro he; apply hw'.2
        have : w=s := by dsimp [r,s] at *; linear_combination he
        exact this
      · intro he; apply hw'.1
        have : w=r := by dsimp [r,s] at *; linear_combination he-h2
        exact this
    · dsimp [r,s]; linear_combination h2

theorem boxResidues_character_sum (X Y Z : ZMod q)
    (hinj : Function.Injective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z)) :
    (∑ w∈boxResidues (A:=A) (B:=B) (C:=C) X Y Z,cyclicCharacter w)=
      cyclicBoxSum A B C X Y Z := by
  classical
  rw [boxResidues,Finset.sum_image]
  · simp only [Fintype.sum_prod_type,boxWeight,cyclicBoxSum,nsmul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y : Fin B, ∑ z : Fin C,
      cyclicCharacter ((x:ZMod q)*X+(y.val:ZMod q)*Y+(z.val:ZMod q)*Z))]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Fin.sum_univ_eq_sum_range (fun y => ∑ z : Fin C,
      cyclicCharacter ((x:ZMod q)*X+(y:ZMod q)*Y+(z.val:ZMod q)*Z))]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Fin.sum_univ_eq_sum_range (fun z =>
      cyclicCharacter ((x:ZMod q)*X+(y:ZMod q)*Y+(z:ZMod q)*Z))]
  · intro p _ r _ he
    exact Sum.inl.inj (hinj (a₁:=Sum.inl p) (a₂:=Sum.inl r) he)

theorem sevenBox_z_order (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (X Y Z : ZMod q)
    (hinj : Function.Injective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (hz : C • Z=0) : addOrderOf Z=C := by
  apply (addOrderOf_eq_iff hC).mpr
  refine ⟨hz,?_⟩
  intro m hm hpos he
  have hh := hinj (a₁:=Sum.inl (⟨0,hA⟩,⟨0,hB⟩,⟨m,hm⟩))
    (a₂:=Sum.inl (⟨0,hA⟩,⟨0,hB⟩,⟨0,hC⟩))
    (by simpa [sevenBoxResidue,boxWeight,nsmul_eq_mul] using he)
  have hh' := congrArg (fun p : SevenBoxShape A B C =>
    match p with | .inl p => p.2.2.val | .inr _ => 0) hh
  simp at hh'
  omega

theorem sevenBox_character_XY_nonzero (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (X Y Z : ZMod q)
    (hb : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z)) :
    cyclicGeometricSum A X≠0 ∧ cyclicGeometricSum B Y≠0 := by
  constructor
  · intro hz
    have he := geometric_sum_zero_nsmul A X hz
    exact (sevenBox_extensions hA hB hC X Y Z hb).2.1 (by simpa [nsmul_eq_mul] using he)
  · intro hz
    have he := geometric_sum_zero_nsmul B Y hz
    exact (sevenBox_extensions hA hB hC X Y Z hb).2.2 (by simpa [nsmul_eq_mul] using he)

theorem sevenBox_fixed_impossible (hA : 2≤A) (hB : 2≤B) (hC : 2≤C)
    (X Y Z : ZMod q)
    (hb : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z))
    (hr : ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z-
      (A:ZMod q)*X=(A:ZMod q)*X)
    (hs : ((A-1:ℕ):ZMod q)*X+((B-1:ℕ):ZMod q)*Y+((C-1:ℕ):ZMod q)*Z-
      (B:ZMod q)*Y=(B:ZMod q)*Y) : False := by
  classical
  have hAp : 0<A := by omega
  have hBp : 0<B := by omega
  have hCp : 0<C := by omega
  have hcard : q=A*B*C+2 := by
    have he := Fintype.card_congr (Equiv.ofBijective _ hb)
    simpa [sevenBoxShape_card,ZMod.card,Nat.mul_assoc] using he.symm
  let r := (A:ZMod q)*X
  let s := (B:ZMod q)*Y
  let h := r-s
  have hne : h≠0 := sub_ne_zero.mpr (sevenBox_extensions hAp hBp hCp X Y Z hb).1
  have h2 : h+h=0 := by dsimp [h,r,s]; linear_combination hs-hr
  have hhalf := nonzero_two_torsion_eq_half h hne h2
  have hsum := cyclicCharacter_translation_sum_zero
    (boxResidues (A:=A) (B:=B) (C:=C) X Y Z) h hne h2
    (boxResidues_half_translation X Y Z hb h2)
  rw [boxResidues_character_sum X Y Z hb.1,cyclicCharacter_box_product] at hsum
  obtain ⟨hx,hy⟩ := sevenBox_character_XY_nonzero hAp hBp hCp X Y Z hb
  have hz : cyclicGeometricSum C Z=0 := (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero hx hy)
  have hCZ := geometric_sum_zero_nsmul C Z hz
  have hord := sevenBox_z_order hAp hBp hCp X Y Z hb.1 hCZ
  have hdq : C∣q := by simpa [hord,ZMod.card] using (addOrderOf_dvd_card (x:=Z))
  have hd2 : C∣2 := by
    have hp : C∣A*B*C := ⟨A*B,by ring⟩
    have hh : C∣A*B*C+2 := hcard ▸ hdq
    simpa using (Nat.dvd_sub hh hp)
  have hC2 : C=2 := by have := Nat.le_of_dvd (by decide : 0<2) hd2; omega
  have hZne : Z≠0 := by
    intro he
    have hh := hb.1 (a₁:=Sum.inl (⟨0,hAp⟩,⟨0,hBp⟩,⟨1,by omega⟩))
      (a₂:=Sum.inl (⟨0,hAp⟩,⟨0,hBp⟩,⟨0,hCp⟩)) (by simp [sevenBoxResidue,boxWeight,he])
    have hh' := congrArg (fun p : SevenBoxShape A B C =>
      match p with | .inl p => p.2.2.val | .inr _ => 0) hh
    simp at hh'
  have hZ2 : Z+Z=0 := by simpa [hC2,two_nsmul,two_mul] using hCZ
  have hZh : Z=h := (nonzero_two_torsion_eq_half Z hZne hZ2).2.trans hhalf.2.symm
  have ha : ((A-1:ℕ):ZMod q)+1=(A:ZMod q) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ZMod q)) (Nat.sub_add_cancel (by omega : 1≤A))
  have hbb : ((B-1:ℕ):ZMod q)+1=(B:ZMod q) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ZMod q)) (Nat.sub_add_cancel (by omega : 1≤B))
  have he : X+Y=0 := by
    simp only [hC2,show 2-1=1 by decide,Nat.cast_one,one_mul] at hr
    dsimp [h,r,s] at hZh
    linear_combination hZh-hr+ha*X+hbb*Y
  have hh := hb.1 (a₁:=Sum.inl (⟨1,by omega⟩,⟨1,by omega⟩,⟨0,hCp⟩))
    (a₂:=Sum.inl (⟨0,hAp⟩,⟨0,hBp⟩,⟨0,hCp⟩))
    (by simpa [sevenBoxResidue,boxWeight] using he)
  have hh' := congrArg (fun p : SevenBoxShape A B C =>
    match p with | .inl p => p.1.val | .inr _ => 0) hh
  simp at hh'

theorem sevenBox_residue_bijective_impossible (hA : 2≤A) (hB : 2≤B) (hC : 2≤C)
    (X Y Z : ZMod q)
    (hb : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C) X Y Z)) : False := by
  rcases sevenBox_reflection_cases (by omega) (by omega) (by omega) X Y Z hb with hs | ⟨hr,hs⟩
  · exact sevenBox_swap_impossible hA hB hC X Y Z hb.1 hs
  · exact sevenBox_fixed_impossible hA hB hC X Y Z hb hr hs

end
end P23.Algebra
