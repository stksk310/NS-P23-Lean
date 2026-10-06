import P23.Semigroup.PlainAperyResidues
import P23.Algebra.SevenBoxResidueObstruction

namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.Monomial P23.Algebra
open scoped BigOperators
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4} {A B C : ℕ}

theorem tailDegree_coordinate_inverse (e : Equiv.Perm (Fin 3)) (p : PlainExp) :
    tailDegree D i (plainCoordinatePerm e.symm p)=
      ∑ j : Fin 3,p j*D.tailGen i (e j) := by
  classical
  unfold tailDegree
  apply Finset.sum_bij (fun j _=>e.symm j)
  · intro j _; exact Finset.mem_univ _
  · intro a _ b _ he; exact e.symm.injective he
  · intro b _; exact ⟨e b,Finset.mem_univ _,by simp⟩
  · intro j _; simp

def sevenBoxToPlain (M : BudgetZeroPlainModel D i) (e : Equiv.Perm (Fin 3))
    (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (he : M.roots.image (plainCoordinatePerm e)=plainDominantAxisRoots (A-1) (B-1) (C-1))
    (p : SevenBoxShape A B C) : PlainMonomialIndex M.roots :=
  ⟨plainCoordinatePerm e.symm (sevenBoxExponent A B C p),by
    apply (mem_plainStandardFinset _ _).mpr
    apply (plainStandard_coordinatePerm_iff e M.roots _).mp
    have hi : plainCoordinatePerm e (plainCoordinatePerm e.symm (sevenBoxExponent A B C p))=
        sevenBoxExponent A B C p := by ext j; simp
    rw [hi,he]
    exact (sevenBoxExponent_range A B C hA hB hC _).mp ⟨p,rfl⟩⟩

theorem sevenBoxToPlain_bijective (M : BudgetZeroPlainModel D i) (e : Equiv.Perm (Fin 3))
    (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (he : M.roots.image (plainCoordinatePerm e)=plainDominantAxisRoots (A-1) (B-1) (C-1)) :
    Function.Bijective (sevenBoxToPlain M e hA hB hC he) := by
  constructor
  · intro p r hh
    apply sevenBoxExponent_injective A B C hA hB
    exact (plainCoordinatePerm e.symm).injective (congrArg Subtype.val hh)
  · intro p
    have hp := (plainStandard_coordinatePerm_iff e M.roots p.1).mpr
      ((mem_plainStandardFinset _ _).mp p.2)
    rw [he] at hp
    obtain ⟨r,hr⟩ := (sevenBoxExponent_range A B C hA hB hC _).mpr hp
    refine ⟨r,Subtype.ext ?_⟩
    change plainCoordinatePerm e.symm (sevenBoxExponent A B C r)=p.1
    rw [hr]
    ext j
    simp

def sevenBoxAperyEquiv (M : BudgetZeroPlainModel D i) (e : Equiv.Perm (Fin 3))
    (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (he : M.roots.image (plainCoordinatePerm e)=plainDominantAxisRoots (A-1) (B-1) (C-1)) :
    SevenBoxShape A B C ≃ D.AperyIndex i :=
  (Equiv.ofBijective _ (sevenBoxToPlain_bijective M e hA hB hC he)).trans (plainStandardAperyEquiv M)

theorem sevenBoxApery_card (M : BudgetZeroPlainModel D i) (e : Equiv.Perm (Fin 3))
    (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (he : M.roots.image (plainCoordinatePerm e)=plainDominantAxisRoots (A-1) (B-1) (C-1)) :
    D.n i=A*B*C+2 := by
  have hh := Nat.card_congr (sevenBoxAperyEquiv M e hA hB hC he)
  rw [D.aperyIndex_card] at hh
  simpa [Nat.card_eq_fintype_card,sevenBoxShape_card,Nat.mul_assoc] using hh.symm

theorem sevenBox_actual_residue (M : BudgetZeroPlainModel D i) (e : Equiv.Perm (Fin 3))
    (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (he : M.roots.image (plainCoordinatePerm e)=plainDominantAxisRoots (A-1) (B-1) (C-1))
    (p : SevenBoxShape A B C) :
    ((sevenBoxAperyEquiv M e hA hB hC he).trans (D.aperyResidueEquiv i)) p=
      sevenBoxResidue (D.tailGen i (e 0):ZMod (D.n i))
        (D.tailGen i (e 1):ZMod (D.n i)) (D.tailGen i (e 2):ZMod (D.n i)) p := by
  change (tailDegree D i (plainCoordinatePerm e.symm (sevenBoxExponent A B C p)):ZMod (D.n i))=_
  rw [tailDegree_coordinate_inverse]
  cases p with
  | inl p => simp [sevenBoxExponent,sevenBoxResidue,boxWeight,Fin.sum_univ_succ,plainExp,add_assoc]
  | inr j => fin_cases j <;> simp [sevenBoxExponent,sevenBoxResidue,Fin.sum_univ_succ,plainExp]

theorem budget_zero_type_three_rho_seven_impossible (D : FourGeneratedNumericalSemigroup)
    (i : Fin 4) (h0 : D.fourBaseBudget i=0) (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (h7 : D.semigroupRho=7) : False := by
  obtain ⟨M⟩ := budgetZeroPlainModel D i h0
  have h3 : M.roots.card=3 := M.rootCard_eq_semigroupType.trans ht
  obtain ⟨e,A,B,C,hA,hB,hC,he⟩ := plain_seven_border_exact_box M.roots M.roots_antichain
    h3 M.variables_survive (M.centres_of_ng (by omega) hn) (M.borderCard_eq_rho.trans h7)
  letI : NeZero (D.n i) := ⟨(Nat.ne_of_gt (D.positive i))⟩
  have hAp : 0<A := by omega
  have hBp : 0<B := by omega
  have hCp : 0<C := by omega
  let E := (sevenBoxAperyEquiv M e hAp hBp hCp he).trans (D.aperyResidueEquiv i)
  have heq : E.toFun=sevenBoxResidue (D.tailGen i (e 0):ZMod (D.n i))
      (D.tailGen i (e 1):ZMod (D.n i)) (D.tailGen i (e 2):ZMod (D.n i)) :=
    funext (sevenBox_actual_residue M e hAp hBp hCp he)
  have hb : Function.Bijective (sevenBoxResidue (A:=A) (B:=B) (C:=C)
      (D.tailGen i (e 0):ZMod (D.n i)) (D.tailGen i (e 1):ZMod (D.n i))
      (D.tailGen i (e 2):ZMod (D.n i))) := by
    rw [←heq]
    exact E.bijective
  exact sevenBox_residue_bijective_impossible hA hB hC _ _ _ hb

theorem budget_zero_type_three_rho_le_six (D : FourGeneratedNumericalSemigroup)
    (i : Fin 4) (h0 : D.fourBaseBudget i=0) (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) : D.semigroupRho≤6 := by
  obtain ⟨F⟩ := budgetZeroTypeThreeFrontier D i h0 ht hn
  have hf := F.rhoFrontier
  have hh : D.semigroupRho≠7 := fun h=>budget_zero_type_three_rho_seven_impossible D i h0 ht hn h
  omega

end
end P23.Semigroup
