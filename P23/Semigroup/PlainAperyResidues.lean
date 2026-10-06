import P23.Semigroup.AperyResidues
import P23.Semigroup.PlainLocalFrontier
import P23.Semigroup.RhoFourMonomialBase

namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.Monomial
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}

theorem plain_standard_degree_injective (M : BudgetZeroPlainModel D i)
    (p q : PlainMonomialIndex M.roots) (he : tailDegree D i p.1=tailDegree D i q.1) : p=q := by
  classical
  by_contra hn
  have hpq : p.1≠q.1 := fun h=>hn (Subtype.ext h)
  let f : TailPoly ℚ := MvPolynomial.monomial p.1 1-MvPolynomial.monomial q.1 1
  have hmap : tailPolyToChosenBase (k:=ℚ) D i f=0 := by
    apply (chosenBaseEquivApery D i).injective
    simp only [map_zero,map_sub,f,tailPolyToChosenBase_monomial,one_smul]
    have hd : tailDegreeGamma D i p.1=tailDegreeGamma D i q.1 := Subtype.ext he
    rw [hd,sub_self]
  have hf : f∈plainMonomialIdeal ℚ (plainBorderFinset M.roots) := by
    rw [←M.generators_eq_border,M.idealEq]
    exact RingHom.mem_ker.mpr hmap
  have hz : plainPolyToArtin ℚ M.roots f=0 :=
    RingHom.mem_ker.mp ((plainPolyToArtin_kernel ℚ M.roots).symm ▸ hf)
  have hc := congrArg (fun x : PlainMonomialArtin ℚ M.roots =>x.coeff p) hz
  rw [coeff_plainPolyToArtin] at hc
  simpa [f,MvPolynomial.coeff_monomial,hpq,Ne.symm hpq] using hc

def plainStandardApery (M : BudgetZeroPlainModel D i) (p : PlainMonomialIndex M.roots) :
    D.AperyIndex i := ⟨tailDegreeGamma D i p.1,
      (chosenBase_plain_monomial_isApery_iff_standard D i M.generators M.roots
        M.idealEq M.generators_eq_border p.1).mpr ((mem_plainStandardFinset _ _).mp p.2)⟩

theorem plainStandardApery_bijective (M : BudgetZeroPlainModel D i) :
    Function.Bijective (plainStandardApery M) := by
  constructor
  · intro p q he
    exact plain_standard_degree_injective M p q (congrArg (fun s : D.AperyIndex i =>s.1.1) he)
  · intro w
    obtain ⟨u,hu⟩ := exists_tailExponent_of_isApery D i w.2
    have hg : tailDegreeGamma D i u=w.1 := Subtype.ext hu
    have hs : u∈plainStandardFinset M.roots := by
      apply (mem_plainStandardFinset _ _).mpr
      apply (chosenBase_plain_monomial_isApery_iff_standard D i M.generators M.roots
        M.idealEq M.generators_eq_border u).mp
      rw [hg]
      exact w.2
    exact ⟨⟨u,hs⟩,Subtype.ext hg⟩

def plainStandardAperyEquiv (M : BudgetZeroPlainModel D i) :
    PlainMonomialIndex M.roots ≃ D.AperyIndex i :=
  Equiv.ofBijective (plainStandardApery M) (plainStandardApery_bijective M)

def plainStandardResidueEquiv (M : BudgetZeroPlainModel D i) :
    PlainMonomialIndex M.roots ≃ ZMod (D.n i) :=
  (plainStandardAperyEquiv M).trans (D.aperyResidueEquiv i)

@[simp] theorem plainStandardResidueEquiv_apply (M : BudgetZeroPlainModel D i)
    (p : PlainMonomialIndex M.roots) :
    plainStandardResidueEquiv M p=(tailDegree D i p.1:ZMod (D.n i)) := rfl

end
end P23.Semigroup
