import P23.Semigroup.RhoFourResidualDegree

/-! Actual Apéry socle indices of the residual pure family. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.OneTie P23.Presentation
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
namespace ResidualTop
variable (R : RhoFourResidualPureBase D i)
local instance : NeZero R.residual.a' := ⟨by have := R.residual.a'_ge_two; omega⟩

def residualRootX : Normal R.residual.a' R.residual.b' 0 :=
  ⟨R.residual.a'-1,R.residual.residual.u-1,R.residual.residual.C-1,
    by have := R.residual.a'_ge_two; omega⟩
def residualRootY : Normal R.residual.a' R.residual.b' 0 :=
  ⟨0,R.residual.residual.u+R.residual.b'-2,R.residual.residual.C-1,
    Nat.pos_of_ne_zero (NeZero.ne _)⟩
def residualRootZ : Normal R.residual.a' R.residual.b' 0 :=
  ⟨0,R.residual.residual.u+R.residual.b'-1,R.residual.residual.C-2,
    Nat.pos_of_ne_zero (NeZero.ne _)⟩
def rootByResidualAxis (j : Fin 3) : Normal R.residual.a' R.residual.b' 0 :=
  if j=0 then residualRootX R else if j=1 then residualRootY R else residualRootZ R

theorem residual_roots_exact : R.residual.roots =
    {residualRootX R,residualRootY R,residualRootZ R} :=
  pureResidual_roots_exact R.residual.residual R.residual.nonempty R.residual.antichain

theorem residualRoot_mem (j : Fin 3) : rootByResidualAxis R j ∈ R.residual.roots := by
  rw [residual_roots_exact]
  fin_cases j <;> simp [rootByResidualAxis]

theorem residualRoot_distinct : residualRootX R ≠ residualRootY R ∧
    residualRootX R ≠ residualRootZ R ∧ residualRootY R ≠ residualRootZ R := by
  have ha := R.residual.a'_ge_two
  have hu := R.residual.residual.u_pos
  have hb := R.residual.b'_ge_two
  constructor
  · intro h; have := congrArg Normal.x h; dsimp [residualRootX,residualRootY] at this; omega
  · constructor
    · intro h; have := congrArg Normal.x h; dsimp [residualRootX,residualRootZ] at this; omega
    · intro h; have := congrArg Normal.y h; dsimp [residualRootY,residualRootZ] at this; omega

theorem residualRoot_mul_not_standard (j l : Fin 3) :
    rootByResidualAxis R j * coordinateGenerator l ∉ standardSet R.residual.roots := by
  rintro ⟨s,hs,hdiv⟩
  have hr := residualRoot_mem R j
  have hd : rootByResidualAxis R j ∣ s := dvd_trans (dvd_mul_right _ _) hdiv
  have he : rootByResidualAxis R j = s := by
    by_contra hn
    exact R.residual.antichain _ hr s hs hn hd
  obtain ⟨q,hq⟩ := hdiv
  have hdeg := congrArg (residualDegree R) hq
  rw [residualDegree_mul,residualDegree_mul,residualDegree_coordinateGenerator,←he] at hdeg
  have hp := D.tailGen_positive i (residualToTail R l)
  omega

def residualAperySocleIndex (j : Fin 3) : D.AperySocleIndex i :=
  let p := rootByResidualAxis R (tailToResidual R j)
  ⟨⟨tailDegreeGamma D i (residualTailExponent R p),
    (residual_isApery_iff_standard R p).mpr ⟨p,residualRoot_mem R _,dvd_refl p⟩⟩,by
    intro l hl
    let g : Normal R.residual.a' R.residual.b' 0 := coordinateGenerator (tailToResidual R l)
    apply residualRoot_mul_not_standard R (tailToResidual R j) (tailToResidual R l)
    apply (residual_isApery_iff_standard R (p*g)).mp
    have he : tailDegreeGamma D i (residualTailExponent R (p*g)) =
        tailDegreeGamma D i (residualTailExponent R p) + D.tail i l := by
      apply Subtype.ext
      change residualDegree R (p*g) = residualDegree R p + D.tailGen i l
      rw [residualDegree_mul]
      dsimp [g]
      rw [residualDegree_coordinateGenerator]
      simp [tailToResidual]
    rwa [he]⟩

def residualTopDegree : ℕ := R.residual.residual.formalTop
  (D.tailGen i (residualToTail R 1)) (D.tailGen i (residualToTail R 2))

theorem residualRoot_top_equation (j : Fin 3) :
    residualTopDegree R = residualDegree R (rootByResidualAxis R j) +
      D.tailGen i (residualToTail R j) := by
  have hh := pureResidual_top_equations R.residual.residual
    (D.tailGen i (residualToTail R 0)) (D.tailGen i (residualToTail R 1))
    (D.tailGen i (residualToTail R 2)) (residual_weighted_tie R)
  fin_cases j <;> simp only [rootByResidualAxis, Fin.reduceEq, ite_true, ite_false,
    residualDegree_formula] <;>
    dsimp [residualRootX,residualRootY,residualRootZ,residualTopDegree] <;>
    (try simp only [zero_mul,zero_add]) <;>
    first | exact hh.1.symm | exact hh.2.1.symm | exact hh.2.2.symm

theorem residualAperySocle_top_equation (j : Fin 3) :
    residualTopDegree R = aperySocleDegree D i (residualAperySocleIndex R j) + D.tailGen i j := by
  have hh := residualRoot_top_equation R (tailToResidual R j)
  simpa [tailToResidual,residualAperySocleIndex,aperySocleDegree,
    ResidualDegree.residualDegree,tailDegreeGamma] using hh

theorem residualAperySocleIndex_injective : Function.Injective (residualAperySocleIndex R) := by
  intro j l he
  have hd := congrArg (aperySocleDegree D i) he
  have hj := residualAperySocle_top_equation R j
  have hl := residualAperySocle_top_equation R l
  apply D.tailGen_injective i
  omega

def rhoFourResidualTopPattern (ht : D.semigroupType=3) : TailSocleTopPattern D i := by
  classical
  have hc : Fintype.card (Fin 3) = Fintype.card (D.AperySocleIndex i) := by
    rw [Fintype.card_fin,D.pseudoFrobenius_card_eq_aperySocle_card,ht]
  exact ⟨residualTopDegree R,Equiv.ofBijective (residualAperySocleIndex R)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨residualAperySocleIndex_injective R,hc⟩),residualAperySocle_top_equation R⟩

end ResidualTop
export ResidualTop (residualRootX residualRootY residualRootZ rootByResidualAxis
  residual_roots_exact residualRoot_mem residualRoot_distinct residualRoot_mul_not_standard
  residualAperySocleIndex residualTopDegree residualRoot_top_equation
  residualAperySocle_top_equation residualAperySocleIndex_injective rhoFourResidualTopPattern)
end
end P23.Semigroup
