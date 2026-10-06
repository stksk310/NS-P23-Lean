import P23.Semigroup.TailSources
import P23.Semigroup.ChosenBasePlainTrace
import P23.Monomial.PlainHV
import P23.Monomial.PlainFourGeneratorShape

/-! Exact ordinary triangle socle transport and budget-zero exclusion at rho four.
All type/trace/NG premises refer to the genuine chosen-base quotient. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.Monomial P23.Presentation

variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

theorem chosenBase_plain_monomial_isApery_iff_standard (G R : Finset PlainExp)
    (hI : plainMonomialIdeal ℚ G=chosenBaseDefiningIdeal (k := ℚ) D i)
    (hG : G=plainBorderFinset R) (p : PlainExp) :
    D.IsApery i (tailDegreeGamma D i p) ↔ p∈plainStandardSet R := by
  classical
  have hm : MvPolynomial.monomial p (1 : ℚ) ∈ chosenBaseDefiningIdeal (k := ℚ) D i ↔
      p∉plainStandardSet R := by
    rw [←hI,hG,monomial_mem_plainMonomialIdeal_iff]
    exact (killed_iff_border_divisor R p).symm
  apply not_iff_not.mp
  constructor
  · intro hn
    obtain ⟨γ,hγ⟩ := not_not.mp hn
    apply hm.mp
    apply (tail_monomial_mem_chosenBaseDefiningIdeal_iff D i p).mpr
    exact ⟨⟨p,rfl⟩,γ,congrArg Subtype.val hγ⟩
  · intro hp ha
    have hk := (tail_monomial_mem_chosenBaseDefiningIdeal_iff D i p).mp (hm.mpr hp)
    obtain ⟨_,γ,hγ⟩ := hk
    exact ha ⟨γ,Subtype.ext hγ⟩

/-- The actual three Apéry socle indices, with the exact triangle top degree.
Degree injectivity is derived only for this family via tail injectivity. -/
theorem triangle_topPattern_of_chosenBase_border (G : Finset PlainExp) (r u v : ℕ)
    (hI : plainMonomialIdeal ℚ G=chosenBaseDefiningIdeal (k := ℚ) D i)
    (hG : G=plainTriangleBorder r u v)
    (ha : PlainRootAntichain (plainTriangleRoots r u v))
    (ht : D.semigroupType=3) :
    ∃ P : TailSocleTopPattern D i, P.top=tailDegree D i (plainExp (r+1) (u+1) (v+1)) := by
  classical
  let R := plainTriangleRoots r u v
  let p := plainExp (r+1) (u+1) (v+1)
  let w := fun j : Fin 3 => plainPredecessor j p
  have hGb : G=plainBorderFinset R := hG.trans (plainTriangle_border_exact r u v).symm
  have hiff (e : PlainExp) : D.IsApery i (tailDegreeGamma D i e) ↔ e∈plainStandardSet R :=
    chosenBase_plain_monomial_isApery_iff_standard D i G R hI hGb e
  have hw0 : w 0=plainExp r (u+1) (v+1) := by
    rw [plainExp_eq_coordinates]; simp [w,p,plainPredecessor_apply]
  have hw1 : w 1=plainExp (r+1) u (v+1) := by
    rw [plainExp_eq_coordinates]; simp [w,p,plainPredecessor_apply]
  have hw2 : w 2=plainExp (r+1) (u+1) v := by
    rw [plainExp_eq_coordinates]; simp [w,p,plainPredecessor_apply]
  have hwm (j : Fin 3) : w j∈R := by
    fin_cases j <;> simp [R,plainTriangleRoots,hw0,hw1,hw2]
  have hwadd (j : Fin 3) : w j+plainUnitVector j=p := by
    apply plainPredecessor_add_unitVector
    fin_cases j <;> simp [p]
  have htop (j : Fin 3) : tailDegree D i p=tailDegree D i (w j)+D.tailGen i j := by
    rw [←hwadd j,tailDegree_add]
    simp [plainUnitVector]
  have hk (j l : Fin 3) : plainUnitVector l+w j∉plainStandardSet R := by
    rintro ⟨s,hs,hps⟩
    have hws : plainDivides (w j) s := by
      intro x
      have hx := hps x
      simp only [Finsupp.add_apply] at hx
      omega
    have he := ha (w j) (hwm j) s hs hws
    have hcoord := congrArg (fun e : PlainExp => e l) he
    have hl := hps l
    simp only [Finsupp.add_apply,plainUnitVector_apply,ite_true] at hl
    omega
  let idx : Fin 3 → D.AperySocleIndex i := fun j =>
    ⟨⟨tailDegreeGamma D i (w j),
      (hiff (w j)).mpr ⟨w j,hwm j,plainDivides_refl _⟩⟩,by
      intro l hl
      apply hk j l
      apply (hiff _).mp
      have hγ : tailDegreeGamma D i (plainUnitVector l+w j)=
          tailDegreeGamma D i (w j)+D.tail i l := by
        apply Subtype.ext
        change tailDegree D i (plainUnitVector l+w j)=tailDegree D i (w j)+D.tailGen i l
        rw [tailDegree_add]
        simp [plainUnitVector,add_comm]
      rwa [hγ]⟩
  have hinj : Function.Injective idx := by
    intro j l he
    have hdeg := congrArg (fun s : D.AperySocleIndex i => aperySocleDegree D i s) he
    change tailDegree D i (w j)=tailDegree D i (w l) at hdeg
    apply D.tailGen_injective i
    have hj := htop j
    have hl := htop l
    omega
  have hcard : Fintype.card (Fin 3)=Fintype.card (D.AperySocleIndex i) := by
    rw [Fintype.card_fin,D.pseudoFrobenius_card_eq_aperySocle_card,ht]
  let E : Fin 3 ≃ D.AperySocleIndex i :=
    Equiv.ofBijective idx ((Fintype.bijective_iff_injective_and_card idx).mpr ⟨hinj,hcard⟩)
  refine ⟨⟨tailDegree D i p,E,?_⟩,rfl⟩
  intro j
  exact htop j

private theorem triangle_border_positive_non_top_unique (r u v : ℕ) (s : Fin 3)
    (p q : PlainExp) (hp : p∈plainTriangleBorder r u v) (hq : q∈plainTriangleBorder r u v)
    (hps : 0<p s) (hqs : 0<q s)
    (hpn : p≠plainExp (r+1) (u+1) (v+1))
    (hqn : q≠plainExp (r+1) (u+1) (v+1)) : p=q := by
  simp only [plainTriangleBorder,Finset.mem_insert,Finset.mem_singleton] at hp hq
  fin_cases s <;>
    rcases hp with rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl <;> simp_all

theorem rho_four_budget_zero_impossible (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupRho=4) : D.fourBaseBudget i≠0 := by
  intro hz
  obtain ⟨G,hI,hcard,hm⟩ := chosenBase_plain_exponentPresentation_of_budget_zero D i hz
  have hf := chosenBase_plainSurvivors_finite D i G hI
  have h0 := chosenBase_plain_unit_survives D i G hI
  let R := plainSurvivorRoots ℚ G hf
  have hR : R.Nonempty := plainSurvivorRoots_nonempty ℚ G hf h0
  have ha : PlainRootAntichain R := plainSurvivorRoots_antichain ℚ G hf
  have hG := plainGenerators_eq_border ℚ G hf (plainGenerators_antichain_of_minimal ℚ G hm)
  let E := chosenBasePlainQuotientEquiv D i G hI hf hG
  have hv : PlainVariablesSurvive R := chosenBase_plain_variables_survive D i G hI hf
  have htype : plainDirectType ℚ R hR=3 := (chosenPlain_type_eq R hR E).trans
    ((chosenBaseType_eq_semigroupType D i).trans ht)
  have hng : PlainDirectNearlyGorenstein ℚ R hR :=
    (chosenPlain_ng_iff R hR E).mp
      (semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein D i hn)
  have h3 : R.card=3 := by rwa [plainDirectType_eq_rootCard R hR ha] at htype
  have htrace : PlainVariablesInTrace ℚ R hv := by
    intro j
    apply hng
    apply plain_PX_mem_augmentation
    intro he
    have he' := congrArg (fun p : PlainExp => p j) he
    simpa using he'
  have hc := plain_hasDirectionalCentres_of_variablesInTrace R hR (by omega) ha hv htrace
  have h4 : (plainBorderFinset R).card=4 := by rw [←hG,hcard,hr]
  obtain ⟨r,u,v,htri,hborder⟩ := plain_three_root_four_border_exact_triangle R ha h3 hv hc h4
  have hGtri : G=plainTriangleBorder r u v := hG.trans hborder
  obtain ⟨P,hP⟩ := triangle_topPattern_of_chosenBase_border D i G r u v hI hGtri (htri ▸ ha) ht
  obtain ⟨T⟩ := exists_two_tail_sources D i P hn
  have sourceMem (e : PlainExp) (t : Fin 3)
      (hs : IsTailSource D i (D.n i+D.tailGen i t))
      (he : tailDegree D i e=D.n i+D.tailGen i t) : e∈plainTriangleBorder r u v := by
    have hmJ := (tail_monomial_mem_chosenBaseDefiningIdeal_iff (k := ℚ) D i e).mpr
      (he ▸ hs.1)
    have heG := source_factorization_eq_displayed_monomial D i G hI hs e he (hI.symm ▸ hmJ)
    exact hGtri ▸ heG
  have sourceNotTop (e : PlainExp) (t : Fin 3)
      (he : tailDegree D i e=D.n i+D.tailGen i t) : e≠plainExp (r+1) (u+1) (v+1) := by
    intro heTop
    apply P.top_ne_base_add_tail t
    rw [hP,←heTop,he]
  have heq := triangle_border_positive_non_top_unique r u v T.selected
    T.first_factorization T.second_factorization
    (sourceMem _ _ T.first_source T.first_degree)
    (sourceMem _ _ T.second_source T.second_degree)
    T.first_contains_selected T.second_contains_selected
    (sourceNotTop _ _ T.first_degree) (sourceNotTop _ _ T.second_degree)
  apply T.degrees_ne
  rw [←T.first_degree,←T.second_degree,heq]

end
end P23.Semigroup
