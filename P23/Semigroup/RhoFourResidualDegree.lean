import P23.Semigroup.RhoFourLocalReduction

/-! Exact actual-degree and Apéry correspondence. No degree injectivity. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.OneTie P23.Presentation
set_option backward.isDefEq.respectTransparency false
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}

def canonicalTailExponent (T : TaggedBudgetOneNormalization D i)
    (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b
      T.presentation.coordinates.c) : Fin 3 →₀ ℕ :=
  (normalExponent p).mapDomain T.presentation.coordinates.sigma.symm

theorem canonicalTailExponent_degree (T : TaggedBudgetOneNormalization D i)
    (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b
      T.presentation.coordinates.c) :
    tailDegree D i (canonicalTailExponent T p) =
      T.presentation.coordinates.coordinateDegree (normalExponent p) := rfl

theorem canonicalTailExponent_rename (T : TaggedBudgetOneNormalization D i)
    (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b
      T.presentation.coordinates.c) :
    (canonicalTailExponent T p).mapDomain T.presentation.coordinates.sigma = normalExponent p := by
  unfold canonicalTailExponent
  have he : T.presentation.coordinates.sigma ∘ T.presentation.coordinates.sigma.symm = id := by
    funext j; simp
  rw [← Finsupp.mapDomain_comp, he, Finsupp.mapDomain_id]

theorem chosenBase_canonical_isApery_iff_standard (T : TaggedBudgetOneNormalization D i)
    (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b
      T.presentation.coordinates.c) :
    D.IsApery i (tailDegreeGamma D i (canonicalTailExponent T p)) ↔
      p ∈ standardSet T.presentation.roots := by
  classical
  let B := T.presentation
  let C := B.coordinates
  let e := canonicalTailExponent T p
  have hm : MvPolynomial.monomial e (1 : ℚ) ∈ chosenBaseDefiningIdeal (k := ℚ) D i ↔
      monomial (k := ℚ) p ∈ normalGeneratorIdeal B.generators := by
    rw [← renamedChosenBaseIdeal_mem_iff C,
      ← normalGeneratorIdeal_comap_of_raw_span C B.rawExponents B.spanEq]
    change polyToNormalAlg (a := C.a) (b := C.b) (c := C.c)
      (renameToOneTie C (MvPolynomial.monomial e (1 : ℚ))) ∈ normalGeneratorIdeal B.generators ↔
        monomial (k := ℚ) p ∈ normalGeneratorIdeal B.generators
    simp only [renameToOneTie, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_monomial,
      polyToNormalAlg_monomial, one_smul]
    rw [show e.mapDomain C.sigma = normalExponent p from canonicalTailExponent_rename T p,
      normalizeExponent_normalExponent]
  have hk : TailInK D i (tailDegree D i e) ↔ p ∉ standardSet B.roots := by
    rw [← tail_monomial_mem_chosenBaseDefiningIdeal_iff (k := ℚ) D i e, hm]
    simpa only [not_not] using not_congr (B.survivor_iff_standard p)
  constructor
  · intro ha
    by_contra hp
    obtain ⟨_,γ,hγ⟩ := hk.mpr hp
    exact ha ⟨γ,Subtype.ext hγ⟩
  · intro hp
    rintro ⟨γ,hγ⟩
    apply hk.mp ⟨⟨e,rfl⟩,γ,congrArg Subtype.val hγ⟩ hp

def canonicalDegree (T : TaggedBudgetOneNormalization D i)
    (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b
      T.presentation.coordinates.c) : ℕ := tailDegree D i (canonicalTailExponent T p)

theorem canonicalDegree_mul (T : TaggedBudgetOneNormalization D i)
    (p q : Normal T.presentation.coordinates.a T.presentation.coordinates.b
      T.presentation.coordinates.c) : canonicalDegree T (p*q) = canonicalDegree T p + canonicalDegree T q := by
  let C := T.presentation.coordinates
  have he : normalizeExponent C.a C.b C.c (normalExponent p + normalExponent q) = p*q := by
    rw [normalizeExponent_add]; simp
  change C.coordinateDegree (normalExponent (p*q)) =
    C.coordinateDegree (normalExponent p) + C.coordinateDegree (normalExponent q)
  rw [←he, C.normalize_preserves_coordinateDegree]
  simp [OneTieCoordinates.coordinateDegree, Finsupp.mapDomain_add, tailDegree_add]

theorem canonicalDegree_one (T : TaggedBudgetOneNormalization D i) : canonicalDegree T 1 = 0 := by
  simp [canonicalDegree,canonicalTailExponent,normalExponent]

theorem canonicalDegree_coordinateGenerator (T : TaggedBudgetOneNormalization D i) (j : Fin 3) :
    canonicalDegree T (coordinateGenerator j) = D.tailGen i (T.presentation.coordinates.sigma.symm j) := by
  have ha : T.presentation.coordinates.a ≠ 1 := by
    have := T.presentation.coordinates.liveDomain.1; omega
  change T.presentation.coordinates.coordinateDegree (normalExponent (coordinateGenerator j)) = _
  rw [T.presentation.coordinates.coordinateDegree_formula]
  fin_cases j <;> simp [coordinateGenerator, Normal.xGenerator, Normal.yGenerator, Normal.zGenerator, ha]

-- A finite product identity in the frozen normal monoid, not finite search.
theorem normal_coordinate_power_product {a b c : ℕ} [NeZero a] (p : Normal a b c) :
    Normal.xGenerator^p.x * Normal.yGenerator^p.y * Normal.zGenerator^p.z = p := by
  have mpow (q : Normal a b c) (n : ℕ) :
      monomial (k := ℚ) q ^ n = monomial (k := ℚ) (q^n) := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ,ih]
  have hx : MvPolynomial.monomial (normalExponent p) (1 : ℚ) =
      polyX^p.x * polyY^p.y * polyZ^p.z := by
    simp [normalExponent,polyX,polyY,polyZ,MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul]
  have hh := polyToNormalAlg_normalExponent (k := ℚ) p
  rw [hx, map_mul, map_mul, map_pow, map_pow, map_pow,
    polyToNormalAlg_polyX, polyToNormalAlg_polyY, polyToNormalAlg_polyZ,
    mpow,mpow,mpow,monomial_mul,monomial_mul] at hh
  exact MonoidAlgebra.single_left_injective (by norm_num : (1 : ℚ) ≠ 0) hh

def residualToTail (R : RhoFourResidualPureBase D i) : Fin 3 ≃ Fin 3 :=
  R.residual.coordinatePermutation.symm.trans R.tagged.presentation.coordinates.sigma.symm

def tailToResidual (R : RhoFourResidualPureBase D i) : Fin 3 ≃ Fin 3 := (residualToTail R).symm

namespace ResidualDegree
variable (R : RhoFourResidualPureBase D i)
local instance : NeZero R.residual.a' := ⟨by have := R.residual.a'_ge_two; omega⟩

def residualTailExponent (p : Normal R.residual.a' R.residual.b' 0) : Fin 3 →₀ ℕ :=
  canonicalTailExponent R.tagged (R.residual.normalCoordinates.symm p)

def residualDegree (p : Normal R.residual.a' R.residual.b' 0) : ℕ :=
  tailDegree D i (residualTailExponent R p)

theorem residualDegree_mul (p q : Normal R.residual.a' R.residual.b' 0) :
    residualDegree R (p*q) = residualDegree R p + residualDegree R q := by
  change canonicalDegree R.tagged (R.residual.normalCoordinates.symm (p*q)) = _
  rw [map_mul,canonicalDegree_mul]
  rfl

theorem residualDegree_one : residualDegree R 1 = 0 := by
  change canonicalDegree R.tagged (R.residual.normalCoordinates.symm 1) = 0
  rw [map_one,canonicalDegree_one]

theorem residualDegree_pow (p : Normal R.residual.a' R.residual.b' 0) (n : ℕ) :
    residualDegree R (p^n) = n * residualDegree R p := by
  induction n with
  | zero => simp [residualDegree_one]
  | succ n ih => rw [pow_succ,residualDegree_mul,ih]; ring

theorem residualDegree_coordinateGenerator (j : Fin 3) :
    residualDegree R (coordinateGenerator j) = D.tailGen i (residualToTail R j) := by
  have he : R.residual.normalCoordinates.symm (coordinateGenerator j) =
      coordinateGenerator (R.residual.coordinatePermutation.symm j) := by
    apply R.residual.normalCoordinates.injective
    rw [MulEquiv.apply_symm_apply,R.residual.variablesCorrespondence]
    simp
  change canonicalDegree R.tagged (R.residual.normalCoordinates.symm (coordinateGenerator j)) = _
  rw [he,canonicalDegree_coordinateGenerator]
  rfl

theorem residualDegree_formula (p : Normal R.residual.a' R.residual.b' 0) :
    residualDegree R p = p.x * D.tailGen i (residualToTail R 0) +
      p.y * D.tailGen i (residualToTail R 1) + p.z * D.tailGen i (residualToTail R 2) := by
  conv_lhs => rw [←normal_coordinate_power_product p]
  rw [residualDegree_mul,residualDegree_mul,
    residualDegree_pow,residualDegree_pow,residualDegree_pow]
  change _ = _
  have h0 := residualDegree_coordinateGenerator R 0
  have h1 := residualDegree_coordinateGenerator R 1
  have h2 := residualDegree_coordinateGenerator R 2
  change residualDegree R Normal.xGenerator = _ at h0
  change residualDegree R Normal.yGenerator = _ at h1
  change residualDegree R Normal.zGenerator = _ at h2
  rw [h0,h1,h2]

theorem residual_weighted_tie :
    R.residual.a' * D.tailGen i (residualToTail R 0) =
      R.residual.b' * D.tailGen i (residualToTail R 1) := by
  have he : (Normal.xGenerator : Normal R.residual.a' R.residual.b' 0)^R.residual.a' =
      Normal.yGenerator^R.residual.b' := by
    -- The tie equality is already true in the frozen normalized monoid.
    have ht := polyToNormalAlg_tiePolynomial (k := ℚ) (a := R.residual.a') (b := R.residual.b') (c := 0)
    simp only [tiePolynomial,map_sub,map_mul,map_pow,pow_zero,map_one,mul_one,
      polyToNormalAlg_polyX,polyToNormalAlg_polyY,sub_eq_zero] at ht
    have mpow (q : Normal R.residual.a' R.residual.b' 0) (n : ℕ) :
        monomial (k := ℚ) q ^ n = monomial (k := ℚ) (q^n) := by
      induction n with
      | zero => simp
      | succ n ih => simp [pow_succ,ih]
    rw [mpow,mpow] at ht
    exact MonoidAlgebra.single_left_injective (by norm_num : (1 : ℚ) ≠ 0) ht
  have hd := congrArg (residualDegree R) he
  rw [residualDegree_pow,residualDegree_pow] at hd
  have h0 := residualDegree_coordinateGenerator R 0
  have h1 := residualDegree_coordinateGenerator R 1
  change residualDegree R Normal.xGenerator = _ at h0
  change residualDegree R Normal.yGenerator = _ at h1
  rwa [h0,h1] at hd

theorem residual_isApery_iff_standard (p : Normal R.residual.a' R.residual.b' 0) :
    D.IsApery i (tailDegreeGamma D i (residualTailExponent R p)) ↔
      p ∈ standardSet R.residual.roots := by
  rw [residualTailExponent,chosenBase_canonical_isApery_iff_standard]
  have he := R.residual.standardCorrespondence (R.residual.normalCoordinates.symm p)
  simpa using he.symm
end ResidualDegree

export ResidualDegree (residualTailExponent residualDegree residualDegree_mul residualDegree_one
  residualDegree_pow residualDegree_coordinateGenerator residualDegree_formula
  residual_weighted_tie residual_isApery_iff_standard)

end
end P23.Semigroup
