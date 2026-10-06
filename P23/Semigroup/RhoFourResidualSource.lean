import P23.Semigroup.RhoFourResidualTop

/-! Source selection through the actual tail kernel. Normalization need not preserve support. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.OneTie P23.Presentation
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}

def canonicalSourceNormal (T : TaggedBudgetOneNormalization D i) (u : Fin 3 →₀ ℕ) :
    Normal T.presentation.coordinates.a T.presentation.coordinates.b T.presentation.coordinates.c :=
  normalizeExponent _ _ _ (u.mapDomain T.presentation.coordinates.sigma)

theorem canonicalSourceNormal_degree (T : TaggedBudgetOneNormalization D i) (u : Fin 3 →₀ ℕ) :
    canonicalDegree T (canonicalSourceNormal T u) = tailDegree D i u := by
  change T.presentation.coordinates.coordinateDegree (normalExponent
    (normalizeExponent _ _ _ (u.mapDomain T.presentation.coordinates.sigma))) = _
  rw [T.presentation.coordinates.normalize_preserves_coordinateDegree,
    T.presentation.coordinates.coordinateDegree_rename]

theorem canonical_tailInK_iff_not_standard (T : TaggedBudgetOneNormalization D i)
    (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b T.presentation.coordinates.c) :
    TailInK D i (canonicalDegree T p) ↔ p ∉ standardSet T.presentation.roots := by
  constructor
  · rintro ⟨_,g,hg⟩ hp
    exact (chosenBase_canonical_isApery_iff_standard T p).mpr hp ⟨g,Subtype.ext hg⟩
  · intro hp
    have hn := mt (chosenBase_canonical_isApery_iff_standard T p).mp hp
    obtain ⟨g,hg⟩ := not_not.mp hn
    exact ⟨⟨canonicalTailExponent T p,rfl⟩,g,congrArg Subtype.val hg⟩

theorem canonicalDegree_positive_of_ne_one (T : TaggedBudgetOneNormalization D i)
    (p : Normal T.presentation.coordinates.a T.presentation.coordinates.b T.presentation.coordinates.c)
    (hp : p ≠ 1) : 0 < canonicalDegree T p := by
  apply tailDegree_pos_of_ne_zero
  intro he
  have hh := canonicalTailExponent_rename T p
  rw [he,Finsupp.mapDomain_zero] at hh
  apply hp
  apply Normal.ext
  · have h := congrArg (fun e : Fin 3 →₀ ℕ => e 0) hh
    simpa using h.symm
  · have h := congrArg (fun e : Fin 3 →₀ ℕ => e 1) hh
    simpa using h.symm
  · have h := congrArg (fun e : Fin 3 →₀ ℕ => e 2) hh
    simpa using h.symm

theorem source_normal_mem_original_border (T : TaggedBudgetOneNormalization D i)
    {d : ℕ} (hs : IsTailSource D i d) (u : Fin 3 →₀ ℕ) (hu : tailDegree D i u=d) :
    canonicalSourceNormal T u ∈ borderFinset T.presentation.roots := by
  let p := canonicalSourceNormal T u
  have hpdeg : canonicalDegree T p=d := (canonicalSourceNormal_degree T u).trans hu
  have hp : p ∉ standardSet T.presentation.roots :=
    (canonical_tailInK_iff_not_standard T p).mp (hpdeg.symm ▸ hs.1)
  obtain ⟨g,hg,hgp⟩ := killed_has_border_divisor T.presentation.roots
    T.presentation.roots_nonempty T.presentation.coordinates.liveDomain p hp
  by_cases he : g=p
  · change p ∈ borderFinset T.presentation.roots
    exact he ▸ hg
  obtain ⟨r,hr⟩ := hgp
  have hr1 : r ≠ 1 := by intro h; apply he; simpa [h] using hr.symm
  have hgk : TailInK D i (canonicalDegree T g) :=
    (canonical_tailInK_iff_not_standard T g).mpr
      ((mem_borderFinset_iff T.presentation.roots_nonempty g).mp hg).1
  have hpos := canonicalDegree_positive_of_ne_one T r hr1
  have hsum : d = canonicalDegree T g + canonicalDegree T r := by
    rw [←hpdeg,hr,canonicalDegree_mul]
  exact False.elim ((isTailSource_iff_no_nonzero_tail_predecessor D i d).mp hs |>.2
    ⟨canonicalDegree T g,canonicalDegree T r,hgk,⟨canonicalTailExponent T r,rfl⟩,
      Nat.ne_of_gt hpos,hsum⟩)

theorem source_normal_external_tag (T : TaggedBudgetOneNormalization D i)
    {d : ℕ} (hs : IsTailSource D i d) (u : Fin 3 →₀ ℕ) (hu : tailDegree D i u=d) :
    ∃ g ∈ T.externalTags, T.normalizedOfExternal g=canonicalSourceNormal T u ∧
      ∀ h ∈ T.externalTags, T.normalizedOfExternal h=canonicalSourceNormal T u → h=g := by
  classical
  have hp := source_normal_mem_original_border T hs u hu
  rw [←T.external_image_exact_border] at hp
  obtain ⟨g,hg,hgp⟩ := Finset.mem_image.mp hp
  refine ⟨g,hg,hgp,?_⟩
  intro h hh hhp
  exact T.normalized_external_injective hh hg (hhp.trans hgp.symm)

namespace ResidualSource
variable (R : RhoFourResidualPureBase D i)
local instance : NeZero R.residual.a' := ⟨by have := R.residual.a'_ge_two; omega⟩
def residualSourceNormal (u : Fin 3 →₀ ℕ) : Normal R.residual.a' R.residual.b' 0 :=
  R.residual.normalCoordinates (canonicalSourceNormal R.tagged u)
theorem residualSourceNormal_degree (u : Fin 3 →₀ ℕ) :
    residualDegree R (residualSourceNormal R u) = tailDegree D i u := by
  change canonicalDegree R.tagged (R.residual.normalCoordinates.symm
    (R.residual.normalCoordinates (canonicalSourceNormal R.tagged u))) = _
  rw [MulEquiv.symm_apply_apply,canonicalSourceNormal_degree]

private theorem transport_minimal {M N : Type*} [CommMonoid M] [CommMonoid N]
    (E : M ≃* N) (O : Set M) (P : Set N) (hc : ∀ p, E p ∈ P ↔ p ∈ O)
    (m : M) (hm : m ∉ O ∧ ∀ d, d ∣ m → d ≠ m → d ∈ O) :
    E m ∉ P ∧ ∀ d, d ∣ E m → d ≠ E m → d ∈ P := by
  refine ⟨fun h => hm.1 ((hc m).mp h),?_⟩
  intro d hd hn
  have hdiv : E.symm d ∣ m := by
    obtain ⟨q,hq⟩ := hd
    refine ⟨E.symm q,?_⟩
    have hh := congrArg E.symm hq
    simpa [IsDivisibilityMinimalKilled] using hh
  have hne : E.symm d ≠ m := by intro he; apply hn; simpa using congrArg E he
  have hh := (hc (E.symm d)).mpr (hm.2 _ hdiv hne)
  simpa using hh

theorem residual_border_correspondence
    (p : Normal R.tagged.presentation.coordinates.a R.tagged.presentation.coordinates.b
      R.tagged.presentation.coordinates.c) :
    R.residual.normalCoordinates p ∈ borderFinset R.residual.roots ↔
      p ∈ borderFinset R.tagged.presentation.roots := by
  rw [mem_borderFinset_iff R.residual.nonempty,
    mem_borderFinset_iff R.tagged.presentation.roots_nonempty,
    isMinimalBorder_iff_isDivisibilityMinimalKilled _ _
      (variableGenerators_ne_one_of_two_le R.residual.a'_ge_two),
    isMinimalBorder_iff_isDivisibilityMinimalKilled _ _
      (variableGenerators_ne_one_of_two_le R.tagged.presentation.coordinates.liveDomain.1)]
  constructor
  · intro hp
    have hc (q) : R.residual.normalCoordinates.symm q ∈ standardSet R.tagged.presentation.roots ↔
        q ∈ standardSet R.residual.roots := by
      simpa using (R.residual.standardCorrespondence (R.residual.normalCoordinates.symm q)).symm
    have hh := transport_minimal R.residual.normalCoordinates.symm _ _ hc _ hp
    simpa [IsDivisibilityMinimalKilled] using hh
  · intro hp
    exact transport_minimal R.residual.normalCoordinates _ _ R.residual.standardCorrespondence p hp

theorem residualSourceNormal_mem_border {d : ℕ} (hs : IsTailSource D i d)
    (u : Fin 3 →₀ ℕ) (hu : tailDegree D i u=d) :
    residualSourceNormal R u ∈ borderFinset R.residual.roots :=
  (residual_border_correspondence R _).mpr (source_normal_mem_original_border R.tagged hs u hu)

theorem residualSourceNormal_add (u v : Fin 3 →₀ ℕ) :
    residualSourceNormal R (u+v) = residualSourceNormal R u * residualSourceNormal R v := by
  simp only [residualSourceNormal,canonicalSourceNormal,Finsupp.mapDomain_add,
    normalizeExponent_add,map_mul]

theorem residualSourceNormal_single (j : Fin 3) :
    residualSourceNormal R (Finsupp.single j 1) = coordinateGenerator (tailToResidual R j) := by
  have hg (l : Fin 3) : normalizeExponent R.tagged.presentation.coordinates.a
      R.tagged.presentation.coordinates.b R.tagged.presentation.coordinates.c
      (Finsupp.single l 1) = coordinateGenerator l := by
    fin_cases l <;> simp [coordinateGenerator]
  simp only [residualSourceNormal,canonicalSourceNormal,Finsupp.mapDomain_single,hg,
    R.residual.variablesCorrespondence]
  rfl

private theorem generator_mul_support (j : Fin 3)
    (q : Normal R.residual.a' R.residual.b' 0) :
    if j=2 then 0 < (coordinateGenerator j * q).z else
      0 < (coordinateGenerator j * q).x ∨ 0 < (coordinateGenerator j * q).y := by
  have ha := R.residual.a'_ge_two
  have hb := R.residual.b'_ge_two
  have ha1 : R.residual.a' ≠ 1 := by omega
  fin_cases j
  · simp only [coordinateGenerator,ite_true]
    change 0 < (Normal.xGenerator*q).x ∨ 0 < (Normal.xGenerator*q).y
    simp only [Normal.mul_x,Normal.mul_y,Normal.xGenerator,dif_neg ha1,zero_add]
    change 0 < (1+q.x)%R.residual.a' ∨
      0 < q.y + ((1+q.x)/R.residual.a')*R.residual.b'
    by_cases hd : (1+q.x)/R.residual.a'=0
    · left
      have hh := Nat.mod_add_div (1+q.x) R.residual.a'
      rw [hd] at hh
      omega
    · right
      have hpos : 0 < ((1+q.x)/R.residual.a')*R.residual.b' :=
        Nat.mul_pos (Nat.pos_of_ne_zero hd) (by omega)
      omega
  · simp [coordinateGenerator,Normal.mul_y,Normal.yGenerator]
  · simp [coordinateGenerator,Normal.mul_z,Normal.zGenerator]

theorem residualSourceNormal_selected_support (u : Fin 3 →₀ ℕ) (j : Fin 3)
    (hj : 0 < u j) :
    if tailToResidual R j=2 then 0 < (residualSourceNormal R u).z else
      0 < (residualSourceNormal R u).x ∨ 0 < (residualSourceNormal R u).y := by
  classical
  have hle : Finsupp.single j 1 ≤ u := by
    intro l
    by_cases hl : j=l
    · subst l; simp; omega
    · simp [Finsupp.single_apply,hl]
  have he : u = Finsupp.single j 1 + (u-Finsupp.single j 1) := by
    exact (add_tsub_cancel_of_le hle).symm
  rw [he,residualSourceNormal_add,residualSourceNormal_single]
  exact generator_mul_support R (tailToResidual R j) _
end ResidualSource
export ResidualSource (residualSourceNormal residualSourceNormal_degree
  residual_border_correspondence residualSourceNormal_mem_border residualSourceNormal_add
  residualSourceNormal_single residualSourceNormal_selected_support)
end
end P23.Semigroup
