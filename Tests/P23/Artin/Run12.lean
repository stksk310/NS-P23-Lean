import P23.Artin.MaximalIdealTrace

namespace P23.Tests.Run12

open P23 OneTie Artin

noncomputable section

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

#check constantCoeffAlgHom
#check augmentationIdeal
#check augmentationIdeal_isMaximal
#check variableIdeal
#check X_mem_variableIdeal_of_ne_one
#check variableIdeal_eq_augmentationIdeal
#check DirectNearlyGorenstein
#check directNearlyGorenstein_iff_variablesInTrace
#check mixed_directModel_HL5_of_nearlyGorenstein
#check pure_directModel_HL5_of_nearlyGorenstein
#check directNearlyGorenstein_HL5

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (u v : MonomialArtin k S) :
    constantCoeffAlgHom (k := k) S hS hdom (u * v) =
      constantCoeffAlgHom (k := k) S hS hdom u *
        constantCoeffAlgHom (k := k) S hS hdom v := by
  exact map_mul _ _ _

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (v : MonomialArtin k S) :
    v ∈ augmentationIdeal (k := k) S hS hdom ↔
      constantCoeff (k := k) S hS v = 0 :=
  mem_augmentationIdeal_iff (k := k) S hS hdom v

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) :
    (augmentationIdeal (k := k) S hS hdom).IsMaximal :=
  augmentationIdeal_isMaximal (k := k) S hS hdom

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    variableIdeal (k := k) S hlive = augmentationIdeal (k := k) S hS hdom :=
  variableIdeal_eq_augmentationIdeal (k := k) S hS hdom hlive

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    DirectNearlyGorenstein k S hS hdom ↔ VariablesInTrace k S hlive :=
  directNearlyGorenstein_iff_variablesInTrace (k := k) S hS hdom hlive

example (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S)
    (hng : DirectNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩) :
    (borderFinset S).card ≠ 4 :=
  mixed_directModel_HL5_of_nearlyGorenstein
    (k := k) S ha hb hc hcard hlive hanti hng

example (S : Finset (Normal a b 0)) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S)
    (hng : DirectNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩) :
    (borderFinset S).card ≠ 4 :=
  pure_directModel_HL5_of_nearlyGorenstein
    (k := k) S ha hb hcard hlive hanti hng

namespace ConcreteRegression

def mixedR₁ : Normal 3 2 1 := ⟨2, 2, 0, by decide⟩
def mixedR₂ : Normal 3 2 1 := ⟨1, 0, 2, by decide⟩
def mixedR₃ : Normal 3 2 1 := ⟨0, 3, 1, by decide⟩
def mixedS : Finset (Normal 3 2 1) := {mixedR₁, mixedR₂, mixedR₃}

theorem mixedS_live : IsLiveTie mixedS := by
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨mixedR₁, by simp [mixedS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, mixedR₁, Normal.xGenerator]⟩
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨mixedR₁, by simp [mixedS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, mixedR₁, Normal.yGenerator]⟩
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨mixedR₂, by simp [mixedS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, mixedR₂, Normal.zGenerator]⟩
  · rw [mem_standardSet_iff]
    exact ⟨mixedR₃, by simp [mixedS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, mixedR₃, liveTiePoint]⟩

def pureR₁ : Normal 4 2 0 := ⟨0, 2, 0, by decide⟩
def pureR₂ : Normal 4 2 0 := ⟨0, 0, 1, by decide⟩
def pureR₃ : Normal 4 2 0 := ⟨3, 1, 1, by decide⟩
def pureS : Finset (Normal 4 2 0) := {pureR₁, pureR₂, pureR₃}

theorem pureS_live : IsLiveTie pureS := by
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨pureR₁, by simp [pureS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, pureR₁, Normal.xGenerator]⟩
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨pureR₁, by simp [pureS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, pureR₁, Normal.yGenerator]⟩
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨pureR₂, by simp [pureS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, pureR₂, Normal.zGenerator]⟩
  · rw [mem_standardSet_iff]
    exact ⟨pureR₁, by simp [pureS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, pureR₁, liveTiePoint]⟩

def nonprimitiveMixedRoot : Normal 4 2 2 := ⟨0, 2, 2, by decide⟩
def nonprimitiveMixedS : Finset (Normal 4 2 2) := {nonprimitiveMixedRoot}

theorem nonprimitiveMixed_live : IsLiveTie nonprimitiveMixedS := by
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨nonprimitiveMixedRoot, by simp [nonprimitiveMixedS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, nonprimitiveMixedRoot, Normal.xGenerator]⟩
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨nonprimitiveMixedRoot, by simp [nonprimitiveMixedS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, nonprimitiveMixedRoot, Normal.yGenerator]⟩
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨nonprimitiveMixedRoot, by simp [nonprimitiveMixedS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, nonprimitiveMixedRoot, Normal.zGenerator]⟩
  · rw [mem_standardSet_iff]
    exact ⟨nonprimitiveMixedRoot, by simp [nonprimitiveMixedS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, nonprimitiveMixedRoot, liveTiePoint]⟩

def nonprimitivePureRoot : Normal 4 2 0 := ⟨0, 2, 0, by decide⟩
def nonprimitivePureZ : Normal 4 2 0 := ⟨0, 0, 1, by decide⟩
def nonprimitivePureS : Finset (Normal 4 2 0) :=
  {nonprimitivePureRoot, nonprimitivePureZ}

theorem nonprimitivePure_live : IsLiveTie nonprimitivePureS := by
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨nonprimitivePureRoot, by simp [nonprimitivePureS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, nonprimitivePureRoot, Normal.xGenerator]⟩
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨nonprimitivePureRoot, by simp [nonprimitivePureS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, nonprimitivePureRoot, Normal.yGenerator]⟩
  constructor
  · rw [mem_standardSet_iff]
    exact ⟨nonprimitivePureZ, by simp [nonprimitivePureS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, nonprimitivePureZ, Normal.zGenerator]⟩
  · rw [mem_standardSet_iff]
    exact ⟨nonprimitivePureRoot, by simp [nonprimitivePureS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, nonprimitivePureRoot, liveTiePoint]⟩

example (u v : MonomialArtin ℚ mixedS) :
    constantCoeffAlgHom (k := ℚ) mixedS (by decide)
        ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ (u * v) =
      constantCoeffAlgHom (k := ℚ) mixedS (by decide)
          ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ u *
        constantCoeffAlgHom (k := ℚ) mixedS (by decide)
          ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ v := by
  exact map_mul _ _ _

example :
    X (k := ℚ) mixedS Normal.xGenerator
        ((mem_standardFinset_iff_standardSet mixedS _).2 mixedS_live.1) ∈
      augmentationIdeal (k := ℚ) mixedS (by decide)
        ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ :=
  X_variable_mem_augmentationIdeal (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixedS_live .x

def mixedX2 : Normal 3 2 1 := ⟨2, 0, 0, by decide⟩

example : X (k := ℚ) mixedS mixedX2 (by decide) ∈
    variableIdeal (k := ℚ) mixedS mixedS_live :=
  X_mem_variableIdeal_of_ne_one (k := ℚ) mixedS mixedS_live mixedX2
    (by decide) (by decide)

example (hS : mixedS.Nonempty) (v : MonomialArtin ℚ mixedS)
    (hv0 : constantCoeff (k := ℚ) mixedS hS v = 0) :
    v ∈ variableIdeal (k := ℚ) mixedS mixedS_live := by
  apply augmentationIdeal_le_variableIdeal (k := ℚ) mixedS hS
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixedS_live
  exact (mem_augmentationIdeal_iff (k := ℚ) mixedS hS
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ v).2 hv0

example : variableIdeal (k := ℚ) pureS pureS_live =
    augmentationIdeal (k := ℚ) pureS (by decide)
      ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ :=
  variableIdeal_eq_augmentationIdeal (k := ℚ) pureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ pureS_live

example : variableIdeal (k := ℚ) nonprimitiveMixedS nonprimitiveMixed_live =
    augmentationIdeal (k := ℚ) nonprimitiveMixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ :=
  variableIdeal_eq_augmentationIdeal (k := ℚ) nonprimitiveMixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ nonprimitiveMixed_live

example : variableIdeal (k := ℚ) nonprimitivePureS nonprimitivePure_live =
    augmentationIdeal (k := ℚ) nonprimitivePureS (by decide)
      ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ :=
  variableIdeal_eq_augmentationIdeal (k := ℚ) nonprimitivePureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ nonprimitivePure_live

example
    (hng : DirectNearlyGorenstein ℚ mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩) :
    VariablesInTrace ℚ mixedS mixedS_live :=
  (directNearlyGorenstein_iff_variablesInTrace (k := ℚ) mixedS
    (by decide) ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixedS_live).1 hng

example
    (htrace : VariablesInTrace ℚ pureS pureS_live) :
    DirectNearlyGorenstein ℚ pureS (by decide)
      ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ :=
  (directNearlyGorenstein_iff_variablesInTrace (k := ℚ) pureS
    (by decide) ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ pureS_live).2 htrace

end ConcreteRegression

end

end P23.Tests.Run12
