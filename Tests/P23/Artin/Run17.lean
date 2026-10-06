import P23.Artin.LocalSocle
import P23.Artin.MixedTraceObstructions
import P23.Artin.PureTraceObstructions

namespace P23.Tests.Run17

open P23.OneTie P23.Artin

#check variableBasis_isNilpotent
#check xBasis_isNilpotent
#check yBasis_isNilpotent
#check zBasis_isNilpotent
#check maximalIdeal_eq_augmentationIdeal
#check directIsLocalRing
#check localMaximalIdeal_eq_augmentationIdeal
#check DirectSocle
#check mem_directSocle_iff_variables
#check root_mul_variable_eq_zero
#check root_X_mem_directSocle
#check monomial_mem_roots_of_mem_directSocle
#check directSocle_eq_rootSpan
#check directSocleBasis
#check directSocle_finrank_eq_card
#check directType
#check directType_eq_rootCard
#check directType_eq_three_iff
#check directNearlyGorenstein_iff_localMaximalIdeal_le_trace
#check DirectLocalArtinStructure
#check directLocalArtinStructure

noncomputable section

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    directType k S hS hdom = S.card :=
  directType_eq_rootCard (k := k) S hS hdom hlive hanti

namespace Concrete

def mixedS : Finset (Normal 3 1 1) :=
  mixedSoclesYZ (a := 3) (b := 1) (c := 1) 0 1 1 (by decide)

theorem mixed_live : IsLiveTie mixedS := by
  simpa [mixedS] using
    (mixedYZ_isLiveTie (a := 3) (u := 1) (v := 1)
      (by decide) (by decide) (by decide))

theorem mixed_anti : IsRootAntichain mixedS := by
  simpa [mixedS] using
    (mixedYZ_isRootAntichain (a := 3) (u := 1) (v := 1)
      (by decide) (by decide) (by decide))

def pureS : Finset (Normal 3 2 0) :=
  p4ZSocles (a := 3) (b := 2) (by decide) 1

theorem pure_live : IsLiveTie pureS := by
  simpa [pureS] using p4Z_isLiveTie (a := 3) (b := 2) (V := 1)
    (by decide) (by decide) (by decide)

theorem pure_anti : IsRootAntichain pureS := by
  simpa [pureS] using p4Z_isRootAntichain (a := 3) (b := 2) (V := 1)
    (by decide) (by decide) (by decide)

def nonprimitiveMixedRoot : Normal 4 2 2 := ⟨0, 2, 2, by decide⟩
def nonprimitiveMixedS : Finset (Normal 4 2 2) := {nonprimitiveMixedRoot}

theorem nonprimitiveMixed_live : IsLiveTie nonprimitiveMixedS := by
  simp [IsLiveTie, standardSet, nonprimitiveMixedS, nonprimitiveMixedRoot,
    liveTiePoint, Normal.exact_divides_iff, Normal.DividesCriterion,
    Normal.xGenerator, Normal.yGenerator, Normal.zGenerator]

theorem nonprimitiveMixed_anti : IsRootAntichain nonprimitiveMixedS := by
  simp [IsRootAntichain, nonprimitiveMixedS]

def nonprimitivePureRoot : Normal 4 2 0 := ⟨0, 2, 1, by decide⟩
def nonprimitivePureS : Finset (Normal 4 2 0) := {nonprimitivePureRoot}

theorem nonprimitivePure_live : IsLiveTie nonprimitivePureS := by
  simp [IsLiveTie, standardSet, nonprimitivePureS, nonprimitivePureRoot,
    liveTiePoint, Normal.exact_divides_iff, Normal.DividesCriterion,
    Normal.xGenerator, Normal.yGenerator, Normal.zGenerator]

theorem nonprimitivePure_anti : IsRootAntichain nonprimitivePureS := by
  simp [IsRootAntichain, nonprimitivePureS]

/- Wrapped powers of x and the ordinary y/z powers are all covered by the
same symbolic finite-weight nilpotence theorem. -/
example : IsNilpotent
    (X (k := ℚ) mixedS Normal.xGenerator
      ((mem_standardFinset_iff_standardSet mixedS _).2 mixed_live.1)) :=
  xBasis_isNilpotent (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live

example : IsNilpotent
    (X (k := ℚ) mixedS Normal.yGenerator
      ((mem_standardFinset_iff_standardSet mixedS _).2 mixed_live.2.1)) :=
  yBasis_isNilpotent (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live

example : IsNilpotent
    (X (k := ℚ) pureS Normal.zGenerator
      ((mem_standardFinset_iff_standardSet pureS _).2 pure_live.2.2.1)) :=
  zBasis_isNilpotent (k := ℚ) pureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ pure_live

example : IsNilpotent
    (X (k := ℚ) nonprimitiveMixedS Normal.xGenerator
      ((mem_standardFinset_iff_standardSet nonprimitiveMixedS _).2
        nonprimitiveMixed_live.1)) :=
  xBasis_isNilpotent (k := ℚ) nonprimitiveMixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ nonprimitiveMixed_live

example : IsNilpotent
    (X (k := ℚ) nonprimitivePureS Normal.zGenerator
      ((mem_standardFinset_iff_standardSet nonprimitivePureS _).2
        nonprimitivePure_live.2.2.1)) :=
  zBasis_isNilpotent (k := ℚ) nonprimitivePureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ nonprimitivePure_live

example (I : Ideal (MonomialArtin ℚ mixedS)) (hI : I.IsMaximal) :
    I = augmentationIdeal (k := ℚ) mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ :=
  maximalIdeal_eq_augmentationIdeal (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live I hI

example :
    letI := directIsLocalRing (k := ℚ) mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live
    IsLocalRing.maximalIdeal (MonomialArtin ℚ mixedS) =
      augmentationIdeal (k := ℚ) mixedS (by decide)
        ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ :=
  localMaximalIdeal_eq_augmentationIdeal (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live

example (s : ↥mixedS) :
    rootBasisVector (k := ℚ) mixedS s ∈
      DirectSocle (k := ℚ) mixedS (by decide)
        ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ :=
  root_X_mem_directSocle (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live mixed_anti s.2

example :
    X (k := ℚ) mixedS 1 (one_mem_standardFinset mixedS (by decide)) ∉
      DirectSocle (k := ℚ) mixedS (by decide)
        ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ := by
  intro h
  have hu := monomial_mem_roots_of_mem_directSocle (k := ℚ) mixedS
    (by decide) ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩
    mixed_live mixed_anti
    ⟨1, one_mem_standardFinset mixedS (by decide)⟩ h
  have : (1 : Normal 3 1 1) ∈ mixedS := hu
  exact (by decide : (1 : Normal 3 1 1) ∉ mixedS) this

example (r s : ↥mixedS) :
    rootBasisVector (k := ℚ) mixedS r + rootBasisVector (k := ℚ) mixedS s ∈
      rootSpan (k := ℚ) mixedS := by
  rw [← directSocle_eq_rootSpan (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live mixed_anti]
  exact (DirectSocle (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩).add_mem
      (root_X_mem_directSocle (k := ℚ) mixedS (by decide)
        ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live mixed_anti r.2)
      (root_X_mem_directSocle (k := ℚ) mixedS (by decide)
        ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live mixed_anti s.2)

example : Module.finrank ℚ
    (DirectSocle (k := ℚ) pureS (by decide)
      ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩) = 3 := by
  rw [directSocle_finrank_eq_card (k := ℚ) pureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ pure_live pure_anti]
  exact p4Z_card_eq_three (by decide) (by decide) (by decide)

example : directType ℚ mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ = 3 ↔ mixedS.card = 3 :=
  directType_eq_three_iff (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live mixed_anti

example : directType ℚ nonprimitiveMixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ = 1 := by
  rw [directType_eq_rootCard (k := ℚ) nonprimitiveMixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩
    nonprimitiveMixed_live nonprimitiveMixed_anti]
  decide

example : DirectNearlyGorenstein ℚ mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ ↔
    (letI := directIsLocalRing (k := ℚ) mixedS (by decide)
       ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live
     IsLocalRing.maximalIdeal (MonomialArtin ℚ mixedS) ≤ TraceSubmodule ℚ mixedS) :=
  directNearlyGorenstein_iff_localMaximalIdeal_le_trace
    (k := ℚ) mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live

end Concrete

end

end P23.Tests.Run17
