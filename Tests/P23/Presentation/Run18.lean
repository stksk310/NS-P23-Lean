import P23.Presentation.QuotientLocalSocle
import P23.Presentation.QuotientDualTrace

open P23.OneTie P23.Artin P23.Presentation

#check quotientIsLocalRing
#check quotientAugmentationIdeal
#check quotientMaximalIdeal_eq_augmentationIdeal
#check quotientMaximalIdeal_mem_iff
#check QuotientSocle
#check mem_quotientSocle_iff_equiv_mem_directSocle
#check quotientSocleEquivDirectSocle
#check quotientSocle_finrank_eq_card
#check quotientType
#check quotientType_eq_rootCard
#check quotientType_eq_three_iff
#check QuotientOmega
#check quotientOmegaEquivDirectOmega
#check quotientOmegaEquivDirectOmega_apply_equiv
#check quotientOmegaEquivDirectOmega_smul
#check pushCanonicalHom
#check pullCanonicalHom
#check pull_pushCanonicalHom
#check push_pullCanonicalHom
#check QuotientTraceSubmodule
#check mem_quotientTrace_iff_equiv_mem_directTrace
#check QuotientNearlyGorenstein
#check quotientNearlyGorenstein_iff_directNearlyGorenstein
#check FiniteQuotientArtinTransport
#check finiteQuotientArtinTransport

namespace P23.Tests.Run18

noncomputable section

open P23.OneTie P23.Artin P23.Presentation

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    IsLocalRing (FinitePolynomialQuotient k S) :=
  quotientIsLocalRing (k := k) S hS hdom hlive

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (q : FinitePolynomialQuotient k S) :
    letI := quotientIsLocalRing (k := k) S hS hdom hlive
    q ∈ IsLocalRing.maximalIdeal (FinitePolynomialQuotient k S) ↔
      finitePolynomialQuotientEquiv (k := k) S hS hdom q ∈
        augmentationIdeal (k := k) S hS hdom :=
  quotientMaximalIdeal_mem_iff (k := k) S hS hdom hlive q

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (φ : QuotientOmega k S)
    (q : FinitePolynomialQuotient k S) :
    quotientOmegaEquivDirectOmega (k := k) S hS hdom φ
        (finitePolynomialQuotientEquiv (k := k) S hS hdom q) = φ q :=
  quotientOmegaEquivDirectOmega_apply_equiv (k := k) S hS hdom φ q

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c)
    (F : QuotientOmega k S →ₗ[FinitePolynomialQuotient k S]
      FinitePolynomialQuotient k S) :
    pullCanonicalHom (k := k) S hS hdom
      (pushCanonicalHom (k := k) S hS hdom F) = F :=
  pull_pushCanonicalHom (k := k) S hS hdom F

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c)
    (q : FinitePolynomialQuotient k S) :
    q ∈ QuotientTraceSubmodule k S ↔
      finitePolynomialQuotientEquiv (k := k) S hS hdom q ∈
        TraceSubmodule k S :=
  mem_quotientTrace_iff_equiv_mem_directTrace (k := k) S hS hdom q

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

example : quotientType ℚ mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live = 3 := by
  rw [quotientType_eq_rootCard (k := ℚ) mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live mixed_anti]
  decide

example : quotientType ℚ pureS (by decide)
      ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ pure_live = 3 := by
  rw [quotientType_eq_rootCard (k := ℚ) pureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ pure_live pure_anti]
  exact p4Z_card_eq_three (by decide) (by decide) (by decide)

example : quotientType ℚ nonprimitiveMixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ nonprimitiveMixed_live = 1 := by
  rw [quotientType_eq_rootCard (k := ℚ) nonprimitiveMixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩
    nonprimitiveMixed_live nonprimitiveMixed_anti]
  decide

example : quotientType ℚ nonprimitivePureS (by decide)
      ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ nonprimitivePure_live = 1 := by
  rw [quotientType_eq_rootCard (k := ℚ) nonprimitivePureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩
    nonprimitivePure_live nonprimitivePure_anti]
  decide

example (s : ↥mixedS) :
    (finitePolynomialQuotientEquiv (k := ℚ) mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩).symm
        (rootBasisVector (k := ℚ) mixedS s) ∈
      QuotientSocle (k := ℚ) mixedS (by decide)
        ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live := by
  apply (mem_quotientSocle_iff_equiv_mem_directSocle
    (k := ℚ) mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live _).2
  simpa [rootBasisVector] using
    root_X_mem_directSocle (k := ℚ) mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live mixed_anti s.2

example : QuotientNearlyGorenstein ℚ mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live ↔
    DirectNearlyGorenstein ℚ mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ :=
  quotientNearlyGorenstein_iff_directNearlyGorenstein
    (k := ℚ) mixedS (by decide)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixed_live

end Concrete

end


end P23.Tests.Run18

