import P23.Presentation.KernelMinimality
import P23.Artin.MixedTraceObstructions
import P23.Artin.PureTraceObstructions

open P23.OneTie
open P23.Presentation

#check polyVariableIdeal_eq_span_variables
#check presentationGeneratorFinset_card
#check presentationRelationSpace_finrank
#check finitePresentationIdeal_generator_card_lower_bound
#check finitePresentationIdeal_minimalGeneratorCard
#check polyToDirectAlg_kernel_minimalGeneratorCard
#check polyToDirectAlg_kernel_mu_eq_one_add_borderCard
#check kernel_mu_eq_five_iff_border_card_eq_four
#check polynomialKernelBorderCount

namespace P23.Presentation.Run16Test

open P23.OneTie P23.Artin

section Symbolic

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

example (S : Finset (Normal a b c)) (hdom : IsLiveParameterDomain a b c) :
    relationDetector (k := k) S (tiePolynomial (k := k) a b c) none = 1 :=
  relationDetector_tie_none S hdom

example (S : Finset (Normal a b c)) (g : ↥(borderFinset S)) :
    relationDetector (k := k) S (polynomialLift (k := k) g.1) (some g) = 1 := by
  simpa using relationDetector_lift_some (k := k) S g g

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (f : ThreePoly k) (hf : f ∈ presentationGeneratorFinset (k := k) S) :
    relationDetector (k := k) S (polyX * f) = 0 :=
  relationDetector_mul_presentationGenerator_eq_zero
    S hS hdom hlive polyX polyX_mem_polyVariableIdeal f hf

noncomputable def alternativeGeneratorFinset
    (S : Finset (Normal a b c)) : Finset (ThreePoly k) := by
  classical
  exact insert 0 (presentationGeneratorFinset (k := k) S)

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    1 + (borderFinset S).card ≤
      (alternativeGeneratorFinset (k := k) S).card := by
  apply finitePresentationIdeal_generator_card_lower_bound
    (k := k) S hS hdom hlive
  simp [alternativeGeneratorFinset, span_presentationGeneratorFinset (k := k) S]

end Symbolic

namespace Concrete

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

def mixedFourS : Finset (Normal 3 1 1) :=
  mixedSoclesYZ (a := 3) (b := 1) (c := 1) 0 1 1 (by decide)

def pureFourS : Finset (Normal 3 2 0) :=
  p4ZSocles (a := 3) (b := 2) (by decide) 1

theorem mixedFourS_live : IsLiveTie mixedFourS := by
  simpa [mixedFourS] using
    (P23.Artin.mixedYZ_isLiveTie (a := 3) (u := 1) (v := 1)
      (by decide) (by decide) (by decide))

theorem pureFourS_live : IsLiveTie pureFourS := by
  exact P23.Artin.p4Z_isLiveTie (by decide) (by decide) (by decide)

theorem mixedFourS_border_card : (borderFinset mixedFourS).card = 4 := by
  rw [show mixedFourS =
      mixedSoclesYZ (a := 3) (b := 1) (c := 1) 0 1 1 (by decide) by rfl]
  rw [mixedBorderYZ_card (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  decide

theorem pureFourS_border_card : (borderFinset pureFourS).card = 4 := by
  exact p4Z_border_card (by decide) (by decide) (by decide)

example : idealGeneratorMu (k := ℚ)
    (RingHom.ker (polyToDirectAlg (k := ℚ) mixedFourS).toRingHom) = 5 := by
  rw [polyToDirectAlg_kernel_mu_eq_one_add_borderCard mixedFourS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixedFourS_live,
    mixedFourS_border_card]

example : idealGeneratorMu (k := ℚ)
    (RingHom.ker (polyToDirectAlg (k := ℚ) pureFourS).toRingHom) = 5 := by
  rw [polyToDirectAlg_kernel_mu_eq_one_add_borderCard pureFourS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ pureFourS_live,
    pureFourS_border_card]

example : idealGeneratorMu (k := ℚ)
    (RingHom.ker (polyToDirectAlg (k := ℚ) nonprimitiveMixedS).toRingHom) =
      1 + (borderFinset nonprimitiveMixedS).card :=
  polyToDirectAlg_kernel_mu_eq_one_add_borderCard nonprimitiveMixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ nonprimitiveMixed_live

example : idealGeneratorMu (k := ℚ)
    (RingHom.ker (polyToDirectAlg (k := ℚ) nonprimitivePureS).toRingHom) =
      1 + (borderFinset nonprimitivePureS).card :=
  polyToDirectAlg_kernel_mu_eq_one_add_borderCard nonprimitivePureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ nonprimitivePure_live

example : idealGeneratorMu (k := ℚ)
      (RingHom.ker (polyToDirectAlg (k := ℚ) mixedFourS).toRingHom) = 5 ↔
    (borderFinset mixedFourS).card = 4 :=
  kernel_mu_eq_five_iff_border_card_eq_four mixedFourS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixedFourS_live

end Concrete

end P23.Presentation.Run16Test

