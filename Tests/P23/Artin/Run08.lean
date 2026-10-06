import P23.Artin.Trace

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {a b c : ℕ} [NeZero a]
variable {k : Type*} [Field k]

example (S : Finset (Normal a b c)) (p q : MonomialIndex S) :
    coeffAt (k := k) S p (X (k := k) S q.1 q.2) = if p = q then 1 else 0 :=
  coeffAt_X (k := k) S p q

example (S : Finset (Normal a b c)) (hS : S.Nonempty) :
    constantCoeff (k := k) S hS 1 = 1 :=
  constantCoeff_one (k := k) S hS

example (S : Finset (Normal a b c)) (m e t : MonomialIndex S)
    (h : m.1 * e.1 = t.1) (v : MonomialArtin k S) :
    coeffAt (k := k) S t (X (k := k) S m.1 m.2 * v) =
      coeffAt (k := k) S e v :=
  coeffAt_X_mul (k := k) S m e t h v

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : 2 ≤ a ∧ ((1 ≤ b ∧ 1 ≤ c) ∨ (2 ≤ b ∧ c = 0)))
    (u v : MonomialArtin k S) :
    constantCoeff (k := k) S hS (u * v) =
      constantCoeff (k := k) S hS u * constantCoeff (k := k) S hS v :=
  constantCoeff_mul (k := k) S hS hdom u v

example (e : Direction) (p q : Normal a b c)
    (hdom : 2 ≤ a ∧ ((1 ≤ b ∧ 1 ≤ c) ∨ (2 ≤ b ∧ c = 0)))
    (h : p * q = e.generator) : p = 1 ∨ q = 1 :=
  variableGenerator_is_atom hdom e p q h

example (S : Finset (Normal a b c)) :
    TraceSubmodule k S =
      ⨆ F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S, F.range := rfl

example (S : Finset (Normal a b c)) :
    TraceSubmodule k S =
      Submodule.span (MonomialArtin k S) (rootTraceValueSet k S) :=
  trace_eq_span_rootTraceValueSet (k := k) S

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (s : Normal a b c) (hs : s ∈ S) :
    constantCoeff (k := k) S hS (F (U (k := k) S (rootIndex S s hs))) = 0 :=
  rootTraceValue_constantCoeff_eq_zero (k := k) S hS hcard hanti F s hs

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : 2 ≤ a ∧ ((1 ≤ b ∧ 1 ≤ c) ∨ (2 ≤ b ∧ c = 0)))
    (hlive : IsLiveTie S) :
    VariablesInTrace k S hlive →
      VariableTraceSources k S hlive :=
  variableTraceSources_of_variablesInTrace (k := k) S hS hcard hanti hdom hlive

namespace ConcreteRegression

def mixedR₁ : Normal 3 2 1 := ⟨2, 2, 0, by decide⟩
def mixedR₂ : Normal 3 2 1 := ⟨1, 0, 2, by decide⟩
def mixedR₃ : Normal 3 2 1 := ⟨0, 3, 1, by decide⟩
def mixedS : Finset (Normal 3 2 1) := {mixedR₁, mixedR₂, mixedR₃}

example : mixedS.Nonempty := by decide
example : 2 ≤ mixedS.card := by decide

theorem mixedS_antichain : IsRootAntichain mixedS := by
  intro p hp q hq hne hd
  simp [mixedS] at hp hq
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
    subst p <;> subst q <;> try { exact (hne rfl).elim }
  all_goals
    rw [exact_divides_iff] at hd
    simp [Normal.DividesCriterion, mixedR₁, mixedR₂, mixedR₃] at hd

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
      simp [Normal.DividesCriterion, liveTiePoint, mixedR₃]⟩

example (F : Omega ℚ mixedS →ₗ[MonomialArtin ℚ mixedS] MonomialArtin ℚ mixedS) :
    constantCoeff (k := ℚ) mixedS (by decide)
      (F (U (k := ℚ) mixedS (rootIndex mixedS mixedR₁ (by decide)))) = 0 :=
  rootTraceValue_constantCoeff_eq_zero (k := ℚ) mixedS (by decide)
    (by decide) mixedS_antichain F mixedR₁ (by decide)

example
    (hx : X (k := ℚ) mixedS Normal.xGenerator
      ((mem_standardFinset_iff_standardSet mixedS _).2 mixedS_live.1) ∈
        TraceSubmodule ℚ mixedS) :
    ∃ (F : Omega ℚ mixedS →ₗ[MonomialArtin ℚ mixedS] MonomialArtin ℚ mixedS)
      (s : Normal 3 2 1) (hs : s ∈ mixedS),
      coeffAt (k := ℚ) mixedS
        ⟨Normal.xGenerator, (mem_standardFinset_iff_standardSet mixedS _).2 mixedS_live.1⟩
        (F (U (k := ℚ) mixedS (rootIndex mixedS s hs))) ≠ 0 :=
  exists_root_image_with_x_coeff_of_mem_trace (k := ℚ) mixedS (by decide)
    (by decide) mixedS_antichain
    (by exact ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩) mixedS_live hx

example
    (hy : X (k := ℚ) mixedS Normal.yGenerator
      ((mem_standardFinset_iff_standardSet mixedS _).2 mixedS_live.2.1) ∈
        TraceSubmodule ℚ mixedS) :
    ∃ (F : Omega ℚ mixedS →ₗ[MonomialArtin ℚ mixedS] MonomialArtin ℚ mixedS)
      (s : Normal 3 2 1) (hs : s ∈ mixedS),
      coeffAt (k := ℚ) mixedS
        ⟨Normal.yGenerator,
          (mem_standardFinset_iff_standardSet mixedS _).2 mixedS_live.2.1⟩
        (F (U (k := ℚ) mixedS (rootIndex mixedS s hs))) ≠ 0 :=
  exists_root_image_with_y_coeff_of_mem_trace (k := ℚ) mixedS (by decide)
    (by decide) mixedS_antichain
    (by exact ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩) mixedS_live hy

example
    (hz : X (k := ℚ) mixedS Normal.zGenerator
      ((mem_standardFinset_iff_standardSet mixedS _).2 mixedS_live.2.2.1) ∈
        TraceSubmodule ℚ mixedS) :
    ∃ (F : Omega ℚ mixedS →ₗ[MonomialArtin ℚ mixedS] MonomialArtin ℚ mixedS)
      (s : Normal 3 2 1) (hs : s ∈ mixedS),
      coeffAt (k := ℚ) mixedS
        ⟨Normal.zGenerator,
          (mem_standardFinset_iff_standardSet mixedS _).2 mixedS_live.2.2.1⟩
        (F (U (k := ℚ) mixedS (rootIndex mixedS s hs))) ≠ 0 :=
  exists_root_image_with_z_coeff_of_mem_trace (k := ℚ) mixedS (by decide)
    (by decide) mixedS_antichain
    (by exact ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩) mixedS_live hz

def pureR₁ : Normal 4 2 0 := ⟨3, 2, 0, by decide⟩
def pureR₂ : Normal 4 2 0 := ⟨2, 0, 2, by decide⟩
def pureR₃ : Normal 4 2 0 := ⟨0, 3, 1, by decide⟩
def pureS : Finset (Normal 4 2 0) := {pureR₁, pureR₂, pureR₃}

example : pureS.Nonempty := by decide
example : 2 ≤ pureS.card := by decide

theorem pureS_antichain : IsRootAntichain pureS := by
  intro p hp q hq hne hd
  simp [pureS] at hp hq
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
    subst p <;> subst q <;> try { exact (hne rfl).elim }
  all_goals
    rw [exact_divides_iff] at hd
    simp [Normal.DividesCriterion, pureR₁, pureR₂, pureR₃] at hd

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
    exact ⟨pureR₃, by simp [pureS], by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, liveTiePoint, pureR₃]⟩

/-! Swapping the mixed tie parameters preserves the symbolic atom API. -/
example (p q : Normal 3 1 2)
    (h : p * q = Normal.zGenerator) : p = 1 ∨ q = 1 :=
  variableGenerator_is_atom
    (by exact ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩) Direction.z p q h

/-! A wrapped product exercises coefficient transport in the normalized monoid. -/
def wrappedS : Finset (Normal 3 2 1) := {⟨0, 3, 2, by decide⟩}
def wrappedM : MonomialIndex wrappedS := ⟨Normal.xGenerator, by decide⟩
def wrappedE : MonomialIndex wrappedS := ⟨⟨2, 1, 1, by decide⟩, by decide⟩
def wrappedT : MonomialIndex wrappedS := ⟨⟨0, 3, 2, by decide⟩, by decide⟩

example : wrappedM.1 * wrappedE.1 = wrappedT.1 := by decide
example (v : MonomialArtin ℚ wrappedS) :
    coeffAt (k := ℚ) wrappedS wrappedT
        (X (k := ℚ) wrappedS wrappedM.1 wrappedM.2 * v) =
      coeffAt (k := ℚ) wrappedS wrappedE v :=
  coeffAt_X_mul (k := ℚ) wrappedS wrappedM wrappedE wrappedT (by decide) v

/-! Nonprimitive tie parameters still expose symbolic atom/source APIs. -/
example (p q : Normal 4 2 2)
    (h : p * q = Normal.xGenerator) : p = 1 ∨ q = 1 :=
  variableGenerator_is_atom
    (by exact ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩) Direction.x p q h

/-! A trace sum with two provably nonzero coordinates checks that trace
membership is not restricted to monomial-valued maps. -/
example (S : Finset (Normal a b c))
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (φ ψ : Omega k S) (p q : MonomialIndex S)
    (hpφ : coeffAt (k := k) S p (F φ) ≠ 0)
    (hpψ : coeffAt (k := k) S p (F ψ) = 0)
    (hqφ : coeffAt (k := k) S q (F φ) = 0)
    (hqψ : coeffAt (k := k) S q (F ψ) ≠ 0) :
    ∃ t ∈ TraceSubmodule k S,
      coeffAt (k := k) S p t ≠ 0 ∧ coeffAt (k := k) S q t ≠ 0 := by
  refine ⟨F φ + F ψ, (TraceSubmodule k S).add_mem
    (trace_range_le (k := k) S F ⟨φ, rfl⟩)
    (trace_range_le (k := k) S F ⟨ψ, rfl⟩), ?_, ?_⟩
  · change (F φ).coeff p + (F ψ).coeff p ≠ 0
    have hpψ' : (F ψ).coeff p = 0 := hpψ
    rw [hpψ', add_zero]
    exact hpφ
  · change (F φ).coeff q + (F ψ).coeff q ≠ 0
    have hqφ' : (F φ).coeff q = 0 := hqφ
    rw [hqφ', zero_add]
    exact hqψ

end ConcreteRegression

end

end P23.Artin

