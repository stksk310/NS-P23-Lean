import P23.Artin.TraceToCentre

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {a b c : ℕ} [NeZero a]
variable {k : Type*} [Field k]

#check predecessor_mul_generator
#check predecessor_dvd_root
#check predecessor_mem_standardSet
#check predecessor_mem_standardFinset
#check root_mem_standardFinset
#check rootSource_isDirectionalCentre
#check exists_directionalCentre_of_variable_mem_trace
#check exists_x_directionalCentre_of_mem_trace
#check exists_y_directionalCentre_of_mem_trace
#check exists_z_directionalCentre_of_mem_trace
#check hasDirectionalCentres_of_variablesInTrace
#check mixed_four_border_trace_has_dominant
#check pure_four_border_trace_dominant_or_residual
#check TraceFourBorderGeometry
#check trace_four_border_geometry

example (S : Finset (Normal a b c)) (e : Direction)
    (heS : e.generator ∈ standardFinset S)
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (s : Normal a b c) (hs : s ∈ S)
    (hcoeff : coeffAt (k := k) S ⟨e.generator, heS⟩
      (F (U (k := k) S (rootIndex S s hs))) ≠ 0) :
    IsDirectionalCentre S e s :=
  rootSource_isDirectionalCentre (k := k) S e heS F s hs hcoeff

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    VariablesInTrace k S hlive → HasDirectionalCentres S :=
  hasDirectionalCentres_of_variablesInTrace (k := k) S hS hcard hanti
    hdom hlive

namespace ConcreteRegression

def mixedR₁ : Normal 3 2 1 := ⟨2, 2, 0, by decide⟩
def mixedR₂ : Normal 3 2 1 := ⟨1, 0, 2, by decide⟩
def mixedR₃ : Normal 3 2 1 := ⟨0, 3, 1, by decide⟩
def mixedS : Finset (Normal 3 2 1) := {mixedR₁, mixedR₂, mixedR₃}

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

/-! Mixed x/y/z source coefficients produce centres. -/
example
    (F : Omega ℚ mixedS →ₗ[MonomialArtin ℚ mixedS] MonomialArtin ℚ mixedS)
    (s : Normal 3 2 1) (hs : s ∈ mixedS)
    (hx : coeffAt (k := ℚ) mixedS
      ⟨Normal.xGenerator, (mem_standardFinset_iff_standardSet mixedS _).2
        mixedS_live.1⟩
      (F (U (k := ℚ) mixedS (rootIndex mixedS s hs))) ≠ 0) :
    IsDirectionalCentre mixedS .x s :=
  rootSource_isDirectionalCentre (k := ℚ) mixedS .x _ F s hs hx

example
    (F : Omega ℚ mixedS →ₗ[MonomialArtin ℚ mixedS] MonomialArtin ℚ mixedS)
    (s : Normal 3 2 1) (hs : s ∈ mixedS)
    (hy : coeffAt (k := ℚ) mixedS
      ⟨Normal.yGenerator, (mem_standardFinset_iff_standardSet mixedS _).2
        mixedS_live.2.1⟩
      (F (U (k := ℚ) mixedS (rootIndex mixedS s hs))) ≠ 0) :
    IsDirectionalCentre mixedS .y s :=
  rootSource_isDirectionalCentre (k := ℚ) mixedS .y _ F s hs hy

example
    (F : Omega ℚ mixedS →ₗ[MonomialArtin ℚ mixedS] MonomialArtin ℚ mixedS)
    (s : Normal 3 2 1) (hs : s ∈ mixedS)
    (hz : coeffAt (k := ℚ) mixedS
      ⟨Normal.zGenerator, (mem_standardFinset_iff_standardSet mixedS _).2
        mixedS_live.2.2.1⟩
      (F (U (k := ℚ) mixedS (rootIndex mixedS s hs))) ≠ 0) :
    IsDirectionalCentre mixedS .z s :=
  rootSource_isDirectionalCentre (k := ℚ) mixedS .z _ F s hs hz

/-! A concrete wrapped-x predecessor passes through the generic helper. -/
def wrappedRoot : Normal 3 2 1 := ⟨0, 3, 2, by decide⟩
def wrappedPred : Normal 3 2 1 := ⟨2, 1, 1, by decide⟩
def wrappedS : Finset (Normal 3 2 1) := {wrappedRoot}

example : Normal.predecessor .x wrappedRoot = some wrappedPred := by decide

example : wrappedPred ∈ standardFinset wrappedS :=
  predecessor_mem_standardFinset wrappedS (r := wrappedRoot) (q := wrappedPred)
    (by simp [wrappedS]) .x (by decide)

example
    (F : Omega ℚ wrappedS →ₗ[MonomialArtin ℚ wrappedS] MonomialArtin ℚ wrappedS)
    (hx : coeffAt (k := ℚ) wrappedS
      ⟨Normal.xGenerator, by decide⟩
      (F (U (k := ℚ) wrappedS
        (rootIndex wrappedS wrappedRoot (by simp [wrappedS])))) ≠ 0) :
    IsDirectionalCentre wrappedS .x wrappedRoot :=
  rootSource_isDirectionalCentre (k := ℚ) wrappedS .x (by decide) F
    wrappedRoot (by simp [wrappedS]) hx

def pureR₁ : Normal 4 2 0 := ⟨3, 2, 0, by decide⟩
def pureR₂ : Normal 4 2 0 := ⟨2, 0, 2, by decide⟩
def pureR₃ : Normal 4 2 0 := ⟨0, 3, 1, by decide⟩
def pureS : Finset (Normal 4 2 0) := {pureR₁, pureR₂, pureR₃}

example
    (F : Omega ℚ pureS →ₗ[MonomialArtin ℚ pureS] MonomialArtin ℚ pureS)
    (s : Normal 4 2 0) (hs : s ∈ pureS)
    (hy : coeffAt (k := ℚ) pureS ⟨Normal.yGenerator, by decide⟩
      (F (U (k := ℚ) pureS (rootIndex pureS s hs))) ≠ 0) :
    IsDirectionalCentre pureS .y s :=
  rootSource_isDirectionalCentre (k := ℚ) pureS .y (by decide) F s hs hy

/-! Nonprimitive tie parameters use the identical theorem. -/
example (S : Finset (Normal 4 2 2)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S) (hlive : IsLiveTie S) :
    VariablesInTrace ℚ S hlive → HasDirectionalCentres S :=
  hasDirectionalCentres_of_variablesInTrace (k := ℚ) S hS hcard hanti
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ hlive

/-! The packaging deliberately permits three different centre roots. -/
example (htrace : VariablesInTrace ℚ mixedS mixedS_live) :
    ∃ sx sy sz,
      IsDirectionalCentre mixedS .x sx ∧
      IsDirectionalCentre mixedS .y sy ∧
      IsDirectionalCentre mixedS .z sz := by
  have hcentres := hasDirectionalCentres_of_variablesInTrace (k := ℚ)
    mixedS (by decide) (by decide) mixedS_antichain
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ mixedS_live htrace
  obtain ⟨sx, hx⟩ := hcentres .x
  obtain ⟨sy, hy⟩ := hcentres .y
  obtain ⟨sz, hz⟩ := hcentres .z
  exact ⟨sx, sy, sz, hx, hy, hz⟩

/-! Concrete-parameter mixed trace/four-border bridge. -/
example (S : Finset (Normal 3 2 1)) (hcard : S.card = 3)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    (htrace : VariablesInTrace ℚ S hlive)
    (hborder : (borderFinset S).card = 4) :
    ∃ C ∈ S, IsDominantRoot S C :=
  mixed_four_border_trace_has_dominant (k := ℚ) S (by decide) (by decide)
    (by decide) hcard hlive hanti htrace hborder

def p4S : Finset (Normal 4 2 0) := p4ZSocles (by decide) 1
def p5S : Finset (Normal 4 2 0) := p5ZSocles (by decide) 1

example : IsPureResidualFourBorderShape p4S := by
  exact Or.inl ⟨1, by decide, by decide, by decide, rfl⟩

example : IsPureResidualFourBorderShape p5S := by
  exact Or.inr ⟨1, by decide, by decide, by decide, rfl⟩

example (hlive : IsLiveTie p4S) (hanti : IsRootAntichain p4S)
    (htrace : VariablesInTrace ℚ p4S hlive) :
    (∃ C ∈ p4S, IsDominantRoot p4S C) ∨ IsPureResidualFourBorderShape p4S :=
  pure_four_border_trace_dominant_or_residual (k := ℚ) p4S (by decide)
    (by decide) (by decide) hlive hanti htrace
    (by
      change (borderFinset
        (p4ZSocles (a := 4) (b := 2) (by decide) 1)).card = 4
      exact p4Z_border_card (a := 4) (b := 2) (V := 1)
        (by decide) (by decide) (by decide))

example (hlive : IsLiveTie p5S) (hanti : IsRootAntichain p5S)
    (htrace : VariablesInTrace ℚ p5S hlive) :
    (∃ C ∈ p5S, IsDominantRoot p5S C) ∨ IsPureResidualFourBorderShape p5S :=
  pure_four_border_trace_dominant_or_residual (k := ℚ) p5S (by decide)
    (by decide) (by decide) hlive hanti htrace
    (by
      change (borderFinset
        (p5ZSocles (a := 4) (b := 2) (by decide) 1)).card = 4
      exact p5Z_border_card (a := 4) (b := 2) (v := 1)
        (by decide) (by decide) (by decide))

end ConcreteRegression

end

end P23.Artin
