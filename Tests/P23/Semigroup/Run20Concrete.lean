import P23.Semigroup.ChosenBase

/-!
Test-only concrete fixtures closing the non-load-bearing Run20 regression
debt.  No production module imports this file.
-/

namespace P23.Semigroup.Run20Concrete

open P23.Semigroup

noncomputable section

private def nFour : Fin 4 → ℕ := ![4, 5, 6, 7]
private def nFive : Fin 4 → ℕ := ![5, 6, 7, 8]

@[simp] private theorem nFour_0 : nFour 0 = 4 := rfl
@[simp] private theorem nFour_1 : nFour 1 = 5 := rfl
@[simp] private theorem nFour_2 : nFour 2 = 6 := rfl
@[simp] private theorem nFour_3 : nFour 3 = 7 := rfl
@[simp] private theorem nFive_0 : nFive 0 = 5 := rfl
@[simp] private theorem nFive_1 : nFive 1 = 6 := rfl
@[simp] private theorem nFive_2 : nFive 2 = 7 := rfl
@[simp] private theorem nFive_3 : nFive 3 = 8 := rfl

private theorem nFour_positive : ∀ j, 0 < nFour j := by decide
private theorem nFive_positive : ∀ j, 0 < nFive j := by decide
private theorem nFour_injective : Function.Injective nFour := by decide
private theorem nFive_injective : Function.Injective nFive := by decide

private theorem weightedDegree_four (n : Fin 4 → ℕ) (u : Fin 4 →₀ ℕ) :
    weightedDegreeOf n u =
      u 0 * n 0 + u 1 * n 1 + u 2 * n 2 + u 3 * n 3 := by
  simp [weightedDegreeOf, Fin.sum_univ_succ, add_assoc]

private theorem nFour_minimal : ∀ j (u : Fin 4 →₀ ℕ), u j = 0 →
    weightedDegreeOf nFour u ≠ nFour j := by
  intro j u hu heq
  rw [weightedDegree_four] at heq
  simp only [nFour_0, nFour_1, nFour_2, nFour_3] at heq
  fin_cases j <;> simp at hu <;> simp [hu] at heq
  all_goals
    have h0 : u 0 ≤ 1 := by omega
    have h1 : u 1 ≤ 1 := by omega
    have h2 : u 2 ≤ 1 := by omega
    have h3 : u 3 ≤ 1 := by omega
    interval_cases e0 : u 0 <;> interval_cases e1 : u 1 <;>
      interval_cases e2 : u 2 <;> interval_cases e3 : u 3 <;> omega

private theorem nFive_minimal : ∀ j (u : Fin 4 →₀ ℕ), u j = 0 →
    weightedDegreeOf nFive u ≠ nFive j := by
  intro j u hu heq
  rw [weightedDegree_four] at heq
  simp only [nFive_0, nFive_1, nFive_2, nFive_3] at heq
  fin_cases j <;> simp at hu <;> simp [hu] at heq <;> omega

private theorem nFour_large_mem (s : ℕ) (hs : 4 ≤ s) :
    s ∈ generatedByFour nFour := by
  rw [generatedByFour, AddMonoidHom.mem_mrange]
  let u : Fin 4 →₀ ℕ :=
    if s % 4 = 0 then Finsupp.single 0 (s / 4)
    else if s % 4 = 1 then Finsupp.single 0 (s / 4 - 1) + Finsupp.single 1 1
    else if s % 4 = 2 then Finsupp.single 0 (s / 4 - 1) + Finsupp.single 2 1
    else Finsupp.single 0 (s / 4 - 1) + Finsupp.single 3 1
  refine ⟨u, ?_⟩
  change weightedDegreeOf nFour u = s
  rw [weightedDegree_four]
  have hm := Nat.mod_lt s (by omega : 0 < 4)
  have hd := Nat.mod_add_div s 4
  interval_cases h : s % 4 <;>
    simp [u, h, nFour, Finsupp.single_apply] <;> omega

private theorem nFive_large_mem (s : ℕ) (hs : 10 ≤ s) :
    s ∈ generatedByFour nFive := by
  rw [generatedByFour, AddMonoidHom.mem_mrange]
  let u : Fin 4 →₀ ℕ :=
    if s % 5 = 0 then Finsupp.single 0 (s / 5)
    else if s % 5 = 1 then Finsupp.single 0 (s / 5 - 1) + Finsupp.single 1 1
    else if s % 5 = 2 then Finsupp.single 0 (s / 5 - 1) + Finsupp.single 2 1
    else if s % 5 = 3 then Finsupp.single 0 (s / 5 - 1) + Finsupp.single 3 1
    else Finsupp.single 0 (s / 5 - 2) + Finsupp.single 2 2
  refine ⟨u, ?_⟩
  change weightedDegreeOf nFive u = s
  rw [weightedDegree_four]
  have hm := Nat.mod_lt s (by omega : 0 < 5)
  have hd := Nat.mod_add_div s 5
  interval_cases h : s % 5 <;>
    simp [u, h, nFive, Finsupp.single_apply] <;> omega

private theorem cofinite_of_large_mem (n : Fin 4 → ℕ) (C : ℕ)
    (hlarge : ∀ s, C ≤ s → s ∈ generatedByFour n) :
    Set.Finite {s : ℕ | s ∉ generatedByFour n} := by
  apply Set.Finite.subset (Set.finite_Iio C)
  intro s hs
  simp only [Set.mem_setOf_eq, Set.mem_Iio]
  by_contra hnot
  exact hs (hlarge s (by omega))

private def GammaFour : FourGeneratedNumericalSemigroup where
  n := nFour
  positive := nFour_positive
  injective := nFour_injective
  minimal := nFour_minimal
  cofinite := cofinite_of_large_mem nFour 4 nFour_large_mem

private def GammaFive : FourGeneratedNumericalSemigroup where
  n := nFive
  positive := nFive_positive
  injective := nFive_injective
  minimal := nFive_minimal
  cofinite := cofinite_of_large_mem nFive 10 nFive_large_mem

-- All four chosen bases retain all three tail generators in both fixtures.
example (i : Fin 4) (j : Fin 3) : GammaFour.IsApery i (GammaFour.tail i j) :=
  GammaFour.tail_isApery i j

example (i : Fin 4) (j : Fin 3) : GammaFive.IsApery i (GammaFive.tail i j) :=
  GammaFive.tail_isApery i j

-- At base 4, the Apéry degree 12 has distinct tail factorizations 6+6=5+7.
private def sixTwice : Fin 3 →₀ ℕ := Finsupp.single 1 2
private def fivePlusSeven : Fin 3 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 2 1

example : sixTwice ≠ fivePlusSeven := by
  intro h
  have hv := congrArg (fun u : Fin 3 →₀ ℕ => u 0) h
  simp [sixTwice, fivePlusSeven] at hv

example : tailDegree GammaFour 0 sixTwice = 12 := by
  simp [tailDegree, sixTwice, GammaFour, nFour, Fin.sum_univ_succ,
    FourGeneratedNumericalSemigroup.tailGen,
    FourGeneratedNumericalSemigroup.tailIndex]

example : tailDegree GammaFour 0 fivePlusSeven = 12 := by
  simp [tailDegree, fivePlusSeven, GammaFour, nFour, Fin.sum_univ_succ,
    FourGeneratedNumericalSemigroup.tailGen,
    FourGeneratedNumericalSemigroup.tailIndex]

end

end P23.Semigroup.Run20Concrete
