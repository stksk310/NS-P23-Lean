import P23.Presentation.MonomialQuotient

namespace P23.Tests.Run13

open P23 OneTie Presentation Artin

#check NormalMonoidAlgebra
#check monomial
#check truncateAlgHom
#check truncateAlgHom_monomial
#check truncateAlgHom_surjective
#check killedMonomialIdeal
#check truncateAlgHom_ker
#check killed_has_border_divisor
#check borderMonomialIdeal_eq_killedMonomialIdeal
#check NormalMonomialQuotient
#check normalMonomialQuotientEquiv
#check borderMonomialQuotientEquiv
#check directModel_as_normalMonoidQuotient

noncomputable section

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

example (S : Finset (Normal a b c)) (p q : Normal a b c) :
    monomial (k := k) p * monomial (k := k) q = monomial (k := k) (p * q) :=
  monomial_mul p q

example (S : Finset (Normal a b c)) (p : Normal a b c)
    (hp : p ∈ standardFinset S) :
    truncateAlgHom (k := k) S (monomial (k := k) p) = X (k := k) S p hp :=
  truncateAlgHom_monomial_of_mem S p hp

example (S : Finset (Normal a b c)) (p : Normal a b c)
    (hp : p ∉ standardFinset S) :
    truncateAlgHom (k := k) S (monomial (k := k) p) = 0 :=
  truncateAlgHom_monomial_of_not_mem S p hp

example (S : Finset (Normal a b c)) :
    RingHom.ker (truncateAlgHom (k := k) S).toRingHom =
      killedMonomialIdeal (k := k) S :=
  truncateAlgHom_ker S

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) :
    borderMonomialIdeal (k := k) S = killedMonomialIdeal (k := k) S :=
  borderMonomialIdeal_eq_killedMonomialIdeal S hS hdom

namespace ConcreteRegression

def mixedRoot : Normal 3 2 1 := ⟨2, 2, 1, by decide⟩
def mixedS : Finset (Normal 3 2 1) := {mixedRoot}
def mixedSurvivor : Normal 3 2 1 := ⟨2, 1, 0, by decide⟩
def mixedKilled : Normal 3 2 1 := ⟨2, 3, 1, by decide⟩
def wrappedLeft : Normal 3 2 1 := ⟨2, 0, 0, by decide⟩
def wrappedRight : Normal 3 2 1 := ⟨1, 0, 0, by decide⟩
def mixedBorderY : Normal 3 2 1 := ⟨0, 3, 0, by decide⟩
def mixedKilledMultiple : Normal 3 2 1 := ⟨0, 4, 0, by decide⟩

example : mixedSurvivor ∈ standardFinset mixedS := by decide
example : mixedKilled ∉ standardFinset mixedS := by decide

example :
    truncateAlgHom (k := ℚ) mixedS (monomial (k := ℚ) mixedSurvivor) =
      X (k := ℚ) mixedS mixedSurvivor (by decide) := by
  exact truncateAlgHom_monomial_of_mem mixedS mixedSurvivor (by decide)

example :
    truncateAlgHom (k := ℚ) mixedS (monomial (k := ℚ) mixedKilled) = 0 := by
  exact truncateAlgHom_monomial_of_not_mem mixedS mixedKilled (by decide)

example : wrappedLeft * wrappedRight = (⟨0, 2, 1, by decide⟩ : Normal 3 2 1) := by
  decide

example :
    truncateAlgHom (k := ℚ) mixedS
        (monomial (k := ℚ) wrappedLeft * monomial (k := ℚ) wrappedRight) =
      truncatedMonomial (k := ℚ) mixedS (wrappedLeft * wrappedRight) := by
  simp

example : mixedBorderY ∈ borderFinset mixedS := by
  have h := mixedPrincipalBorder_last (a := 3) (b := 2) (c := 1)
    (r := 2) (u := 2) (v := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h' : borderFinset mixedS =
      {mixedY (a := 3) (b := 2) (c := 1) 2,
        mixedZ (a := 3) (b := 2) (c := 1) 1} := by
    simpa [mixedS, mixedRoot, mixedCore] using h
  rw [h']
  simp [mixedBorderY, mixedY]

example : mixedKilledMultiple ∉ borderFinset mixedS := by
  have h := mixedPrincipalBorder_last (a := 3) (b := 2) (c := 1)
    (r := 2) (u := 2) (v := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h' : borderFinset mixedS =
      {mixedY (a := 3) (b := 2) (c := 1) 2,
        mixedZ (a := 3) (b := 2) (c := 1) 1} := by
    simpa [mixedS, mixedRoot, mixedCore] using h
  rw [h']
  simp [mixedKilledMultiple, mixedY, mixedZ]

example : mixedBorderY ∣ mixedKilledMultiple := by
  refine ⟨Normal.yGenerator, ?_⟩
  decide

example :
    monomial (k := ℚ) mixedKilledMultiple ∈
      borderMonomialIdeal (k := ℚ) mixedS := by
  apply monomial_mem_borderMonomialIdeal_of_dvd mixedS
    (g := mixedBorderY) (p := mixedKilledMultiple)
  · have h := mixedPrincipalBorder_last (a := 3) (b := 2) (c := 1)
      (r := 2) (u := 2) (v := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have h' : borderFinset mixedS =
        {mixedY (a := 3) (b := 2) (c := 1) 2,
          mixedZ (a := 3) (b := 2) (c := 1) 1} := by
      simpa [mixedS, mixedRoot, mixedCore] using h
    rw [h']
    simp [mixedBorderY, mixedY]
  · exact ⟨Normal.yGenerator, by decide⟩

example :
    truncateAlgHom (k := ℚ) mixedS
        (monomial (k := ℚ) mixedKilled +
          (2 : ℚ) • monomial (k := ℚ) mixedKilledMultiple) = 0 := by
  rw [map_add, map_smul,
    truncateAlgHom_monomial_of_not_mem mixedS mixedKilled (by decide),
    truncateAlgHom_monomial_of_not_mem mixedS mixedKilledMultiple (by decide)]
  simp

example :
    monomial (k := ℚ) mixedKilled +
        (2 : ℚ) • monomial (k := ℚ) mixedKilledMultiple ∈
      killedMonomialIdeal (k := ℚ) mixedS := by
  rw [← truncateAlgHom_ker mixedS]
  apply RingHom.mem_ker.2
  change truncateAlgHom (k := ℚ) mixedS
      (monomial (k := ℚ) mixedKilled +
        (2 : ℚ) • monomial (k := ℚ) mixedKilledMultiple) = 0
  rw [map_add, map_smul,
    truncateAlgHom_monomial_of_not_mem mixedS mixedKilled (by decide),
    truncateAlgHom_monomial_of_not_mem mixedS mixedKilledMultiple (by decide)]
  simp

example :
    normalMonomialQuotientEquiv (k := ℚ) mixedS
        (Ideal.Quotient.mk (killedMonomialIdeal (k := ℚ) mixedS)
          (monomial (k := ℚ) mixedSurvivor)) =
      X (k := ℚ) mixedS mixedSurvivor (by decide) := by
  exact normalMonomialQuotientEquiv_monomial_of_mem mixedS mixedSurvivor
    (by decide)

example :
    normalMonomialQuotientEquiv (k := ℚ) mixedS
        (Ideal.Quotient.mk (killedMonomialIdeal (k := ℚ) mixedS)
          (monomial (k := ℚ) mixedKilled)) = 0 := by
  exact normalMonomialQuotientEquiv_monomial_of_not_mem mixedS mixedKilled
    (by decide)

def pureRoot : Normal 4 2 0 := ⟨3, 1, 1, by decide⟩
def pureS : Finset (Normal 4 2 0) := {pureRoot}

def nonprimitiveMixedRoot : Normal 4 2 2 := ⟨0, 2, 2, by decide⟩
def nonprimitiveMixedS : Finset (Normal 4 2 2) := {nonprimitiveMixedRoot}

def nonprimitivePureRoot : Normal 4 2 0 := ⟨0, 2, 0, by decide⟩
def nonprimitivePureZ : Normal 4 2 0 := ⟨0, 0, 1, by decide⟩
def nonprimitivePureS : Finset (Normal 4 2 0) :=
  {nonprimitivePureRoot, nonprimitivePureZ}

example :
    borderMonomialIdeal (k := ℚ) nonprimitiveMixedS =
      killedMonomialIdeal (k := ℚ) nonprimitiveMixedS := by
  exact borderMonomialIdeal_eq_killedMonomialIdeal nonprimitiveMixedS
    (by decide) ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩

example :
    borderMonomialIdeal (k := ℚ) nonprimitivePureS =
      killedMonomialIdeal (k := ℚ) nonprimitivePureS := by
  exact borderMonomialIdeal_eq_killedMonomialIdeal nonprimitivePureS
    (by decide) ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩

example :
    borderMonomialIdeal (k := ℚ) pureS = killedMonomialIdeal (k := ℚ) pureS := by
  exact borderMonomialIdeal_eq_killedMonomialIdeal pureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩

example (f : NormalMonoidAlgebra ℚ 4 2 0)
    (hf : truncateAlgHom (k := ℚ) pureS f = 0) :
    f ∈ killedMonomialIdeal (k := ℚ) pureS := by
  rw [← truncateAlgHom_ker pureS]
  exact hf

example (p : Normal 4 2 0) :
    borderMonomialQuotientEquiv (k := ℚ) pureS (by decide)
        ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩
        (Ideal.Quotient.mk (borderMonomialIdeal (k := ℚ) pureS)
          (monomial (k := ℚ) p)) =
      truncatedMonomial (k := ℚ) pureS p := by
  exact borderMonomialQuotientEquiv_monomial (k := ℚ) pureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ p

end ConcreteRegression

end

end P23.Tests.Run13
