import P23.Presentation.FinitePolynomialQuotient

namespace P23.Presentation.Run15Test

open P23.OneTie P23.Artin
open MvPolynomial

section Symbolic

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

#check polynomialLift
#check polyToNormalAlg_polynomialLift
#check polynomialLift_injective
#check polynomialBorderIdeal
#check finitePresentationIdeal
#check tiePolynomial_mem_finitePresentationIdeal
#check polynomialLift_mem_finitePresentationIdeal_of_border
#check polynomialBorderIdeal_map
#check borderMonomialIdeal_comap
#check killedMonomialIdeal_comap
#check polyToDirectAlg
#check polyToDirectAlg_monomial
#check polyToDirectAlg_polyX
#check polyToDirectAlg_polyY
#check polyToDirectAlg_polyZ
#check polyToDirectAlg_surjective
#check polyToDirectAlg_ker
#check FinitePolynomialQuotient
#check finitePolynomialQuotientEquiv
#check finitePolynomialQuotientEquiv_polyX
#check finitePolynomialQuotientEquiv_polyY
#check finitePolynomialQuotientEquiv_polyZ
#check finitePolynomialQuotientEquiv_monomial
#check finitePolynomialQuotientEquiv_polynomialLift_of_mem
#check finitePolynomialQuotientEquiv_polynomialLift_of_border
#check presentationGeneratorFinset
#check span_presentationGeneratorFinset
#check DirectModelAsPolynomialQuotient
#check directModel_as_polynomialQuotient

example (p : Normal a b c) :
    polyToNormalAlg (k := k) (polynomialLift (k := k) p) = monomial p :=
  polyToNormalAlg_polynomialLift p

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) :
    RingHom.ker (polyToDirectAlg (k := k) S).toRingHom =
      finitePresentationIdeal (k := k) S :=
  polyToDirectAlg_ker S hS hdom

end Symbolic

namespace Concrete

def mixedRoot : Normal 3 2 1 := ⟨2, 2, 1, by decide⟩
def mixedS : Finset (Normal 3 2 1) := {mixedRoot}
def mixedSurvivor : Normal 3 2 1 := ⟨2, 1, 0, by decide⟩
def mixedBorder : Normal 3 2 1 := ⟨0, 3, 0, by decide⟩
def mixedKilledNonBorder : Normal 3 2 1 := ⟨0, 4, 0, by decide⟩

def pureRoot : Normal 4 2 0 := ⟨3, 1, 1, by decide⟩
def pureS : Finset (Normal 4 2 0) := {pureRoot}

def nonprimitiveMixedRoot : Normal 4 2 2 := ⟨0, 2, 2, by decide⟩
def nonprimitiveMixedS : Finset (Normal 4 2 2) := {nonprimitiveMixedRoot}

def nonprimitivePureRoot : Normal 4 2 0 := ⟨0, 2, 0, by decide⟩
def nonprimitivePureZ : Normal 4 2 0 := ⟨0, 0, 1, by decide⟩
def nonprimitivePureS : Finset (Normal 4 2 0) :=
  {nonprimitivePureRoot, nonprimitivePureZ}

theorem mixedS_nonempty : mixedS.Nonempty := by decide

theorem mixed_liveDomain : IsLiveParameterDomain 3 2 1 :=
  ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩

theorem mixedBorder_mem : mixedBorder ∈ borderFinset mixedS := by
  have h := mixedPrincipalBorder_last (a := 3) (b := 2) (c := 1)
    (r := 2) (u := 2) (v := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h' : borderFinset mixedS =
      {mixedY (a := 3) (b := 2) (c := 1) 2,
        mixedZ (a := 3) (b := 2) (c := 1) 1} := by
    simpa [mixedS, mixedRoot, mixedCore] using h
  rw [h']
  simp [mixedBorder, mixedY]

theorem mixedSurvivor_mem : mixedSurvivor ∈ standardFinset mixedS := by decide

theorem mixedKilledNonBorder_not_mem :
    mixedKilledNonBorder ∉ standardFinset mixedS := by decide

example :
    RingHom.ker (polyToDirectAlg (k := ℚ) mixedS).toRingHom =
      finitePresentationIdeal (k := ℚ) mixedS := by
  exact polyToDirectAlg_ker mixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩

example :
    RingHom.ker (polyToDirectAlg (k := ℚ) pureS).toRingHom =
      finitePresentationIdeal (k := ℚ) pureS := by
  exact polyToDirectAlg_ker pureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩

example :
    RingHom.ker (polyToDirectAlg (k := ℚ) nonprimitiveMixedS).toRingHom =
      finitePresentationIdeal (k := ℚ) nonprimitiveMixedS := by
  exact polyToDirectAlg_ker nonprimitiveMixedS (by decide)
    ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩

example :
    RingHom.ker (polyToDirectAlg (k := ℚ) nonprimitivePureS).toRingHom =
      finitePresentationIdeal (k := ℚ) nonprimitivePureS := by
  exact polyToDirectAlg_ker nonprimitivePureS (by decide)
    ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩

/- Exact generator and kernel behavior in a concrete mixed live model. -/
example :
    tiePolynomial (k := ℚ) 3 2 1 ∈
      RingHom.ker (polyToDirectAlg (k := ℚ) mixedS).toRingHom := by
  rw [polyToDirectAlg_ker mixedS mixedS_nonempty mixed_liveDomain]
  exact tiePolynomial_mem_finitePresentationIdeal mixedS

example :
    polynomialLift (k := ℚ) mixedBorder ∈
      RingHom.ker (polyToDirectAlg (k := ℚ) mixedS).toRingHom := by
  rw [polyToDirectAlg_ker mixedS mixedS_nonempty mixed_liveDomain]
  exact polynomialLift_mem_finitePresentationIdeal_of_border
    mixedS mixedBorder_mem

example :
    polynomialLift (k := ℚ) mixedKilledNonBorder ∈
      RingHom.ker (polyToDirectAlg (k := ℚ) mixedS).toRingHom := by
  apply RingHom.mem_ker.2
  simp [polyToDirectAlg, mixedKilledNonBorder_not_mem]

example :
    polynomialLift (k := ℚ) mixedSurvivor ∉
      RingHom.ker (polyToDirectAlg (k := ℚ) mixedS).toRingHom := by
  intro h
  have hz := RingHom.mem_ker.1 h
  have hne :
      polyToDirectAlg (k := ℚ) mixedS
          (polynomialLift (k := ℚ) mixedSurvivor) ≠ 0 := by
    simp [polyToDirectAlg, mixedSurvivor_mem,
      X_ne_zero (k := ℚ) mixedS mixedSurvivor mixedSurvivor_mem]
  exact hne hz

example :
    tiePolynomial (k := ℚ) 3 2 1 +
        polyY * polynomialLift (k := ℚ) mixedBorder ∈
      RingHom.ker (polyToDirectAlg (k := ℚ) mixedS).toRingHom := by
  rw [polyToDirectAlg_ker mixedS mixedS_nonempty mixed_liveDomain]
  apply Ideal.add_mem
  · exact tiePolynomial_mem_finitePresentationIdeal mixedS
  · exact (finitePresentationIdeal (k := ℚ) mixedS).mul_mem_left _
      (polynomialLift_mem_finitePresentationIdeal_of_border
        mixedS mixedBorder_mem)

/- Quotient transport on variables, a survivor and a border lift. -/
example :
    finitePolynomialQuotientEquiv (k := ℚ) mixedS
        mixedS_nonempty mixed_liveDomain
        (Ideal.Quotient.mk _ polyX) =
      truncatedMonomial (k := ℚ) mixedS
        (Normal.xGenerator : Normal 3 2 1) := by
  exact finitePolynomialQuotientEquiv_polyX
    mixedS mixedS_nonempty mixed_liveDomain

example :
    finitePolynomialQuotientEquiv (k := ℚ) mixedS
        mixedS_nonempty mixed_liveDomain
        (Ideal.Quotient.mk _ polyY) =
      truncatedMonomial (k := ℚ) mixedS
        (Normal.yGenerator : Normal 3 2 1) := by
  exact finitePolynomialQuotientEquiv_polyY
    mixedS mixedS_nonempty mixed_liveDomain

example :
    finitePolynomialQuotientEquiv (k := ℚ) mixedS
        mixedS_nonempty mixed_liveDomain
        (Ideal.Quotient.mk _ polyZ) =
      truncatedMonomial (k := ℚ) mixedS
        (Normal.zGenerator : Normal 3 2 1) := by
  exact finitePolynomialQuotientEquiv_polyZ
    mixedS mixedS_nonempty mixed_liveDomain

example :
    finitePolynomialQuotientEquiv (k := ℚ) mixedS
        mixedS_nonempty mixed_liveDomain
        (Ideal.Quotient.mk _ (polynomialLift (k := ℚ) mixedSurvivor)) =
      X (k := ℚ) mixedS mixedSurvivor mixedSurvivor_mem := by
  exact finitePolynomialQuotientEquiv_polynomialLift_of_mem
    mixedS mixedS_nonempty mixed_liveDomain mixedSurvivor mixedSurvivor_mem

example :
    finitePolynomialQuotientEquiv (k := ℚ) mixedS
        mixedS_nonempty mixed_liveDomain
        (Ideal.Quotient.mk _ (polynomialLift (k := ℚ) mixedBorder)) = 0 := by
  exact finitePolynomialQuotientEquiv_polynomialLift_of_border
    mixedS mixedS_nonempty mixed_liveDomain mixedBorder mixedBorder_mem

end Concrete

end P23.Presentation.Run15Test
