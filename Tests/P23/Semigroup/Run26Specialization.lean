import P23.Semigroup.ChosenBaseSpecialization

open P23.Semigroup
open FourGeneratedNumericalSemigroup
variable {k : Type*} [Field k] (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
example (j : Fin 4) (hj : j ≠ i) :
    D.tailIndex i ((tailIndexEquiv D i).symm ⟨j, hj⟩) = j :=
  tailIndexEquiv_symm_apply D i j hj
example : baseSpecialization (k := k) D i (MvPolynomial.X i) = 0 :=
  baseSpecialization_X_base D i
example (j : Fin 3) : baseSpecialization (k := k) D i
    (MvPolynomial.X (D.tailIndex i j)) = MvPolynomial.X j :=
  baseSpecialization_X_tail D i j
example (u : Fin 4 →₀ ℕ) (r : k) (h : u i = 0) :
    baseSpecialization D i (MvPolynomial.monomial u r) =
      MvPolynomial.monomial (restrictToTails D i u) r :=
  baseSpecialization_monomial_of_base_zero D i u r h
example (u : Fin 4 →₀ ℕ) (r : k) (h : 0 < u i) :
    baseSpecialization D i (MvPolynomial.monomial u r) = 0 :=
  baseSpecialization_monomial_of_base_pos D i u r h
example : RingHom.ker (baseSpecialization (k := k) D i).toRingHom =
    Ideal.span {MvPolynomial.X i} := baseSpecialization_ker D i
example (p : TailPoly k) : baseSpecialization D i (tailEmbedding D i p) = p :=
  baseSpecialization_tailEmbedding D i p
example (u : Fin 4 →₀ ℕ) (h : u i = 0) :
    tailEmbeddingExponent i (restrictToTails D i u) = u :=
  tailEmbedding_restrictToTails D i u h
example : Ideal.map (baseSpecialization (k := k) D i).toRingHom
    (D.toricIdeal (k := k)) = chosenBaseDefiningIdeal D i :=
  map_toricIdeal_eq_chosenBaseDefiningIdeal D i
