import P23.Semigroup.RhoFourTaggedNormalization

/-! Weighted degree is transported through normalization; exponent support is not. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.OneTie P23.Presentation
open scoped BigOperators
set_option maxHeartbeats 800000
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}

namespace OneTieCoordinates
variable {p : TailPoly ℚ} (C : OneTieCoordinates D i p)

def coordinateDegree (d : Fin 3 →₀ ℕ) : ℕ := tailDegree D i (d.mapDomain C.sigma.symm)

theorem coordinateDegree_rename (d : Fin 3 →₀ ℕ) :
    C.coordinateDegree (d.mapDomain C.sigma) = tailDegree D i d := by
  unfold coordinateDegree
  have he : C.sigma.symm ∘ C.sigma = id := by funext j; simp
  rw [← Finsupp.mapDomain_comp, he, Finsupp.mapDomain_id]

theorem coordinateDegree_formula (d : Fin 3 →₀ ℕ) :
    C.coordinateDegree d = d 0 * D.tailGen i (C.sigma.symm 0) +
      d 1 * D.tailGen i (C.sigma.symm 1) + d 2 * D.tailGen i (C.sigma.symm 2) := by
  unfold coordinateDegree tailDegree
  calc
    _ = ∑ j : Fin 3, d j * D.tailGen i (C.sigma.symm j) := by
      apply Fintype.sum_equiv C.sigma _ _
      intro j
      simp
    _ = _ := by rw [Fin.sum_univ_three]

theorem weighted_tie_equation :
    C.a * D.tailGen i (C.sigma.symm 0) =
      C.b * D.tailGen i (C.sigma.symm 1) + C.c * D.tailGen i (C.sigma.symm 2) := by
  classical
  let dx : Fin 3 →₀ ℕ := Finsupp.single 0 C.a
  let dy : Fin 3 →₀ ℕ := Finsupp.single 1 C.b + Finsupp.single 2 C.c
  let u := C.original.u.mapDomain C.sigma
  let v := C.original.v.mapDomain C.sigma
  have ha : C.a ≠ 0 := NeZero.ne _
  have hxy : dx ≠ dy := by
    intro he
    have hh := congrArg (fun d : Fin 3 →₀ ℕ => d 0) he
    exact ha (by simpa [dx,dy] using hh)
  have ht : tiePolynomial (k := ℚ) C.a C.b C.c =
      MvPolynomial.monomial dx 1 - MvPolynomial.monomial dy 1 := by
    simp [tiePolynomial, polyX, polyY, polyZ, dx, dy,
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
  have he : renameToOneTie C p =
      MvPolynomial.monomial u 1 - MvPolynomial.monomial v 1 := by
    calc
      _ = renameToOneTie C (MvPolynomial.monomial C.original.u 1 -
          MvPolynomial.monomial C.original.v 1) := congrArg (renameToOneTie C) C.original.equation
      _ = _ := by simp [renameToOneTie, MvPolynomial.rename_monomial, u, v]
  have hmatch (d : Fin 3 →₀ ℕ) (hd : d = dx ∨ d = dy) : u = d ∨ v = d := by
    by_contra hn
    push_neg at hn
    have hz : MvPolynomial.coeff d (renameToOneTie C p) = 0 := by
      simp [he, hn.1, hn.2]
    rcases renameToOneTie_live C with hs | hs <;> rw [hs, ht] at hz
    all_goals rcases hd with rfl | rfl
    all_goals simp [MvPolynomial.coeff_monomial, hxy, Ne.symm hxy] at hz
  have hx := hmatch dx (Or.inl rfl)
  have hy := hmatch dy (Or.inr rfl)
  have hdeg : C.coordinateDegree u = C.coordinateDegree v := by
    simpa [u,v,C.coordinateDegree_rename] using C.original.degree_eq
  have hpair : C.coordinateDegree dx = C.coordinateDegree dy := by
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact False.elim (hxy (hx.symm.trans hy))
    · simpa [hx,hy] using hdeg
    · simpa [hx,hy] using hdeg.symm
    · exact False.elim (hxy (hx.symm.trans hy))
  simpa [C.coordinateDegree_formula, dx,dy] using hpair

theorem normalize_preserves_coordinateDegree (d : Fin 3 →₀ ℕ) :
    C.coordinateDegree (normalExponent (normalizeExponent C.a C.b C.c d)) =
      C.coordinateDegree d := by
  rw [C.coordinateDegree_formula, C.coordinateDegree_formula]
  simp only [normalExponent_x, normalExponent_y, normalExponent_z,
    normalizeExponent, exponentRaw, Normal.normalize_x, Normal.normalize_y, Normal.normalize_z]
  have hdiv : d 0 % C.a + d 0 / C.a * C.a = d 0 := by
    simpa [Nat.mul_comm] using Nat.mod_add_div (d 0) C.a
  have ht := C.weighted_tie_equation
  calc
    _ = (d 0 % C.a + d 0 / C.a * C.a) * D.tailGen i (C.sigma.symm 0) +
        d 1 * D.tailGen i (C.sigma.symm 1) + d 2 * D.tailGen i (C.sigma.symm 2) := by
      nlinarith [congrArg (fun n : ℕ => (d 0 / C.a) * n) ht]
    _ = _ := by rw [hdiv]
end OneTieCoordinates

namespace TaggedBudgetOneNormalization
variable (T : TaggedBudgetOneNormalization D i)

def externalTailExponent (g : D.BaseAdaptedGlobalConnector i) : Fin 3 →₀ ℕ :=
  (normalExponent (T.normalizedOfExternal g)).mapDomain T.presentation.coordinates.sigma.symm

theorem normalized_external_degree (g : D.BaseAdaptedGlobalConnector i) :
    tailDegree D i (T.externalTailExponent g) = g.1.1 := by
  change T.presentation.coordinates.coordinateDegree
    (normalExponent (normalizeExponent _ _ _ (T.rawOfExternal g))) = _
  rw [T.presentation.coordinates.normalize_preserves_coordinateDegree]
  change T.presentation.coordinates.coordinateDegree
    ((D.connectorRightTail i g).mapDomain T.presentation.coordinates.sigma) = _
  rw [T.presentation.coordinates.coordinateDegree_rename]
  exact (restrictToTails_degree D i _ (D.connector_target_base_zero i g)).trans
    (D.factorizationAt_degree _)

def normalizedExternalFactorization (g : D.BaseAdaptedGlobalConnector i) : D.FactorizationAt g.1.1 :=
  ⟨extendTailExponent i (T.externalTailExponent g), D.mem_factorizations.mpr
    ((weightedDegree_extendTailExponent D i _).trans (T.normalized_external_degree g))⟩

theorem normalized_external_factorization_at_betti_degree (g : D.BaseAdaptedGlobalConnector i) :
    (T.normalizedExternalFactorization g).1 = extendTailExponent i (T.externalTailExponent g) ∧
    (T.normalizedExternalFactorization g).1 i = 0 ∧
    D.weightedDegree (T.normalizedExternalFactorization g).1 = g.1.1 :=
  ⟨rfl, extendTailExponent_base _ _, D.factorizationAt_degree _⟩
end TaggedBudgetOneNormalization
end
end P23.Semigroup
