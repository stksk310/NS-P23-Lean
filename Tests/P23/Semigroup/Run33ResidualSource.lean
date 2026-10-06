import P23.Semigroup.RhoFourExclusion
open P23.Semigroup P23.OneTie P23.Presentation FourGeneratedNumericalSemigroup
#check canonicalSourceNormal
#check residualSourceNormal
#check residualSourceNormal_degree
#check source_normal_mem_original_border
#check residualSourceNormal_mem_border
#check residualSourceNormal_selected_support

noncomputable section
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
variable (R : RhoFourResidualPureBase D i)
example {d : ℕ} (hs : IsTailSource D i d) (u : Fin 3 →₀ ℕ) (hu : tailDegree D i u=d) :
    canonicalSourceNormal R.tagged u∈borderFinset R.tagged.presentation.roots :=
  source_normal_mem_original_border R.tagged hs u hu
example {d : ℕ} (hs : IsTailSource D i d) (u : Fin 3 →₀ ℕ) (hu : tailDegree D i u=d) :
    ∃ g ∈ R.tagged.externalTags,
      R.tagged.normalizedOfExternal g=canonicalSourceNormal R.tagged u ∧
        ∀ h ∈ R.tagged.externalTags,
          R.tagged.normalizedOfExternal h=canonicalSourceNormal R.tagged u → h=g :=
  source_normal_external_tag R.tagged hs u hu
local instance : NeZero R.residual.a' := ⟨by have := R.residual.a'_ge_two; omega⟩
example (u : Fin 3 →₀ ℕ) : residualDegree R (residualSourceNormal R u)=tailDegree D i u :=
  residualSourceNormal_degree R u
example {d : ℕ} (hs : IsTailSource D i d) (u : Fin 3 →₀ ℕ) (hu : tailDegree D i u=d) :
    residualSourceNormal R u ∈ borderFinset R.residual.roots := residualSourceNormal_mem_border R hs u hu
example (u : Fin 3 →₀ ℕ) (j : Fin 3) (hj : 0<u j) :
    if tailToResidual R j=2 then 0<(residualSourceNormal R u).z else
      0<(residualSourceNormal R u).x ∨ 0<(residualSourceNormal R u).y :=
  residualSourceNormal_selected_support R u j hj
example (ht : D.semigroupType=3) (S : TwoTailSources D i) :
    residualSourceNormal R S.first_factorization=residualSourceNormal R S.second_factorization :=
  two_sources_same_residual_border R ht S
example : residualDegree R (residualTopBorder R)=residualTopDegree R := residualTopBorder_degree R
example (ht : D.semigroupType=3) (u : Fin 3 →₀ ℕ) (t : Fin 3)
    (hu : tailDegree D i u=D.n i+D.tailGen i t) :
    residualSourceNormal R u ≠ residualTopBorder R := residualSourceNormal_not_top R ht u t hu
example (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) : False :=
  residual_pure_base_impossible R ht hn

-- Safety regression: x-positive raw exponent can lose all x support.
example : (normalizeExponent 2 2 0 (Finsupp.single 0 2)).x=0 := by
  norm_num [normalizeExponent,exponentRaw,Normal.normalize]
example : (normalizeExponent 2 2 0 (Finsupp.single 0 2)).y=2 := by
  norm_num [normalizeExponent,exponentRaw,Normal.normalize]
example : 0 < (normalizeExponent 2 2 0 (Finsupp.single 0 2)).y := by norm_num [normalizeExponent,exponentRaw,Normal.normalize]
