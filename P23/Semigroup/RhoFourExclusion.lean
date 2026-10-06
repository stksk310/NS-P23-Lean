import P23.Semigroup.RhoFourResidualSource

/-! Semigroup realizability excludes rho four. No rho lower bound is asserted. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.OneTie P23.Presentation
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
namespace ResidualExclusion
variable (R : RhoFourResidualPureBase D i)
local instance : NeZero R.residual.a' := ⟨by have := R.residual.a'_ge_two; omega⟩

def residualTopBorder : Normal R.residual.a' R.residual.b' 0 :=
  ⟨0,R.residual.residual.u+R.residual.b'-1,R.residual.residual.C-1,
    Nat.pos_of_ne_zero (NeZero.ne _)⟩

theorem residualTopBorder_degree : residualDegree R (residualTopBorder R) = residualTopDegree R := by
  rw [residualDegree_formula]
  simp [residualTopBorder,ResidualTop.residualTopDegree,PureResidualThreeBorder.formalTop]

theorem residualSourceNormal_not_top (ht : D.semigroupType=3) (u : Fin 3 →₀ ℕ)
    (t : Fin 3) (hu : tailDegree D i u=D.n i+D.tailGen i t) :
    residualSourceNormal R u ≠ residualTopBorder R := by
  intro he
  have hd := congrArg (residualDegree R) he
  rw [residualSourceNormal_degree,residualTopBorder_degree,hu] at hd
  exact (rhoFourResidualTopPattern R ht).top_ne_base_add_tail t hd.symm

private theorem supported_non_top_border_unique
    (j : Fin 3) (p q : Normal R.residual.a' R.residual.b' 0)
    (hp : p ∈ borderFinset R.residual.roots) (hq : q ∈ borderFinset R.residual.roots)
    (hpn : p ≠ residualTopBorder R) (hqn : q ≠ residualTopBorder R)
    (hps : if j=2 then 0<p.z else 0<p.x ∨ 0<p.y)
    (hqs : if j=2 then 0<q.z else 0<q.x ∨ 0<q.y) : p=q := by
  rw [R.residual.residual.border] at hp hq
  simp only [Finset.mem_insert,Finset.mem_singleton] at hp hq
  have hp' : p=(⟨1,R.residual.residual.u,0,by have := R.residual.a'_ge_two; omega⟩ :
      Normal R.residual.a' R.residual.b' 0) ∨ p=zAxis R.residual.residual.C := by
    rcases hp with hp | hp | hp
    · exact Or.inl hp
    · exact Or.inr hp
    · exact False.elim (hpn hp)
  have hq' : q=(⟨1,R.residual.residual.u,0,by have := R.residual.a'_ge_two; omega⟩ :
      Normal R.residual.a' R.residual.b' 0) ∨ q=zAxis R.residual.residual.C := by
    rcases hq with hq | hq | hq
    · exact Or.inl hq
    · exact Or.inr hq
    · exact False.elim (hqn hq)
  by_cases hj : j=2
  all_goals simp only [hj,ite_true,ite_false] at hps hqs
  all_goals rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;>
    simp_all [zAxis]

theorem two_sources_same_residual_border (ht : D.semigroupType=3) (S : TwoTailSources D i) :
    residualSourceNormal R S.first_factorization = residualSourceNormal R S.second_factorization := by
  apply supported_non_top_border_unique R (tailToResidual R S.selected)
  · exact residualSourceNormal_mem_border R S.first_source _ S.first_degree
  · exact residualSourceNormal_mem_border R S.second_source _ S.second_degree
  · exact residualSourceNormal_not_top R ht _ S.first S.first_degree
  · exact residualSourceNormal_not_top R ht _ S.second S.second_degree
  · exact residualSourceNormal_selected_support R _ _ S.first_contains_selected
  · exact residualSourceNormal_selected_support R _ _ S.second_contains_selected

include R in
theorem residual_pure_base_impossible (ht : D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) : False := by
  obtain ⟨S⟩ := exists_two_tail_sources D i (rhoFourResidualTopPattern R ht) hn
  have he := congrArg (residualDegree R) (two_sources_same_residual_border R ht S)
  rw [residualSourceNormal_degree,residualSourceNormal_degree,S.first_degree,S.second_degree] at he
  exact S.degrees_ne he

end ResidualExclusion
export ResidualExclusion (residualTopBorder residualTopBorder_degree residualSourceNormal_not_top
  two_sources_same_residual_border residual_pure_base_impossible)

theorem type_three_ng_semigroupRho_ne_four (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) : D.semigroupRho ≠ 4 := by
  intro hr
  obtain ⟨R⟩ := rho_four_residual_pure_at_every_base D ht hn hr 0
  exact residual_pure_base_impossible R ht hn

structure RhoFourRealizabilityExclusion (D : FourGeneratedNumericalSemigroup) : Prop where
  rhoNeFour : D.semigroupRho ≠ 4

theorem rhoFourRealizabilityExclusion (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType=3) (hn : SemigroupNearlyGorenstein D) : RhoFourRealizabilityExclusion D :=
  ⟨type_three_ng_semigroupRho_ne_four D ht hn⟩
end
end P23.Semigroup
