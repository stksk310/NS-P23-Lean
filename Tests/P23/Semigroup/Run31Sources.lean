import P23.Semigroup.TailSources

/-! Typed contracts for actual additive source APIs; no degree-injectivity premise. -/
namespace P23.Semigroup
open P23.Monomial

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) : TailInH D i 0 :=
  tailInH_zero D i

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) {h r : ℕ}
    (hh : TailInH D i h) (hr : TailInH D i r) : TailInH D i (h+r) :=
  tailInH_add D i hh hr

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) : ¬TailInH D i (D.n i) :=
  not_tailInH_base D i

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) {h r : ℕ}
    (hh : TailInK D i h) (hr : TailInH D i r) : TailInK D i (h+r) :=
  tailInK_add_tailInH D i hh hr

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (u : PlainExp) :
    MvPolynomial.monomial u (1 : ℚ) ∈ chosenBaseDefiningIdeal (k := ℚ) D i ↔
      TailInK D i (tailDegree D i u) :=
  tail_monomial_mem_chosenBaseDefiningIdeal_iff D i u

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (h : ℕ) :
    IsTailSource D i h ↔ TailInK D i h ∧
      ¬∃ k r : ℕ, TailInK D i k ∧ TailInH D i r ∧ r≠0 ∧ h=k+r :=
  isTailSource_iff_no_nonzero_tail_predecessor D i h

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (P : TailSocleTopPattern D i) :
    Function.Injective (fun j => aperySocleDegree D i (P.byTail j)) :=
  P.socleDegree_injective

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (P : TailSocleTopPattern D i)
    (hn : SemigroupNearlyGorenstein D) :
    ∃ s : Fin 3, ∀ t : Fin 3, t≠s → ∃ γ : D.Gamma,
      D.n i + D.tailGen i t = D.tailGen i s + γ.1 :=
  exists_selected_tail_ng_relations D i P hn

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (s t : Fin 3)
    (hst : s≠t) (γ : D.Gamma)
    (he : D.n i + D.tailGen i t = D.tailGen i s + γ.1) :
    IsTailSource D i (D.n i + D.tailGen i t) :=
  source_of_ng_tail_relation D i s t hst γ he

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (s t : Fin 3)
    (hst : s≠t) (γ : D.Gamma)
    (he : D.n i + D.tailGen i t = D.tailGen i s + γ.1) :
    ∃ u : PlainExp, tailDegree D i u = D.n i + D.tailGen i t ∧ 0<u s :=
  exists_tail_factorization_containing_selected D i s t hst γ he

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (P : TailSocleTopPattern D i)
    (hn : SemigroupNearlyGorenstein D) : Nonempty (TwoTailSources D i) :=
  exists_two_tail_sources D i P hn

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4) (G : Finset PlainExp)
    (hI : plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal (k := ℚ) D i)
    {d : ℕ} (hs : IsTailSource D i d) (u : PlainExp) (hu : tailDegree D i u=d)
    (hm : MvPolynomial.monomial u (1 : ℚ) ∈ plainMonomialIdeal ℚ G) : u∈G :=
  source_factorization_eq_displayed_monomial D i G hI hs u hu hm

end P23.Semigroup
