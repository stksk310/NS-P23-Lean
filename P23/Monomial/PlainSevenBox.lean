import P23.Monomial.PlainTypeThreeFrontier

namespace P23.Monomial
noncomputable section

/-- Disjoint coordinate box and its two one-step axis extensions. -/
abbrev SevenBoxShape (A B C : ℕ) := (Fin A × Fin B × Fin C) ⊕ Fin 2

def sevenBoxExponent (A B C : ℕ) : SevenBoxShape A B C → PlainExp
  | .inl p => plainExp p.1 p.2.1 p.2.2
  | .inr j => if j=0 then plainExp A 0 0 else plainExp 0 B 0

theorem sevenBoxShape_card (A B C : ℕ) :
    Fintype.card (SevenBoxShape A B C)=A*B*C+2 := by
  simp [SevenBoxShape,Nat.mul_assoc]

theorem sevenBoxExponent_injective (A B C : ℕ) (hA : 0<A) (hB : 0<B) :
    Function.Injective (sevenBoxExponent A B C) := by
  intro p q he
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have hh : (p.1:ℕ)=(q.1:ℕ) ∧ (p.2.1:ℕ)=(q.2.1:ℕ) ∧ (p.2.2:ℕ)=(q.2.2:ℕ) := by
        simpa [sevenBoxExponent,plainExp_eq] using he
      congr 1
      apply Prod.ext
      · exact Fin.ext hh.1
      · exact Prod.ext (Fin.ext hh.2.1) (Fin.ext hh.2.2)
    | inr j =>
      fin_cases j <;> simp [sevenBoxExponent,plainExp_eq] at he
      · have := p.1.isLt; omega
      · have := p.2.1.isLt; omega
  | inr j =>
    cases q with
    | inl q =>
      fin_cases j <;> simp [sevenBoxExponent,plainExp_eq] at he
      · have := q.1.isLt; omega
      · have := q.2.1.isLt; omega
    | inr k =>
      fin_cases j <;> fin_cases k <;> simp [sevenBoxExponent,plainExp_eq] at he ⊢
      all_goals omega

theorem sevenBox_standard_iff (A B C : ℕ) (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (p : PlainExp) :
    p∈plainStandardSet (plainDominantAxisRoots (A-1) (B-1) (C-1)) ↔
    (p 0<A ∧ p 1<B ∧ p 2<C) ∨ p=plainExp A 0 0 ∨ p=plainExp 0 B 0 := by
  rw [plainDominantAxis_standard]
  simp only [plainExp_eq_coordinates]
  omega

theorem sevenBoxExponent_range (A B C : ℕ) (hA : 0<A) (hB : 0<B) (hC : 0<C)
    (p : PlainExp) :
    (∃ u : SevenBoxShape A B C,sevenBoxExponent A B C u=p) ↔
    p∈plainStandardSet (plainDominantAxisRoots (A-1) (B-1) (C-1)) := by
  rw [sevenBox_standard_iff A B C hA hB hC]
  constructor
  · rintro ⟨u,rfl⟩
    cases u with
    | inl u =>
      exact Or.inl ⟨by simpa [sevenBoxExponent] using u.1.isLt,
        by simpa [sevenBoxExponent] using u.2.1.isLt,
        by simpa [sevenBoxExponent] using u.2.2.isLt⟩
    | inr j => fin_cases j <;> simp [sevenBoxExponent]
  · rintro (hp | hp | hp)
    · exact ⟨.inl (⟨p 0,hp.1⟩,⟨p 1,hp.2.1⟩,⟨p 2,hp.2.2⟩),plainExp_coordinates p⟩
    · exact ⟨.inr 0,by simpa [sevenBoxExponent] using hp.symm⟩
    · exact ⟨.inr 1,by simpa [sevenBoxExponent] using hp.symm⟩

theorem plain_axis_pair_exact_box (p q r : PlainExp)
    (ha : PlainRootAntichain {p,q,r}) (hc : HasPlainDirectionalCentres {p,q,r})
    (hp : 0<p 0 ∧ 0<p 1 ∧ 0<p 2)
    (hq : 0<q 0 ∧ q 1=0 ∧ q 2=0)
    (hr : r 0=0 ∧ 0<r 1 ∧ r 2=0) :
    ({p,q,r} : Finset PlainExp)=plainDominantAxisRoots (p 0) (p 1) (p 2) := by
  have centre (j : Fin 3) (hj : j ≠ 2) : PlainDirectionalCentre {p,q,r} j p := by
    obtain ⟨c,hc⟩ := hc j
    have hb := hc.2 p (by simp) (by fin_cases j <;> simp_all)
    have hb2 := hb 2
    have hh : p 2 ≤ c 2 := by
      simpa [plainPredecessor_apply,hj,Ne.symm hj] using hb2
    have hm := hc.1
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with h | h | h
    · simpa [h] using hc
    · subst c; omega
    · subst c; omega
  have hqp : q ≠ p := by intro h; have he := congrArg (fun s : PlainExp => s 1) h; omega
  have hrp : r ≠ p := by intro h; have he := congrArg (fun s : PlainExp => s 0) h; omega
  have hx := (plain_centre_other_root_coordinates {p,q,r} ha
    (centre 0 (by decide)) (by simp) hqp hq.1).1
  have hy := (plain_centre_other_root_coordinates {p,q,r} ha
    (centre 1 (by decide)) (by simp) hrp hr.2.1).1
  exact plain_three_finset_congr (plainExp_coordinates p).symm
    (by rw [plainExp_eq_coordinates]; omega)
    (by rw [plainExp_eq_coordinates]; omega)

theorem plain_permuted_pair_exact_box (e : Equiv.Perm (Fin 3)) (p q r : PlainExp)
    (ha : PlainRootAntichain {p,q,r}) (hc : HasPlainDirectionalCentres {p,q,r})
    (hp : 0<p (e 0) ∧ 0<p (e 1) ∧ 0<p (e 2))
    (hq : 0<q (e 0) ∧ q (e 1)=0 ∧ q (e 2)=0)
    (hr : r (e 0)=0 ∧ 0<r (e 1) ∧ r (e 2)=0) :
    ∃ A B C, 2≤A ∧ 2≤B ∧ 2≤C ∧
      ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e)=
        plainDominantAxisRoots (A-1) (B-1) (C-1) := by
  have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
      {plainCoordinatePerm e p,plainCoordinatePerm e q,plainCoordinatePerm e r} := by simp
  have he := plain_axis_pair_exact_box (plainCoordinatePerm e p) (plainCoordinatePerm e q)
    (plainCoordinatePerm e r) (by rw [←hi]; exact plainAntichain_coordinatePerm e _ ha)
    (by rw [←hi]; exact plainCentres_coordinatePerm e _ hc)
    (by simpa using hp) (by simpa using hq) (by simpa using hr)
  refine ⟨p (e 0)+1,p (e 1)+1,p (e 2)+1,by omega,by omega,by omega,?_⟩
  simpa [hi] using he

theorem plain_pure_axes_exact_box (p q r : PlainExp)
    (hqr : q≠r) (ha : PlainRootAntichain {p,q,r})
    (hc : HasPlainDirectionalCentres {p,q,r})
    (hp : 0<p 0 ∧ 0<p 1 ∧ 0<p 2) (hq : plainPureAxis q) (hr : plainPureAxis r) :
    ∃ e : Equiv.Perm (Fin 3), ∃ A B C, 2≤A ∧ 2≤B ∧ 2≤C ∧
      ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e)=
        plainDominantAxisRoots (A-1) (B-1) (C-1) := by
  have hnc : ¬plainDivides q r := fun h => hqr (ha q (by simp) r (by simp) h)
  have hnc' : ¬plainDivides r q := fun h => hqr (ha r (by simp) q (by simp) h).symm
  have same (j : Fin 3) (hqz : ∀ a, a≠j → q a=0)
      (hrz : ∀ a, a≠j → r a=0) : False := by
    by_cases hle : q j≤r j
    · apply hnc; intro a; by_cases he : a=j
      · simpa [he] using hle
      · simp [hqz a he,hrz a he]
    · apply hnc'; intro a; by_cases he : a=j
      · simp only [he]; omega
      · simp [hqz a he,hrz a he]
  rcases hq with hq | hq | hq <;> rcases hr with hr | hr | hr
  · exfalso; apply same 0
    all_goals intro j hj; fin_cases j <;> simp_all
  · refine ⟨Equiv.refl _,?_⟩
    exact plain_permuted_pair_exact_box _ p q r ha hc hp hq hr
  · refine ⟨Equiv.swap (1 : Fin 3) 2,?_⟩
    apply plain_permuted_pair_exact_box _ p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · refine ⟨Equiv.swap (0 : Fin 3) 1,?_⟩
    apply plain_permuted_pair_exact_box _ p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · exfalso; apply same 1
    all_goals intro j hj; fin_cases j <;> simp_all
  · refine ⟨(Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1),?_⟩
    apply plain_permuted_pair_exact_box _ p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · refine ⟨(Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2),?_⟩
    apply plain_permuted_pair_exact_box _ p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · refine ⟨Equiv.swap (0 : Fin 3) 2,?_⟩
    apply plain_permuted_pair_exact_box _ p q r ha hc
    all_goals simp [Equiv.swap_apply_def]; omega
  · exfalso; apply same 2
    all_goals intro j hj; fin_cases j <;> simp_all

theorem plain_seven_border_exact_box (R : Finset PlainExp)
    (ha : PlainRootAntichain R) (h3 : R.card=3) (hv : PlainVariablesSurvive R)
    (hc : HasPlainDirectionalCentres R) (h7 : (plainBorderFinset R).card=7) :
    ∃ e : Equiv.Perm (Fin 3), ∃ A B C, 2≤A ∧ 2≤B ∧ 2≤C ∧
      R.image (plainCoordinatePerm e)=plainDominantAxisRoots (A-1) (B-1) (C-1) := by
  obtain ⟨p,q,r,hpq,hpr,hqr,rfl⟩ := Finset.card_eq_three.mp h3
  rcases plain_three_root_coordinate_patterns p q r hpq hpr hqr ha hv hc with h | h | h
  · have := plain_triangle_pattern_card p q r h; omega
  · have := plain_plane_pattern_card p q r hpq hpr hqr ha h; omega
  · rcases h with h | h | h
    · exact plain_pure_axes_exact_box p q r hqr ha hc ⟨h.1,h.2.1,h.2.2.1⟩ h.2.2.2.1 h.2.2.2.2
    · have he : ({p,q,r} : Finset PlainExp)={q,r,p} := by ext; simp; tauto
      rw [he]
      exact plain_pure_axes_exact_box q r p (Ne.symm hpr) (he ▸ ha) (he ▸ hc)
        ⟨h.1,h.2.1,h.2.2.1⟩ h.2.2.2.1 h.2.2.2.2
    · have he : ({p,q,r} : Finset PlainExp)={r,p,q} := by ext; simp; tauto
      rw [he]
      exact plain_pure_axes_exact_box r p q hpq (he ▸ ha) (he ▸ hc)
        ⟨h.1,h.2.1,h.2.2.1⟩ h.2.2.2.1 h.2.2.2.2

end
end P23.Monomial
