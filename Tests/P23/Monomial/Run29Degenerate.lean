import P23.Monomial.PlainGeometry
import P23.Monomial.PlainEmbedding

/- Permanent specification regression. No bounded search enters production. -/
namespace P23.Monomial.Run29Regression
noncomputable section
def E (x y z : ℕ) : PlainExp := Finsupp.single 0 x + Finsupp.single 1 y + Finsupp.single 2 z
def badRoots : Finset PlainExp := {E 2 0 0,E 1 1 0,E 0 2 0}
def badBorder : Finset PlainExp := {E 3 0 0,E 2 1 0,E 1 2 0,E 0 3 0,E 0 0 1}
def goodRoots : Finset PlainExp := {E 1 1 0,E 1 0 1,E 0 1 1}
def goodBorder : Finset PlainExp := {E 2 0 0,E 0 2 0,E 0 0 2,E 1 1 1}

theorem E_coordinates (p : PlainExp) : E (p 0) (p 1) (p 2) = p := by
  ext j
  fin_cases j <;> simp [E]

@[simp] theorem E_eq_E (x y z x' y' z' : ℕ) :
    E x y z = E x' y' z' ↔ x = x' ∧ y = y' ∧ z = z' := by
  constructor
  · intro h
    have h0 := congrArg (fun p : PlainExp => p 0) h
    have h1 := congrArg (fun p : PlainExp => p 1) h
    have h2 := congrArg (fun p : PlainExp => p 2) h
    simpa [E] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨rfl,rfl,rfl⟩; rfl

theorem bad_root_count : badRoots.card = 3 := by simp [badRoots]
theorem bad_border_count : badBorder.card = 5 := by simp [badBorder]
theorem good_root_count : goodRoots.card = 3 := by simp [goodRoots]
theorem good_border_count : goodBorder.card = 4 := by simp [goodBorder]

theorem bad_standard (p : PlainExp) :
    p ∈ plainStandardSet badRoots ↔ p 2 = 0 ∧ p 0 + p 1 ≤ 2 := by
  simp [plainStandardSet,badRoots,plainDivides,Fin.forall_fin_succ,E]
  omega

theorem bad_antichain : PlainRootAntichain badRoots := by
  intro p hp q hq h
  simp only [badRoots,Finset.mem_insert,Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    norm_num [plainDivides,Fin.forall_fin_succ,E] at *

theorem bad_centres : HasPlainDirectionalCentres badRoots := by
  intro j
  fin_cases j <;> refine ⟨E 1 1 0,?_,?_⟩
  all_goals try { simp [badRoots] }
  all_goals
    intro s hs hpos
    simp only [badRoots,Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;>
      norm_num [plainDivides,plainPredecessor_apply,Fin.forall_fin_succ,E,
        Finsupp.single_apply, show (0 : Fin 3) ≠ 2 by decide,
        show (1 : Fin 3) ≠ 2 by decide] at *

theorem bad_variables_do_not_survive : ¬ PlainVariablesSurvive badRoots := by
  intro h
  have hz := (bad_standard (plainUnitVector 2)).mp (h 2)
  simp at hz

theorem bad_border_exact : plainBorderFinset badRoots = badBorder := by
  ext p
  rw [mem_plainBorderFinset_iff]
  simp only [bad_standard, Fin.forall_fin_succ, plainPredecessor_apply]
  have he : ∀ x y z, p = E x y z ↔ p 0 = x ∧ p 1 = y ∧ p 2 = z := by
    intro x y z
    constructor
    · intro h; simp [h,E]
    · rintro ⟨hx,hy,hz⟩
      simpa [hx,hy,hz] using (E_coordinates p).symm
  simp [badBorder,he]
  omega

theorem good_survival : PlainVariablesSurvive goodRoots := by
  intro j
  fin_cases j
  · exact ⟨E 1 1 0,by simp [goodRoots],by simp [plainDivides,Fin.forall_fin_succ,E]⟩
  · exact ⟨E 1 1 0,by simp [goodRoots],by simp [plainDivides,Fin.forall_fin_succ,E]⟩
  · exact ⟨E 1 0 1,by simp [goodRoots],by simp [plainDivides,Fin.forall_fin_succ,E]⟩

theorem good_antichain : PlainRootAntichain goodRoots := by
  intro p hp q hq h
  simp only [goodRoots,Finset.mem_insert,Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    norm_num [plainDivides,Fin.forall_fin_succ,E,Finsupp.single_apply,
      show (0 : Fin 3) ≠ 2 by decide,show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide] at *
theorem good_centres : HasPlainDirectionalCentres goodRoots := by
  intro j
  fin_cases j
  · refine ⟨E 0 1 1,by simp [goodRoots],?_⟩
    intro s hs hpos
    simp only [goodRoots,Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;>
      norm_num [plainDivides,plainPredecessor_apply,Fin.forall_fin_succ,E,
        Finsupp.single_apply,show (0 : Fin 3) ≠ 2 by decide,show (1 : Fin 3) ≠ 2 by decide] at *
  · refine ⟨E 1 0 1,by simp [goodRoots],?_⟩
    intro s hs hpos
    simp only [goodRoots,Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;>
      norm_num [plainDivides,plainPredecessor_apply,Fin.forall_fin_succ,E,
        Finsupp.single_apply,show (0 : Fin 3) ≠ 2 by decide,show (1 : Fin 3) ≠ 2 by decide] at *
  · refine ⟨E 1 1 0,by simp [goodRoots],?_⟩
    intro s hs hpos
    simp only [goodRoots,Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;>
      norm_num [plainDivides,plainPredecessor_apply,Fin.forall_fin_succ,E,
        Finsupp.single_apply,show (0 : Fin 3) ≠ 2 by decide,show (1 : Fin 3) ≠ 2 by decide,
        show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide] at *
    all_goals simp only [Finsupp.single_apply] at *
    all_goals split_ifs at * <;> omega

theorem good_standard (p : PlainExp) :
    p ∈ plainStandardSet goodRoots ↔ p 0 ≤ 1 ∧ p 1 ≤ 1 ∧ p 2 ≤ 1 ∧ p 0+p 1+p 2≤2 := by
  simp [plainStandardSet,goodRoots,plainDivides,Fin.forall_fin_succ,E]
  omega

theorem good_border_exact : plainBorderFinset goodRoots=goodBorder := by
  ext p
  rw [mem_plainBorderFinset_iff]
  simp only [good_standard,Fin.forall_fin_succ,plainPredecessor_apply]
  have he : ∀ x y z, p=E x y z ↔ p 0=x ∧ p 1=y ∧ p 2=z := by
    intro x y z
    constructor
    · intro h; simp [h,E]
    · rintro ⟨hx,hy,hz⟩; simpa [hx,hy,hz] using (E_coordinates p).symm
  simp [goodBorder,he]
  omega

theorem good_border_not_five : (plainBorderFinset goodRoots).card ≠ 5 := by
  rw [good_border_exact,good_border_count]
  decide

theorem bad_nonempty : badRoots.Nonempty := by simp [badRoots]

theorem bad_actual_embedding_dimension :
    plainEmbeddingDimension ℚ badRoots bad_nonempty = 2 := by
  unfold plainEmbeddingDimension
  rw [Module.finrank_eq_card_basis (plainCotangentBasis (k := ℚ) badRoots bad_nonempty)]
  rw [Fintype.card_subtype]
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  norm_num [hu, Finset.filter_insert, Finset.filter_singleton,
    mem_plainStandardFinset, bad_standard, plainUnitVector_apply,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (0 : Fin 3) ≠ 1 by decide]
end
end P23.Monomial.Run29Regression
