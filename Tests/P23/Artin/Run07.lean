import P23.Artin.CanonicalDual
import P23.OneTie.CoverGeometry

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {a b c : ℕ} [NeZero a]
variable {k : Type*} [Field k]

/-- RED: a nonempty root set must contain the unit in its standard set. -/
example (S : Finset (Normal a b c)) (hS : S.Nonempty) :
    (1 : Normal a b c) ∈ standardSet S :=
  one_mem_standardSet S hS

/-- RED: the Artin carrier is the finite vector space on surviving monomials. -/
example (S : Finset (Normal a b c)) : Type _ := MonomialArtin k S

/-- RED: standard monomials form the canonical basis. -/
example (S : Finset (Normal a b c)) :
    Module.Basis (MonomialIndex S) k (MonomialArtin k S) :=
  monomialBasis k S

/-- RED: multiplication is exactly normalized multiplication truncated at the
standard-set boundary. -/
example (S : Finset (Normal a b c)) (p q : Normal a b c)
    (hp : p ∈ standardFinset S) (hq : q ∈ standardFinset S) :
    X (k := k) S p hp * X (k := k) S q hq =
      if h : p * q ∈ standardFinset S then X (k := k) S (p * q) h else 0 :=
  X_mul_X (k := k) S p q hp hq

/-- RED: the surviving unit basis vector is the algebra unit. -/
example (S : Finset (Normal a b c)) (hS : S.Nonempty) :
    X (k := k) S 1 (one_mem_standardFinset S hS) = 1 :=
  X_one (k := k) S hS

/-- RED: finite dimension is exactly the number of surviving monomials. -/
example (S : Finset (Normal a b c)) :
    Module.finrank k (MonomialArtin k S) = (standardFinset S).card :=
  finrank_monomialArtin k S

/-- RED: liveness is exactly nonvanishing of the four load-bearing basis
elements. -/
example (S : Finset (Normal a b c)) :
    IsLiveTie S ↔
      BasisSurvives k S Normal.xGenerator ∧
      BasisSurvives k S Normal.yGenerator ∧
      BasisSurvives k S Normal.zGenerator ∧
      BasisSurvives k S liveTiePoint :=
  isLiveTie_iff_basisSurvives k S

/-- RED: the canonical module is the linear dual. -/
example (S : Finset (Normal a b c)) : Type _ := Omega k S

/-- RED: exact coefficient of the contragredient monomial action. -/
example (S : Finset (Normal a b c)) (m q s : MonomialIndex S) :
    (X (k := k) S m.1 m.2 • U (k := k) S s)
        (X (k := k) S q.1 q.2) =
      if m.1 * q.1 = s.1 then 1 else 0 :=
  X_smul_U_apply_X (k := k) S m q s

/-- RED: cancellation turns the exact coefficient action into an exact dual
basis action. -/
example (S : Finset (Normal a b c)) (m q s : MonomialIndex S)
    (h : m.1 * q.1 = s.1) :
    X (k := k) S m.1 m.2 • U (k := k) S s = U (k := k) S q :=
  X_smul_U_eq_U (k := k) S m q s h

/-- RED: selected roots generate the canonical dual as an Artin module. -/
example (S : Finset (Normal a b c)) :
    Submodule.span (MonomialArtin k S) (rootDualSet k S) = ⊤ :=
  rootDual_span_eq_top (k := k) S

/-- RED: exact monomial annihilator of a selected-root dual. -/
example (S : Finset (Normal a b c)) (s : Normal a b c) (hs : s ∈ S)
    (w : MonomialIndex S) :
    X (k := k) S w.1 w.2 • U (k := k) S (rootIndex S s hs) = 0 ↔ ¬ w.1 ∣ s :=
  X_smul_rootDual_eq_zero_iff (k := k) S s hs w

namespace ConcreteRegression

/-! Mixed wrapped multiplication and killed product. -/

def mixedRoot : Normal 3 2 1 := ⟨0, 2, 1, by decide⟩
def mixedX : Normal 3 2 1 := Normal.xGenerator
def mixedX2 : Normal 3 2 1 := ⟨2, 0, 0, by decide⟩
def mixedS : Finset (Normal 3 2 1) := {mixedRoot}

example : mixedX ∈ standardFinset mixedS := by decide
example : mixedX2 ∈ standardFinset mixedS := by decide
example : mixedRoot ∈ standardFinset mixedS := by decide
example : mixedX * mixedX2 = mixedRoot := by decide

example :
    X (k := ℚ) mixedS mixedX (by decide) *
        X (k := ℚ) mixedS mixedX2 (by decide) =
      X (k := ℚ) mixedS mixedRoot (by decide) := by
  rw [X_mul_X]
  split
  · congr
  · rename_i h
    exact (h (by decide)).elim

example :
    X (k := ℚ) mixedS mixedRoot (by decide) *
        X (k := ℚ) mixedS mixedX (by decide) = 0 := by
  rw [X_mul_X]
  split
  · rename_i h
    exact ((by decide : mixedRoot * mixedX ∉ standardFinset mixedS) h).elim
  · rfl

/-! Pure and nonprimitive wrapped endpoints. -/

def pureRoot : Normal 4 2 0 := ⟨0, 2, 0, by decide⟩
def pureX : Normal 4 2 0 := Normal.xGenerator
def pureX3 : Normal 4 2 0 := ⟨3, 0, 0, by decide⟩
def pureS : Finset (Normal 4 2 0) := {pureRoot}

example : pureX * pureX3 = pureRoot := by decide
example :
    X (k := ℚ) pureS pureX (by decide) * X (k := ℚ) pureS pureX3 (by decide) =
      X (k := ℚ) pureS pureRoot (by decide) := by
  rw [X_mul_X]
  split
  · congr
  · rename_i h
    exact (h (by decide)).elim

def nonprimitiveRoot : Normal 4 2 2 := ⟨0, 2, 2, by decide⟩
def nonprimitiveX : Normal 4 2 2 := Normal.xGenerator
def nonprimitiveX3 : Normal 4 2 2 := ⟨3, 0, 0, by decide⟩
def nonprimitiveS : Finset (Normal 4 2 2) := {nonprimitiveRoot}

example : nonprimitiveX * nonprimitiveX3 = nonprimitiveRoot := by decide
example :
    X (k := ℚ) nonprimitiveS nonprimitiveX (by decide) *
        X (k := ℚ) nonprimitiveS nonprimitiveX3 (by decide) =
      X (k := ℚ) nonprimitiveS nonprimitiveRoot (by decide) := by
  rw [X_mul_X]
  split
  · congr
  · rename_i h
    exact (h (by decide)).elim

/-! Concrete nonzero/zero dual actions and generation of a non-root dual. -/

def mixedRootIndex : MonomialIndex mixedS := ⟨mixedRoot, by decide⟩
def mixedXIndex : MonomialIndex mixedS := ⟨mixedX, by decide⟩
def mixedX2Index : MonomialIndex mixedS := ⟨mixedX2, by decide⟩

example : mixedX2 ∉ mixedS := by decide
example :
    X (k := ℚ) mixedS mixedX (by decide) • U (k := ℚ) mixedS mixedRootIndex =
      U (k := ℚ) mixedS mixedX2Index := by
  exact X_smul_U_eq_U (k := ℚ) mixedS mixedXIndex mixedX2Index mixedRootIndex
    (by decide)

def zeroRoot : Normal 3 2 1 := ⟨2, 0, 0, by decide⟩
def otherRoot : Normal 3 2 1 := ⟨0, 1, 0, by decide⟩
def twoRootS : Finset (Normal 3 2 1) := {zeroRoot, otherRoot}
def otherIndex : MonomialIndex twoRootS := ⟨otherRoot, by decide⟩

example :
    X (k := ℚ) twoRootS otherRoot (by decide) •
        U (k := ℚ) twoRootS (rootIndex twoRootS zeroRoot (by decide)) = 0 := by
  exact (X_smul_rootDual_eq_zero_iff (k := ℚ) twoRootS zeroRoot
    (by decide) otherIndex).2 (by
      rw [exact_divides_iff]
      simp [Normal.DividesCriterion, otherIndex, otherRoot, zeroRoot])

end ConcreteRegression

end

end P23.Artin
