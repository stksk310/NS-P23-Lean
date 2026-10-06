import P23.OneTie.Divisibility

#check P23.OneTie.exact_divides_iff
#check P23.OneTie.Normal.yPredecessor_mul
#check P23.OneTie.Normal.zPredecessor_mul
#check P23.OneTie.Normal.xPredecessor_mul
#check P23.OneTie.Normal.wrappedXPredecessor_mul
#check P23.OneTie.Normal.yPredecessor_unique
#check P23.OneTie.Normal.zPredecessor_unique
#check P23.OneTie.Normal.xPredecessor_unique
#check P23.OneTie.Normal.wrappedXPredecessor_unique

namespace P23.OneTie.Run01Regression

open Normal

example : (normalize 5 2 3 (by decide) ⟨12, 4, 1⟩).x = 2 := by decide
example : (normalize 5 2 3 (by decide) ⟨12, 4, 1⟩).y = 8 := by decide
example : (normalize 5 2 3 (by decide) ⟨12, 4, 1⟩).z = 7 := by decide

def mixedP : Normal 5 2 3 := ⟨4, 1, 2, by decide⟩
def mixedS : Normal 5 2 3 := ⟨1, 3, 5, by decide⟩

example : mixedP ∣ mixedS :=
  (P23.OneTie.exact_divides_iff mixedP mixedS).2
    (by simp [Normal.DividesCriterion, mixedP, mixedS])

def pureP : Normal 5 2 0 := ⟨4, 1, 7, by decide⟩
def pureS : Normal 5 2 0 := ⟨1, 3, 7, by decide⟩

example : pureP ∣ pureS :=
  (P23.OneTie.exact_divides_iff pureP pureS).2
    (by simp [Normal.DividesCriterion, pureP, pureS])

def ordinaryP : Normal 5 2 3 := ⟨1, 2, 3, by decide⟩
def ordinaryS : Normal 5 2 3 := ⟨4, 2, 3, by decide⟩

example : ordinaryP ∣ ordinaryS :=
  (P23.OneTie.exact_divides_iff ordinaryP ordinaryS).2
    (by simp [Normal.DividesCriterion, ordinaryP, ordinaryS])

def nondivP : Normal 5 2 3 := ⟨4, 2, 2, by decide⟩
def nondivS : Normal 5 2 3 := ⟨1, 3, 4, by decide⟩

example : ¬nondivP ∣ nondivS := by
  rw [P23.OneTie.exact_divides_iff]
  simp [Normal.DividesCriterion, nondivP, nondivS]

example : (Normal.xGenerator : Normal 1 2 3) = ⟨0, 2, 3, by decide⟩ := by decide

def aOneTarget : Normal 1 2 3 := ⟨0, 2, 3, by decide⟩

example :
    (aOneTarget.wrappedXPredecessor rfl (by decide) (by decide)) *
        Normal.xGenerator = aOneTarget :=
  Normal.wrappedXPredecessor_mul aOneTarget rfl (by decide) (by decide)

example : (Normal.xGenerator : Normal 1 0 0) = 1 := by decide

example :
    (⟨2, 1, 1, by decide⟩ : Normal 5 2 3).xPredecessor (by decide) *
        Normal.xGenerator = ⟨2, 1, 1, by decide⟩ :=
  Normal.xPredecessor_mul _ (by decide)

example :
    (⟨2, 1, 1, by decide⟩ : Normal 5 2 3).yPredecessor (by decide) *
        Normal.yGenerator = ⟨2, 1, 1, by decide⟩ :=
  Normal.yPredecessor_mul _ (by decide)

example :
    (⟨2, 1, 1, by decide⟩ : Normal 5 2 3).zPredecessor (by decide) *
        Normal.zGenerator = ⟨2, 1, 1, by decide⟩ :=
  Normal.zPredecessor_mul _ (by decide)

end P23.OneTie.Run01Regression
