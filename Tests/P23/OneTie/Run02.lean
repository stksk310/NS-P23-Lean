import P23.OneTie.DirectionalCentre

#check P23.OneTie.Normal.mul_left_cancel
#check P23.OneTie.Normal.mul_right_cancel
#check P23.OneTie.Normal.mem_divisorDownset_iff
#check P23.OneTie.Normal.mem_divisorFinset_iff
#check P23.OneTie.Normal.mem_divisorDownset_iff_blocks
#check P23.OneTie.mem_standardSet_iff
#check P23.OneTie.mem_standardFinset_iff
#check P23.OneTie.Normal.predecessor_eq_some_iff_mul
#check P23.OneTie.isMinimalBorder_iff
#check P23.OneTie.mem_borderCandidateFinset_iff
#check P23.OneTie.isDirectionalCentre_x_iff
#check P23.OneTie.isDirectionalCentre_y_iff
#check P23.OneTie.isDirectionalCentre_z_iff

namespace P23.OneTie.Run02Regression

open Normal

abbrev N := Normal 3 1 1

def root : N := ⟨0, 2, 2, by decide⟩
def ordinaryPoint : N := ⟨0, 2, 2, by decide⟩
def wrappedPoint : N := ⟨2, 1, 1, by decide⟩
def failedWrappedPoint : N := ⟨2, 2, 1, by decide⟩

example : ordinaryPoint ∈ divisorFinset root := by decide
example : wrappedPoint ∈ divisorFinset root := by decide
example : failedWrappedPoint ∉ divisorFinset root := by decide

def leftFactor : N := ⟨2, 3, 4, by decide⟩
def rightFactor : N := ⟨1, 5, 6, by decide⟩

example : leftFactor * rightFactor = leftFactor * rightFactor := rfl
example (q r : N) (h : leftFactor * q = leftFactor * r) : q = r :=
  Normal.mul_left_cancel h

def ordinaryX : N := ⟨2, 1, 1, by decide⟩
def wrappedX : N := ⟨0, 1, 1, by decide⟩
def noX : N := ⟨0, 0, 0, by decide⟩

example : predecessor .x ordinaryX = some ⟨1, 1, 1, by decide⟩ := by decide
example : predecessor .x wrappedX = some ⟨2, 0, 0, by decide⟩ := by decide
example : predecessor .x noX = none := by decide
example : predecessor .y ordinaryX = some ⟨2, 0, 1, by decide⟩ := by decide
example : predecessor .z ordinaryX = some ⟨2, 1, 0, by decide⟩ := by decide

abbrev PureN := Normal 3 2 0
def pureWrapped : PureN := ⟨0, 2, 0, by decide⟩
example : predecessor .x pureWrapped = some ⟨2, 0, 0, by decide⟩ := by decide

def socleOne : N := ⟨1, 1, 1, by decide⟩
def socleTwo : N := ⟨0, 2, 0, by decide⟩
def socles : Finset N := {socleOne, socleTwo}

example : (⟨1, 0, 0, by decide⟩ : N) ∈ standardFinset socles := by decide
example : (⟨0, 2, 0, by decide⟩ : N) ∈ standardFinset socles := by decide

def unitSocle : N := ⟨0, 0, 0, by decide⟩
def unitSocles : Finset N := {unitSocle}
def borderPoint : N := ⟨1, 0, 0, by decide⟩
def nonBorderKilled : N := ⟨2, 0, 0, by decide⟩

example : IsMinimalBorder (standardSet unitSocles) borderPoint := by
  simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet, unitSocles,
    unitSocle, borderPoint, Normal.predecessor, Normal.exact_divides_iff,
    Normal.DividesCriterion, Normal.xPredecessor]
example : ¬IsMinimalBorder (standardSet unitSocles) nonBorderKilled := by
  simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet, unitSocles,
    unitSocle, nonBorderKilled, Normal.predecessor, Normal.exact_divides_iff,
    Normal.DividesCriterion, Normal.xPredecessor]

def centreSocle : N := ⟨0, 2, 2, by decide⟩
def centreSocles : Finset N := {centreSocle}

example : IsDirectionalCentre centreSocles .x centreSocle := by
  rw [isDirectionalCentre_x_iff]
  simp [centreSocles, centreSocle]
example : IsDirectionalCentre centreSocles .y centreSocle := by
  rw [isDirectionalCentre_y_iff]
  simp [centreSocles, centreSocle]
example : IsDirectionalCentre centreSocles .z centreSocle := by
  rw [isDirectionalCentre_z_iff]
  simp [centreSocles, centreSocle]

end P23.OneTie.Run02Regression
