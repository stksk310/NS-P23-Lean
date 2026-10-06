import P23.OneTie.CoverShapes

/-!
RED regression for the Run-05 shape-index leak.  This declaration should not
be constructible: the displayed shape lives at the pure parameters `(b,c) =
(2,0)`, while the constructor's positivity witnesses are supplied at the
unrelated local parameters `(1,1)`.
-/

namespace P23.OneTie

example : TypeThreeBaseShape
    (m3KSocles (a := 2) (b := 2) (c := 0) (by omega) 1) :=
  @TypeThreeBaseShape.m3K 2 (by infer_instance) 1 1 1
    (by omega) (by omega) (by omega) (by omega)

end P23.OneTie
