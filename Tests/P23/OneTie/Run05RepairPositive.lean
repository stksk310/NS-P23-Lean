import P23.OneTie.CoverShapes

namespace P23.OneTie

variable {a b c r u v V : ℕ} [NeZero a]

example {S : Finset (Normal a b c)} (h : IsTopDeletion S) :
    BaseCoverShape S := BaseCoverShape.topDeletion h
example {S : Finset (Normal a b 0)} (h : IsPureFibreProduct S) :
    BaseCoverShape S := BaseCoverShape.pureFibreProduct h
example (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) (hr : r ≤ a - 2) :
    BaseCoverShape (m2Socles ha r u v hr) := BaseCoverShape.m2 ha hu hv hr
example (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) (hr : r ≤ a - 2) :
    BaseCoverShape (m2KSocles ha r u v hr) := BaseCoverShape.m2K ha hu hv hr
example (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) (hr : r ≤ a - 2) :
    BaseCoverShape (m2ZSocles ha r u v hr) := BaseCoverShape.m2Z ha hu hv hr
example (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : c ≤ v) :
    BaseCoverShape (m3Socles (a := a) (b := b) (c := c) v) :=
  BaseCoverShape.m3 ha hb hc hv
example (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : c ≤ v) :
    BaseCoverShape (m3KSocles (a := a) (b := b) (c := c) ha v) :=
  BaseCoverShape.m3K ha hb hc hv
example (ha : 2 ≤ a) (hu : 1 ≤ u) :
    BaseCoverShape (m4Socles ha u v) := BaseCoverShape.m4 ha hu
example (ha : 2 ≤ a) (hu : 1 ≤ u) :
    BaseCoverShape (m4YSocles ha u v) := BaseCoverShape.m4Y ha hu
example (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : 1 ≤ v) :
    BaseCoverShape (m5Socles (a := a) (b := b) (c := c) ha v) :=
  BaseCoverShape.m5 ha hb hc hv
example (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : 1 ≤ v) :
    BaseCoverShape (m5YSocles (a := a) (b := b) (c := c) ha v) :=
  BaseCoverShape.m5Y ha hb hc hv
example (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : 1 ≤ v) :
    BaseCoverShape (m5ZSocles (a := a) (b := b) (c := c) ha v) :=
  BaseCoverShape.m5Z ha hb hc hv
example (ha : 2 ≤ a) (hb : 2 ≤ b) :
    BaseCoverShape (p3Socles (a := a) (b := b) v) := BaseCoverShape.p3 ha hb
example (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    BaseCoverShape (p4Socles (a := a) (b := b) V) := BaseCoverShape.p4 ha hb hV
example (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    BaseCoverShape (p4ZSocles (a := a) (b := b) ha V) := BaseCoverShape.p4Z ha hb hV
example (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    BaseCoverShape (p5Socles (a := a) (b := b) ha v) := BaseCoverShape.p5 ha hb hv
example (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    BaseCoverShape (p5ZSocles (a := a) (b := b) ha v) := BaseCoverShape.p5Z ha hb hv
example (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    BaseCoverShape (p6Socles (a := a) (b := b) ha v) := BaseCoverShape.p6 ha hb hv

example {S : Finset (Normal a b c)} (h : TypeThreeBaseShape S) :
    TypeThreeCoverShape S := TypeThreeCoverShape.direct h
example {S : Finset (Normal a b c)} (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : TypeThreeBaseShape (swapYZFinset S)) : TypeThreeCoverShape S :=
  TypeThreeCoverShape.reflected hb hc h

example {S : Finset (Normal a b c)} (h : IsTopDeletion S) :
    TypeThreeBaseShape S := TypeThreeBaseShape.topDeletion h
example {S : Finset (Normal a b 0)} (h : IsPureFibreProduct S) :
    TypeThreeBaseShape S := TypeThreeBaseShape.pureFibreProduct h
example (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) (hr : r ≤ a - 2) :
    TypeThreeBaseShape (m2KSocles ha r u v hr) := TypeThreeBaseShape.m2K ha hu hv hr
example (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) (hr : r ≤ a - 2) :
    TypeThreeBaseShape (m2ZSocles ha r u v hr) := TypeThreeBaseShape.m2Z ha hu hv hr
example (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : c ≤ v) :
    TypeThreeBaseShape (m3KSocles (a := a) (b := b) (c := c) ha v) :=
  TypeThreeBaseShape.m3K ha hb hc hv
example (ha : 2 ≤ a) (hu : 1 ≤ u) :
    TypeThreeBaseShape (m4YSocles ha u v) := TypeThreeBaseShape.m4Y ha hu
example (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : 1 ≤ v) :
    TypeThreeBaseShape (m5YSocles (a := a) (b := b) (c := c) ha v) :=
  TypeThreeBaseShape.m5Y ha hb hc hv
example (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : 1 ≤ v) :
    TypeThreeBaseShape (m5ZSocles (a := a) (b := b) (c := c) ha v) :=
  TypeThreeBaseShape.m5Z ha hb hc hv
example (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    TypeThreeBaseShape (p4ZSocles (a := a) (b := b) ha V) :=
  TypeThreeBaseShape.p4Z ha hb hV
example (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    TypeThreeBaseShape (p5ZSocles (a := a) (b := b) ha v) :=
  TypeThreeBaseShape.p5Z ha hb hv

example {S : Finset (Normal a b c)} (h : BaseCoverShape S) : CoverShape S :=
  CoverShape.direct h
example {S : Finset (Normal a b c)} (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : BaseCoverShape (swapYZFinset S)) : CoverShape S :=
  CoverShape.reflected hb hc h

end P23.OneTie
