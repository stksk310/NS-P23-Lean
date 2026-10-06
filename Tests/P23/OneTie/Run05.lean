import P23.OneTie.CoverGeometry
import P23.OneTie.CoverShapes
import P23.OneTie.H5Cover

namespace P23.OneTie

/-! Run-05 root, dominance, and H4 API (RED before implementation). -/

#check IsRootAntichain
#check IsLiveTie
#check IsDominantRoot
#check CoverHypotheses
#check isDominantRoot_iff_all_directionalCentre

#check h4_y_edge_exact
#check h4_z_edge_exact
#check h4_x_edge_ordinary_exact
#check h4_x_edge_wrapped_exact

/-! Exact cover-shape API. -/

#check predecessorRootFinset
#check IsTopDeletion
#check IsPureFibreProduct
#check BaseCoverShape
#check CoverShape
#check TypeThreeBaseShape
#check TypeThreeCoverShape

/-! Full unbounded symbolic H5 cover API. -/

#check h5_cover_below_last
#check h5_cover_last_layer
#check h5_full_symbolic_cover
#check h5_typeThree_specialized_cover

/-! The four H4 results are exercised through their public theorem bodies. -/

example {a b c : ℕ} [NeZero a] {S : Finset (Normal a b c)} {C R : Normal a b c}
    (hanti : IsRootAntichain S) (hyC : IsDirectionalCentre S .y C)
    (hR : R ∈ S) (hne : R ≠ C) (hy : 0 < R.y) :=
  h4_y_edge_exact hanti hyC hR hne hy

example {a b c : ℕ} [NeZero a] {S : Finset (Normal a b c)} {C R : Normal a b c}
    (hanti : IsRootAntichain S) (hzC : IsDirectionalCentre S .z C)
    (hR : R ∈ S) (hne : R ≠ C) (hz : 0 < R.z) :=
  h4_z_edge_exact hanti hzC hR hne hz

example {a b c : ℕ} [NeZero a] {S : Finset (Normal a b c)} {C R : Normal a b c}
    (hanti : IsRootAntichain S) (hxC : IsDirectionalCentre S .x C)
    (hR : R ∈ S) (hne : R ≠ C) (hx : 0 < R.x) :=
  h4_x_edge_ordinary_exact hanti hxC hR hne hx

example {a b c : ℕ} [NeZero a] {S : Finset (Normal a b c)} {C R : Normal a b c}
    (hanti : IsRootAntichain S) (hxC : IsDirectionalCentre S .x C)
    (hR : R ∈ S) (hne : R ≠ C) (hx : R.x = 0) (hy : b ≤ R.y) (hz : c ≤ R.z) :=
  h4_x_edge_wrapped_exact hanti hxC hR hne hx hy hz

/-! Constructor-level symbolic smoke tests for every Run-04 extension row. -/

example {a r u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : r ≤ a - 2) : BaseCoverShape (m2KSocles ha r u v hr) :=
  BaseCoverShape.m2K ha hu hv hr

example {a r u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : r ≤ a - 2) : BaseCoverShape (m2ZSocles ha r u v hr) :=
  BaseCoverShape.m2Z ha hu hv hr

example {b c v : ℕ} [NeZero (2 : ℕ)] (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : c ≤ v) :
    BaseCoverShape (m3KSocles (a := 2) (b := b) (c := c) (by omega) v) :=
  BaseCoverShape.m3K (by omega) hb hc hv

example {a u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hu : 1 ≤ u) :
    BaseCoverShape (m4YSocles ha u v) := BaseCoverShape.m4Y ha hu

example {a b v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 1 ≤ b) (hv : 1 ≤ v) :
    BaseCoverShape (m5YSocles (b := b) (c := 1) ha v) :=
  BaseCoverShape.m5Y ha hb (by omega) hv

example {a b c v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : 1 ≤ v) : BaseCoverShape (m5ZSocles (b := b) (c := c) ha v) :=
  BaseCoverShape.m5Z ha hb hc hv

example {a b V : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    BaseCoverShape (p4ZSocles (b := b) ha V) := BaseCoverShape.p4Z ha hb hV

example {a b v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    BaseCoverShape (p5ZSocles (b := b) ha v) := BaseCoverShape.p5Z ha hb hv

/-! Every required named configuration also instantiates the full public H5
theorem.  `CoverHypotheses` is kept explicit so these tests remain symbolic
and unbounded; the constructor tests above identify the exact expected row. -/

example {a r u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hr : r ≤ a - 2)
    (h : CoverHypotheses (m2KSocles ha r u v hr)) : CoverShape (m2KSocles ha r u v hr) :=
  h5_full_symbolic_cover _ h

example {a r u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hr : r ≤ a - 2)
    (h : CoverHypotheses (m2ZSocles ha r u v hr)) : CoverShape (m2ZSocles ha r u v hr) :=
  h5_full_symbolic_cover _ h

example {b c v : ℕ} [NeZero (2 : ℕ)] (h : CoverHypotheses
    (m3KSocles (a := 2) (b := b) (c := c) (by omega) v)) :
    CoverShape (m3KSocles (a := 2) (b := b) (c := c) (by omega) v) :=
  h5_full_symbolic_cover _ h

example {a u v : ℕ} [NeZero a] (ha : 2 ≤ a)
    (h : CoverHypotheses (m4YSocles ha u v)) : CoverShape (m4YSocles ha u v) :=
  h5_full_symbolic_cover _ h

example {a b v : ℕ} [NeZero a] (ha : 2 ≤ a)
    (h : CoverHypotheses (m5YSocles (b := b) (c := 1) ha v)) :
    CoverShape (m5YSocles (b := b) (c := 1) ha v) := h5_full_symbolic_cover _ h

example {a b c v : ℕ} [NeZero a] (ha : 2 ≤ a)
    (h : CoverHypotheses (m5ZSocles (b := b) (c := c) ha v)) :
    CoverShape (m5ZSocles (b := b) (c := c) ha v) := h5_full_symbolic_cover _ h

example {a b V : ℕ} [NeZero a] (ha : 2 ≤ a)
    (h : CoverHypotheses (p4ZSocles (b := b) ha V)) : CoverShape (p4ZSocles (b := b) ha V) :=
  h5_full_symbolic_cover _ h

example {a b v : ℕ} [NeZero a] (ha : 2 ≤ a)
    (h : CoverHypotheses (p5ZSocles (b := b) ha v)) : CoverShape (p5ZSocles (b := b) ha v) :=
  h5_full_symbolic_cover _ h

/-! Explicit pure fibre-product and mixed y/z-reflection witnesses. -/

example : IsPureFibreProduct
    ({(⟨0, 0, 1, by omega⟩ : Normal 2 2 0)} : Finset (Normal 2 2 0)) := by
  refine ⟨rfl, 1, by omega, ?_, ?_⟩
  · simp
  · intro R hR hne
    simp at hR
    exact False.elim (hne hR)

example {a b : ℕ} [NeZero a] (S : Finset (Normal a b 0))
    (_hfibre : IsPureFibreProduct S) (h : CoverHypotheses S) : CoverShape S :=
  h5_full_symbolic_cover S h

example {a b c : ℕ} [NeZero a] (T : Normal a b c)
    (_htop : IsTopDeletion (predecessorRootFinset T))
    (h : CoverHypotheses (predecessorRootFinset T)) : CoverShape (predecessorRootFinset T) :=
  h5_full_symbolic_cover _ h

example {a r u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : r ≤ a - 2) :
    CoverShape (swapYZFinset (m2KSocles ha r u v hr)) := by
  apply CoverShape.reflected (by omega) (by omega)
  rw [swapYZFinset_swapYZFinset]
  exact BaseCoverShape.m2K ha hu hv hr

/-! Wrapped endpoint smoke check used by both last-layer pure and mixed paths. -/

example (T : Normal 2 1 1) (hTx : T.x = 0) (hTy : 1 ≤ T.y) (hTz : 1 ≤ T.z) :
    Normal.predecessor .x T = some (Normal.wrappedXPredecessor T hTx hTy hTz) := by
  exact Normal.predecessor_x_wrapped T hTx hTy hTz

example {a b c : ℕ} [NeZero a] (S : Finset (Normal a b c)) (h : CoverHypotheses S)
    (C : Normal a b c) (hxC : IsDirectionalCentre S .x C) (hbelow : C.x < a - 1) :
    CoverShape S := h5_cover_below_last S h C hxC hbelow

example {a b c : ℕ} [NeZero a] (S : Finset (Normal a b c)) (h : CoverHypotheses S)
    (C : Normal a b c) (hxC : IsDirectionalCentre S .x C) (hlast : C.x = a - 1) :
    CoverShape S := h5_cover_last_layer S h C hxC hlast

end P23.OneTie
