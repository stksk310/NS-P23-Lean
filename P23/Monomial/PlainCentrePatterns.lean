import P23.Monomial.PlainPermutation
namespace P23.Monomial
noncomputable section

def plainPureAxis (p : PlainExp) : Prop :=
  (p 0>0 ∧ p 1=0 ∧ p 2=0) ∨ (p 0=0 ∧ p 1>0 ∧ p 2=0) ∨ (p 0=0 ∧ p 1=0 ∧ p 2>0)
def plainTrianglePattern (p q r : PlainExp) : Prop :=
  (p 0+1=q 0 ∧ q 0=r 0 ∧ q 1+1=p 1 ∧ p 1=r 1 ∧ r 2+1=p 2 ∧ p 2=q 2) ∨
  (p 0+1=r 0 ∧ r 0=q 0 ∧ r 1+1=p 1 ∧ p 1=q 1 ∧ q 2+1=p 2 ∧ p 2=r 2) ∨
  (q 0+1=p 0 ∧ p 0=r 0 ∧ p 1+1=q 1 ∧ q 1=r 1 ∧ r 2+1=q 2 ∧ q 2=p 2) ∨
  (q 0+1=r 0 ∧ r 0=p 0 ∧ r 1+1=q 1 ∧ q 1=p 1 ∧ p 2+1=q 2 ∧ q 2=r 2) ∨
  (r 0+1=p 0 ∧ p 0=q 0 ∧ p 1+1=r 1 ∧ r 1=q 1 ∧ q 2+1=r 2 ∧ r 2=p 2) ∨
  (r 0+1=q 0 ∧ q 0=p 0 ∧ q 1+1=r 1 ∧ r 1=p 1 ∧ p 2+1=r 2 ∧ r 2=q 2)
def plainPlaneSplitPattern (p q r : PlainExp) : Prop :=
  (p 0>0 ∧ p 1=0 ∧ p 2=0 ∧ q 0=0 ∧ r 0=0) ∨
  (q 0>0 ∧ q 1=0 ∧ q 2=0 ∧ p 0=0 ∧ r 0=0) ∨
  (r 0>0 ∧ r 1=0 ∧ r 2=0 ∧ p 0=0 ∧ q 0=0) ∨
  (p 1>0 ∧ p 0=0 ∧ p 2=0 ∧ q 1=0 ∧ r 1=0) ∨
  (q 1>0 ∧ q 0=0 ∧ q 2=0 ∧ p 1=0 ∧ r 1=0) ∨
  (r 1>0 ∧ r 0=0 ∧ r 2=0 ∧ p 1=0 ∧ q 1=0) ∨
  (p 2>0 ∧ p 0=0 ∧ p 1=0 ∧ q 2=0 ∧ r 2=0) ∨
  (q 2>0 ∧ q 0=0 ∧ q 1=0 ∧ p 2=0 ∧ r 2=0) ∨
  (r 2>0 ∧ r 0=0 ∧ r 1=0 ∧ p 2=0 ∧ q 2=0)
def plainDominantAxisPattern (p q r : PlainExp) : Prop :=
  (p 0>0 ∧ p 1>0 ∧ p 2>0 ∧ plainPureAxis q ∧ plainPureAxis r) ∨
  (q 0>0 ∧ q 1>0 ∧ q 2>0 ∧ plainPureAxis r ∧ plainPureAxis p) ∨
  (r 0>0 ∧ r 1>0 ∧ r 2>0 ∧ plainPureAxis p ∧ plainPureAxis q)

-- Symbolic support cases: every positive coordinate remains an arbitrary natural.
-- This branches only on zero/nonzero, never on an exponent bound.
local macro "plain_plane_zero_cases" p:ident q:ident r:ident : tactic =>
  `(tactic| (
    simp only [plainPlaneSplitPattern]
    generalize ($p) 0 = x0 at *
    generalize ($p) 1 = x1 at *
    generalize ($p) 2 = x2 at *
    generalize ($q) 0 = y0 at *
    generalize ($q) 1 = y1 at *
    generalize ($q) 2 = y2 at *
    generalize ($r) 0 = z0 at *
    generalize ($r) 1 = z1 at *
    generalize ($r) 2 = z2 at *
    have hx0 : x0=0 ∨ 1≤x0 := by omega
    have hx1 : x1=0 ∨ 1≤x1 := by omega
    have hx2 : x2=0 ∨ 1≤x2 := by omega
    have hy0 : y0=0 ∨ 1≤y0 := by omega
    have hy1 : y1=0 ∨ 1≤y1 := by omega
    have hy2 : y2=0 ∨ 1≤y2 := by omega
    have hz0 : z0=0 ∨ 1≤z0 := by omega
    have hz1 : z1=0 ∨ 1≤z1 := by omega
    have hz2 : z2=0 ∨ 1≤z2 := by omega
    by_cases hp0 : x0 = 0 <;> by_cases hp1 : x1 = 0 <;>
      by_cases hp2 : x2 = 0 <;> by_cases hq0 : y0 = 0 <;>
      by_cases hq1 : y1 = 0 <;> by_cases hq2 : y2 = 0 <;>
      by_cases hr0 : z0 = 0 <;> by_cases hr1 : z1 = 0 <;>
      by_cases hr2 : z2 = 0
    all_goals simp only [Nat.pos_iff_ne_zero,Nat.zero_le,
      and_true,true_and,and_false,false_and,or_true,true_or,or_false,false_or,
      not_true_eq_false,not_false_eq_true,true_implies,false_implies,implies_true,
      hp0,hp1,hp2,hq0,hq1,hq2,hr0,hr1,hr2] at *
    all_goals omega))

set_option maxHeartbeats 1600000 in
private theorem plain_two_same_centres_plane (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainPlaneSplitPattern p q r := by
  have hp : p∈({p,q,r} : Finset PlainExp) := by simp
  have hq : q∈({p,q,r} : Finset PlainExp) := by simp
  have hr : r∈({p,q,r} : Finset PlainExp) := by simp
  have hnpq : ¬(p 0 ≤ q 0 ∧ p 1 ≤ q 1 ∧ p 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha p hp q hq h)
  have hnpr : ¬(p 0 ≤ r 0 ∧ p 1 ≤ r 1 ∧ p 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha p hp r hr h)
  have hnqp : ¬(q 0 ≤ p 0 ∧ q 1 ≤ p 1 ∧ q 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha q hq p hp h).symm
  have hnqr : ¬(q 0 ≤ r 0 ∧ q 1 ≤ r 1 ∧ q 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha q hq r hr h)
  have hnrp : ¬(r 0 ≤ p 0 ∧ r 1 ≤ p 1 ∧ r 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha r hr p hp h).symm
  have hnrq : ¬(r 0 ≤ q 0 ∧ r 1 ≤ q 1 ∧ r 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha r hr q hq h).symm
  have active (j : Fin 3) : 0<p j ∨ 0<q j ∨ 0<r j := by
    obtain ⟨s,hs,hjs⟩ := plain_direction_active {p,q,r} hv j
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact Or.inl hjs
    · exact Or.inr (Or.inl hjs)
    · exact Or.inr (Or.inr hjs)
  have hact0 := active 0
  have hact1 := active 1
  have hact2 := active 2
  have h0p (h : 0<p 0) : p 0-1≤p 0 ∧ p 1≤p 1 ∧ p 2≤p 2 := by
    have hb := hc0.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0q (h : 0<q 0) : q 0-1≤p 0 ∧ q 1≤p 1 ∧ q 2≤p 2 := by
    have hb := hc0.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0r (h : 0<r 0) : r 0-1≤p 0 ∧ r 1≤p 1 ∧ r 2≤p 2 := by
    have hb := hc0.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1p (h : 0<p 1) : p 1-1≤p 1 ∧ p 0≤p 0 ∧ p 2≤p 2 := by
    have hb := hc1.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1q (h : 0<q 1) : q 1-1≤p 1 ∧ q 0≤p 0 ∧ q 2≤p 2 := by
    have hb := hc1.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1r (h : 0<r 1) : r 1-1≤p 1 ∧ r 0≤p 0 ∧ r 2≤p 2 := by
    have hb := hc1.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2p (h : 0<p 2) : p 2-1≤q 2 ∧ p 0≤q 0 ∧ p 1≤q 1 := by
    have hb := hc2.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2q (h : 0<q 2) : q 2-1≤q 2 ∧ q 0≤q 0 ∧ q 1≤q 1 := by
    have hb := hc2.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2r (h : 0<r 2) : r 2-1≤q 2 ∧ r 0≤q 0 ∧ r 1≤q 1 := by
    have hb := hc2.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have he0p (h : 0 < p 0) : p = p ∨ p 0 = p 0 + 1 := by
    by_cases he : p = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hp he h).1
  have he0q (h : 0 < q 0) : q = p ∨ q 0 = p 0 + 1 := by
    by_cases he : q = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hq he h).1
  have he0r (h : 0 < r 0) : r = p ∨ r 0 = p 0 + 1 := by
    by_cases he : r = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hr he h).1
  have he1p (h : 0 < p 1) : p = p ∨ p 1 = p 1 + 1 := by
    by_cases he : p = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hp he h).1
  have he1q (h : 0 < q 1) : q = p ∨ q 1 = p 1 + 1 := by
    by_cases he : q = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hq he h).1
  have he1r (h : 0 < r 1) : r = p ∨ r 1 = p 1 + 1 := by
    by_cases he : r = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hr he h).1
  have he2p (h : 0 < p 2) : p = q ∨ p 2 = q 2 + 1 := by
    by_cases he : p = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hp he h).1
  have he2q (h : 0 < q 2) : q = q ∨ q 2 = q 2 + 1 := by
    by_cases he : q = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hq he h).1
  have he2r (h : 0 < r 2) : r = q ∨ r 2 = q 2 + 1 := by
    by_cases he : r = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hr he h).1
  simp only [hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr,
    false_or,true_or,or_false,or_true,implies_true] at he0p he0q he0r he1p he1q he1r he2p he2q he2r
  clear hc0 hc1 hc2 ha hv active hp hq hr hpq hpr hqr
  plain_plane_zero_cases p q r

set_option maxHeartbeats 1600000 in
private theorem plain_distinct_centres_pattern (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    (p 0+1=q 0 ∧ q 0=r 0 ∧ q 1+1=p 1 ∧ p 1=r 1 ∧ r 2+1=p 2 ∧ p 2=q 2) ∨ plainPlaneSplitPattern p q r := by
  have hp : p∈({p,q,r} : Finset PlainExp) := by simp
  have hq : q∈({p,q,r} : Finset PlainExp) := by simp
  have hr : r∈({p,q,r} : Finset PlainExp) := by simp
  have hnpq : ¬(p 0 ≤ q 0 ∧ p 1 ≤ q 1 ∧ p 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha p hp q hq h)
  have hnpr : ¬(p 0 ≤ r 0 ∧ p 1 ≤ r 1 ∧ p 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha p hp r hr h)
  have hnqp : ¬(q 0 ≤ p 0 ∧ q 1 ≤ p 1 ∧ q 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha q hq p hp h).symm
  have hnqr : ¬(q 0 ≤ r 0 ∧ q 1 ≤ r 1 ∧ q 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha q hq r hr h)
  have hnrp : ¬(r 0 ≤ p 0 ∧ r 1 ≤ p 1 ∧ r 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha r hr p hp h).symm
  have hnrq : ¬(r 0 ≤ q 0 ∧ r 1 ≤ q 1 ∧ r 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha r hr q hq h).symm
  have active (j : Fin 3) : 0<p j ∨ 0<q j ∨ 0<r j := by
    obtain ⟨s,hs,hjs⟩ := plain_direction_active {p,q,r} hv j
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact Or.inl hjs
    · exact Or.inr (Or.inl hjs)
    · exact Or.inr (Or.inr hjs)
  have hact0 := active 0
  have hact1 := active 1
  have hact2 := active 2
  have h0p (h : 0<p 0) : p 0-1≤p 0 ∧ p 1≤p 1 ∧ p 2≤p 2 := by
    have hb := hc0.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0q (h : 0<q 0) : q 0-1≤p 0 ∧ q 1≤p 1 ∧ q 2≤p 2 := by
    have hb := hc0.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0r (h : 0<r 0) : r 0-1≤p 0 ∧ r 1≤p 1 ∧ r 2≤p 2 := by
    have hb := hc0.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1p (h : 0<p 1) : p 1-1≤q 1 ∧ p 0≤q 0 ∧ p 2≤q 2 := by
    have hb := hc1.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1q (h : 0<q 1) : q 1-1≤q 1 ∧ q 0≤q 0 ∧ q 2≤q 2 := by
    have hb := hc1.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1r (h : 0<r 1) : r 1-1≤q 1 ∧ r 0≤q 0 ∧ r 2≤q 2 := by
    have hb := hc1.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2p (h : 0<p 2) : p 2-1≤r 2 ∧ p 0≤r 0 ∧ p 1≤r 1 := by
    have hb := hc2.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2q (h : 0<q 2) : q 2-1≤r 2 ∧ q 0≤r 0 ∧ q 1≤r 1 := by
    have hb := hc2.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2r (h : 0<r 2) : r 2-1≤r 2 ∧ r 0≤r 0 ∧ r 1≤r 1 := by
    have hb := hc2.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have he0p (h : 0 < p 0) : p = p ∨ p 0 = p 0 + 1 := by
    by_cases he : p = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hp he h).1
  have he0q (h : 0 < q 0) : q = p ∨ q 0 = p 0 + 1 := by
    by_cases he : q = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hq he h).1
  have he0r (h : 0 < r 0) : r = p ∨ r 0 = p 0 + 1 := by
    by_cases he : r = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hr he h).1
  have he1p (h : 0 < p 1) : p = q ∨ p 1 = q 1 + 1 := by
    by_cases he : p = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hp he h).1
  have he1q (h : 0 < q 1) : q = q ∨ q 1 = q 1 + 1 := by
    by_cases he : q = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hq he h).1
  have he1r (h : 0 < r 1) : r = q ∨ r 1 = q 1 + 1 := by
    by_cases he : r = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hr he h).1
  have he2p (h : 0 < p 2) : p = r ∨ p 2 = r 2 + 1 := by
    by_cases he : p = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hp he h).1
  have he2q (h : 0 < q 2) : q = r ∨ q 2 = r 2 + 1 := by
    by_cases he : q = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hq he h).1
  have he2r (h : 0 < r 2) : r = r ∨ r 2 = r 2 + 1 := by
    by_cases he : r = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hr he h).1
  simp only [hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr,
    false_or,true_or,or_false,or_true,implies_true] at he0p he0q he0r he1p he1q he1r he2p he2q he2r
  clear hc0 hc1 hc2 ha hv active hp hq hr hpq hpr hqr
  plain_plane_zero_cases p q r

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_0 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 p) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
  have hp : p∈({p,q,r} : Finset PlainExp) := by simp
  have hq : q∈({p,q,r} : Finset PlainExp) := by simp
  have hr : r∈({p,q,r} : Finset PlainExp) := by simp
  have hnpq : ¬(p 0 ≤ q 0 ∧ p 1 ≤ q 1 ∧ p 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha p hp q hq h)
  have hnpr : ¬(p 0 ≤ r 0 ∧ p 1 ≤ r 1 ∧ p 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha p hp r hr h)
  have hnqp : ¬(q 0 ≤ p 0 ∧ q 1 ≤ p 1 ∧ q 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha q hq p hp h).symm
  have hnqr : ¬(q 0 ≤ r 0 ∧ q 1 ≤ r 1 ∧ q 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha q hq r hr h)
  have hnrp : ¬(r 0 ≤ p 0 ∧ r 1 ≤ p 1 ∧ r 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha r hr p hp h).symm
  have hnrq : ¬(r 0 ≤ q 0 ∧ r 1 ≤ q 1 ∧ r 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha r hr q hq h).symm
  have active (j : Fin 3) : 0<p j ∨ 0<q j ∨ 0<r j := by
    obtain ⟨s,hs,hjs⟩ := plain_direction_active {p,q,r} hv j
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact Or.inl hjs
    · exact Or.inr (Or.inl hjs)
    · exact Or.inr (Or.inr hjs)
  have hact0 := active 0
  have hact1 := active 1
  have hact2 := active 2
  have h0p (h : 0<p 0) : p 0-1≤p 0 ∧ p 1≤p 1 ∧ p 2≤p 2 := by
    have hb := hc0.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0q (h : 0<q 0) : q 0-1≤p 0 ∧ q 1≤p 1 ∧ q 2≤p 2 := by
    have hb := hc0.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0r (h : 0<r 0) : r 0-1≤p 0 ∧ r 1≤p 1 ∧ r 2≤p 2 := by
    have hb := hc0.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1p (h : 0<p 1) : p 1-1≤p 1 ∧ p 0≤p 0 ∧ p 2≤p 2 := by
    have hb := hc1.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1q (h : 0<q 1) : q 1-1≤p 1 ∧ q 0≤p 0 ∧ q 2≤p 2 := by
    have hb := hc1.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1r (h : 0<r 1) : r 1-1≤p 1 ∧ r 0≤p 0 ∧ r 2≤p 2 := by
    have hb := hc1.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2p (h : 0<p 2) : p 2-1≤p 2 ∧ p 0≤p 0 ∧ p 1≤p 1 := by
    have hb := hc2.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2q (h : 0<q 2) : q 2-1≤p 2 ∧ q 0≤p 0 ∧ q 1≤p 1 := by
    have hb := hc2.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2r (h : 0<r 2) : r 2-1≤p 2 ∧ r 0≤p 0 ∧ r 1≤p 1 := by
    have hb := hc2.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have he0p (h : 0 < p 0) : p = p ∨ p 0 = p 0 + 1 := by
    by_cases he : p = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hp he h).1
  have he0q (h : 0 < q 0) : q = p ∨ q 0 = p 0 + 1 := by
    by_cases he : q = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hq he h).1
  have he0r (h : 0 < r 0) : r = p ∨ r 0 = p 0 + 1 := by
    by_cases he : r = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hr he h).1
  have he1p (h : 0 < p 1) : p = p ∨ p 1 = p 1 + 1 := by
    by_cases he : p = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hp he h).1
  have he1q (h : 0 < q 1) : q = p ∨ q 1 = p 1 + 1 := by
    by_cases he : q = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hq he h).1
  have he1r (h : 0 < r 1) : r = p ∨ r 1 = p 1 + 1 := by
    by_cases he : r = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hr he h).1
  have he2p (h : 0 < p 2) : p = p ∨ p 2 = p 2 + 1 := by
    by_cases he : p = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hp he h).1
  have he2q (h : 0 < q 2) : q = p ∨ q 2 = p 2 + 1 := by
    by_cases he : q = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hq he h).1
  have he2r (h : 0 < r 2) : r = p ∨ r 2 = p 2 + 1 := by
    by_cases he : r = p
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hr he h).1
  simp only [hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr,
    false_or,true_or,implies_true] at he0p he0q he0r he1p he1q he1r he2p he2q he2r
  clear active hp hq hr
  clear hc0 hc1 hc2 ha hv hpq hpr hqr
  by_cases hz0 : p 0 = 0
  ·
    have h : (q 0>0 ∧ q 1=0 ∧ q 2=0 ∧ p 0=0 ∧ r 0=0) ∨ (r 0>0 ∧ r 1=0 ∧ r 2=0 ∧ p 0=0 ∧ q 0=0) := by omega
    right; left
    rcases h with h | h
    · exact Or.inr (Or.inl (h))
    · exact Or.inr (Or.inr (Or.inl (h)))
  ·
    by_cases hz1 : p 1 = 0
    ·
      have h : (q 1>0 ∧ q 0=0 ∧ q 2=0 ∧ p 1=0 ∧ r 1=0) ∨ (r 1>0 ∧ r 0=0 ∧ r 2=0 ∧ p 1=0 ∧ q 1=0) := by omega
      right; left
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
    ·
      by_cases hz2 : p 2 = 0
      ·
        have h : (q 2>0 ∧ q 0=0 ∧ q 1=0 ∧ p 2=0 ∧ r 2=0) ∨ (r 2>0 ∧ r 0=0 ∧ r 1=0 ∧ p 2=0 ∧ q 2=0) := by omega
        right; left
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))))
      ·
        have hpos : 0<p 0 ∧ 0<p 1 ∧ 0<p 2 := by omega
        have haxis1 : plainPureAxis q := by
          simp only [plainPureAxis]
          omega
        have haxis2 : plainPureAxis r := by
          simp only [plainPureAxis]
          omega
        right; right
        exact Or.inl (⟨hpos.1,hpos.2.1,hpos.2.2,haxis1,haxis2⟩)

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_1 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (2 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e p,plainCoordinatePerm e q,plainCoordinatePerm e r} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e p)
      (plainCoordinatePerm e q) (plainCoordinatePerm e r)
      (fun h => hpq ((plainCoordinatePerm e).injective h))
      (fun h => hpr ((plainCoordinatePerm e).injective h))
      (fun h => hqr ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 p
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 p
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 q
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_2 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (2 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e p,plainCoordinatePerm e r,plainCoordinatePerm e q} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e p)
      (plainCoordinatePerm e r) (plainCoordinatePerm e q)
      (fun h => hpr ((plainCoordinatePerm e).injective h))
      (fun h => hpq ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hqr) ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 p
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 p
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 r
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
    · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_3 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 p) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (1 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e p,plainCoordinatePerm e q,plainCoordinatePerm e r} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e p)
      (plainCoordinatePerm e q) (plainCoordinatePerm e r)
      (fun h => hpq ((plainCoordinatePerm e).injective h))
      (fun h => hpr ((plainCoordinatePerm e).injective h))
      (fun h => hqr ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 p
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 p
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 q
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_4 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (0 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e q,plainCoordinatePerm e p,plainCoordinatePerm e r} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e q)
      (plainCoordinatePerm e p) (plainCoordinatePerm e r)
      (fun h => (Ne.symm hpq) ((plainCoordinatePerm e).injective h))
      (fun h => hqr ((plainCoordinatePerm e).injective h))
      (fun h => hpr ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 q
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 q
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 p
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_5 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    have he : ({p,q,r} : Finset PlainExp) = {p,q,r} := by
      ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    have h := plain_distinct_centres_pattern p q r
      hpq hpr hqr
      (by simpa only [← he] using ha) (by simpa only [← he] using hv)
      (by simpa only [← he] using hc0) (by simpa only [← he] using hc1)
      (by simpa only [← he] using hc2)
    rcases h with h | h
    · left
      exact Or.inl (h)
    · right; left
      rcases h with h | h | h | h | h | h | h | h | h
      · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)
      · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))
      · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_6 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 r)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 p) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (1 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e p,plainCoordinatePerm e r,plainCoordinatePerm e q} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e p)
      (plainCoordinatePerm e r) (plainCoordinatePerm e q)
      (fun h => hpr ((plainCoordinatePerm e).injective h))
      (fun h => hpq ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hqr) ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 p
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 p
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 r
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_7 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 r)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    have he : ({p,q,r} : Finset PlainExp) = {p,r,q} := by
      ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    have h := plain_distinct_centres_pattern p r q
      hpr hpq (Ne.symm hqr)
      (by simpa only [← he] using ha) (by simpa only [← he] using hv)
      (by simpa only [← he] using hc0) (by simpa only [← he] using hc1)
      (by simpa only [← he] using hc2)
    rcases h with h | h
    · left
      exact Or.inr (Or.inl (h))
    · right; left
      rcases h with h | h | h | h | h | h | h | h | h
      · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)
      · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
      · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_8 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 p)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 r)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (0 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e r,plainCoordinatePerm e p,plainCoordinatePerm e q} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e r)
      (plainCoordinatePerm e p) (plainCoordinatePerm e q)
      (fun h => (Ne.symm hpr) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hqr) ((plainCoordinatePerm e).injective h))
      (fun h => hpq ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 r
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 r
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 p
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_9 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 q)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 p) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (0 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e p,plainCoordinatePerm e q,plainCoordinatePerm e r} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e p)
      (plainCoordinatePerm e q) (plainCoordinatePerm e r)
      (fun h => hpq ((plainCoordinatePerm e).injective h))
      (fun h => hpr ((plainCoordinatePerm e).injective h))
      (fun h => hqr ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 p
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 p
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 q
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_10 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 q)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (1 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e q,plainCoordinatePerm e p,plainCoordinatePerm e r} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e q)
      (plainCoordinatePerm e p) (plainCoordinatePerm e r)
      (fun h => (Ne.symm hpq) ((plainCoordinatePerm e).injective h))
      (fun h => hqr ((plainCoordinatePerm e).injective h))
      (fun h => hpr ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 q
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 q
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 p
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_11 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 q)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    have he : ({p,q,r} : Finset PlainExp) = {q,p,r} := by
      ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    have h := plain_distinct_centres_pattern q p r
      (Ne.symm hpq) hqr hpr
      (by simpa only [← he] using ha) (by simpa only [← he] using hv)
      (by simpa only [← he] using hc0) (by simpa only [← he] using hc1)
      (by simpa only [← he] using hc2)
    rcases h with h | h
    · left
      exact Or.inr (Or.inr (Or.inl (h)))
    · right; left
      rcases h with h | h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))
      · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)
      · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_12 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 q)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 p) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (2 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e q,plainCoordinatePerm e p,plainCoordinatePerm e r} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e q)
      (plainCoordinatePerm e p) (plainCoordinatePerm e r)
      (fun h => (Ne.symm hpq) ((plainCoordinatePerm e).injective h))
      (fun h => hqr ((plainCoordinatePerm e).injective h))
      (fun h => hpr ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 q
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 q
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 p
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))
    · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_13 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 q)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
  have hp : p∈({p,q,r} : Finset PlainExp) := by simp
  have hq : q∈({p,q,r} : Finset PlainExp) := by simp
  have hr : r∈({p,q,r} : Finset PlainExp) := by simp
  have hnpq : ¬(p 0 ≤ q 0 ∧ p 1 ≤ q 1 ∧ p 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha p hp q hq h)
  have hnpr : ¬(p 0 ≤ r 0 ∧ p 1 ≤ r 1 ∧ p 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha p hp r hr h)
  have hnqp : ¬(q 0 ≤ p 0 ∧ q 1 ≤ p 1 ∧ q 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha q hq p hp h).symm
  have hnqr : ¬(q 0 ≤ r 0 ∧ q 1 ≤ r 1 ∧ q 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha q hq r hr h)
  have hnrp : ¬(r 0 ≤ p 0 ∧ r 1 ≤ p 1 ∧ r 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha r hr p hp h).symm
  have hnrq : ¬(r 0 ≤ q 0 ∧ r 1 ≤ q 1 ∧ r 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha r hr q hq h).symm
  have active (j : Fin 3) : 0<p j ∨ 0<q j ∨ 0<r j := by
    obtain ⟨s,hs,hjs⟩ := plain_direction_active {p,q,r} hv j
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact Or.inl hjs
    · exact Or.inr (Or.inl hjs)
    · exact Or.inr (Or.inr hjs)
  have hact0 := active 0
  have hact1 := active 1
  have hact2 := active 2
  have h0p (h : 0<p 0) : p 0-1≤q 0 ∧ p 1≤q 1 ∧ p 2≤q 2 := by
    have hb := hc0.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0q (h : 0<q 0) : q 0-1≤q 0 ∧ q 1≤q 1 ∧ q 2≤q 2 := by
    have hb := hc0.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0r (h : 0<r 0) : r 0-1≤q 0 ∧ r 1≤q 1 ∧ r 2≤q 2 := by
    have hb := hc0.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1p (h : 0<p 1) : p 1-1≤q 1 ∧ p 0≤q 0 ∧ p 2≤q 2 := by
    have hb := hc1.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1q (h : 0<q 1) : q 1-1≤q 1 ∧ q 0≤q 0 ∧ q 2≤q 2 := by
    have hb := hc1.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1r (h : 0<r 1) : r 1-1≤q 1 ∧ r 0≤q 0 ∧ r 2≤q 2 := by
    have hb := hc1.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2p (h : 0<p 2) : p 2-1≤q 2 ∧ p 0≤q 0 ∧ p 1≤q 1 := by
    have hb := hc2.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2q (h : 0<q 2) : q 2-1≤q 2 ∧ q 0≤q 0 ∧ q 1≤q 1 := by
    have hb := hc2.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2r (h : 0<r 2) : r 2-1≤q 2 ∧ r 0≤q 0 ∧ r 1≤q 1 := by
    have hb := hc2.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have he0p (h : 0 < p 0) : p = q ∨ p 0 = q 0 + 1 := by
    by_cases he : p = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hp he h).1
  have he0q (h : 0 < q 0) : q = q ∨ q 0 = q 0 + 1 := by
    by_cases he : q = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hq he h).1
  have he0r (h : 0 < r 0) : r = q ∨ r 0 = q 0 + 1 := by
    by_cases he : r = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hr he h).1
  have he1p (h : 0 < p 1) : p = q ∨ p 1 = q 1 + 1 := by
    by_cases he : p = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hp he h).1
  have he1q (h : 0 < q 1) : q = q ∨ q 1 = q 1 + 1 := by
    by_cases he : q = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hq he h).1
  have he1r (h : 0 < r 1) : r = q ∨ r 1 = q 1 + 1 := by
    by_cases he : r = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hr he h).1
  have he2p (h : 0 < p 2) : p = q ∨ p 2 = q 2 + 1 := by
    by_cases he : p = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hp he h).1
  have he2q (h : 0 < q 2) : q = q ∨ q 2 = q 2 + 1 := by
    by_cases he : q = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hq he h).1
  have he2r (h : 0 < r 2) : r = q ∨ r 2 = q 2 + 1 := by
    by_cases he : r = q
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hr he h).1
  simp only [hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr,
    false_or,true_or,implies_true] at he0p he0q he0r he1p he1q he1r he2p he2q he2r
  clear active hp hq hr
  clear hc0 hc1 hc2 ha hv hpq hpr hqr
  by_cases hz0 : q 0 = 0
  ·
    have h : (p 0>0 ∧ p 1=0 ∧ p 2=0 ∧ q 0=0 ∧ r 0=0) ∨ (r 0>0 ∧ r 1=0 ∧ r 2=0 ∧ p 0=0 ∧ q 0=0) := by omega
    right; left
    rcases h with h | h
    · exact Or.inl (h)
    · exact Or.inr (Or.inr (Or.inl (h)))
  ·
    by_cases hz1 : q 1 = 0
    ·
      have h : (p 1>0 ∧ p 0=0 ∧ p 2=0 ∧ q 1=0 ∧ r 1=0) ∨ (r 1>0 ∧ r 0=0 ∧ r 2=0 ∧ p 1=0 ∧ q 1=0) := by omega
      right; left
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
    ·
      by_cases hz2 : q 2 = 0
      ·
        have h : (p 2>0 ∧ p 0=0 ∧ p 1=0 ∧ q 2=0 ∧ r 2=0) ∨ (r 2>0 ∧ r 0=0 ∧ r 1=0 ∧ p 2=0 ∧ q 2=0) := by omega
        right; left
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))))
      ·
        have hpos : 0<q 0 ∧ 0<q 1 ∧ 0<q 2 := by omega
        have haxis1 : plainPureAxis p := by
          simp only [plainPureAxis]
          omega
        have haxis2 : plainPureAxis r := by
          simp only [plainPureAxis]
          omega
        right; right
        exact Or.inr (Or.inl (⟨hpos.1,hpos.2.1,hpos.2.2,haxis2,haxis1⟩))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_14 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 q)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (2 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e q,plainCoordinatePerm e r,plainCoordinatePerm e p} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e q)
      (plainCoordinatePerm e r) (plainCoordinatePerm e p)
      (fun h => hqr ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpq) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpr) ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 q
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 q
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 r
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
    · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_15 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 q)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 r)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 p) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    have he : ({p,q,r} : Finset PlainExp) = {q,r,p} := by
      ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    have h := plain_distinct_centres_pattern q r p
      hqr (Ne.symm hpq) (Ne.symm hpr)
      (by simpa only [← he] using ha) (by simpa only [← he] using hv)
      (by simpa only [← he] using hc0) (by simpa only [← he] using hc1)
      (by simpa only [← he] using hc2)
    rcases h with h | h
    · left
      exact Or.inr (Or.inr (Or.inr (Or.inl (h))))
    · right; left
      rcases h with h | h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))
      · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
      · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_16 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 q)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 r)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (1 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e q,plainCoordinatePerm e r,plainCoordinatePerm e p} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e q)
      (plainCoordinatePerm e r) (plainCoordinatePerm e p)
      (fun h => hqr ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpq) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpr) ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 q
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 q
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 r
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_17 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 q)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 r)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (0 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e r,plainCoordinatePerm e q,plainCoordinatePerm e p} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e r)
      (plainCoordinatePerm e q) (plainCoordinatePerm e p)
      (fun h => (Ne.symm hqr) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpr) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpq) ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 r
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 r
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 q
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_18 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 r)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 p) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (0 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e p,plainCoordinatePerm e r,plainCoordinatePerm e q} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e p)
      (plainCoordinatePerm e r) (plainCoordinatePerm e q)
      (fun h => hpr ((plainCoordinatePerm e).injective h))
      (fun h => hpq ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hqr) ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 p
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 p
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 r
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_19 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 r)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    have he : ({p,q,r} : Finset PlainExp) = {r,p,q} := by
      ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    have h := plain_distinct_centres_pattern r p q
      (Ne.symm hpr) (Ne.symm hqr) hpq
      (by simpa only [← he] using ha) (by simpa only [← he] using hv)
      (by simpa only [← he] using hc0) (by simpa only [← he] using hc1)
      (by simpa only [← he] using hc2)
    rcases h with h | h
    · left
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h)))))
    · right; left
      rcases h with h | h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
      · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)
      · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_20 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 r)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 p)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (1 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e r,plainCoordinatePerm e p,plainCoordinatePerm e q} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e r)
      (plainCoordinatePerm e p) (plainCoordinatePerm e q)
      (fun h => (Ne.symm hpr) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hqr) ((plainCoordinatePerm e).injective h))
      (fun h => hpq ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 r
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 r
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 p
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_21 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 r)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 p) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    have he : ({p,q,r} : Finset PlainExp) = {r,q,p} := by
      ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    have h := plain_distinct_centres_pattern r q p
      (Ne.symm hqr) (Ne.symm hpr) (Ne.symm hpq)
      (by simpa only [← he] using ha) (by simpa only [← he] using hv)
      (by simpa only [← he] using hc0) (by simpa only [← he] using hc1)
      (by simpa only [← he] using hc2)
    rcases h with h | h
    · left
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))
    · right; left
      rcases h with h | h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
      · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))
      · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_22 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 r)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (0 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e q,plainCoordinatePerm e r,plainCoordinatePerm e p} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e q)
      (plainCoordinatePerm e r) (plainCoordinatePerm e p)
      (fun h => hqr ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpq) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpr) ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 q
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 q
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 r
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩))))
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩)

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_23 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 r)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 q)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (1 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e r,plainCoordinatePerm e q,plainCoordinatePerm e p} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e r)
      (plainCoordinatePerm e q) (plainCoordinatePerm e p)
      (fun h => (Ne.symm hqr) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpr) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpq) ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 r
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 r
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 q
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
    · exact Or.inr (Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩))
    · exact Or.inl (⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2,h.2.2.2.1⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_24 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 r)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 r)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 p) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (2 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e r,plainCoordinatePerm e p,plainCoordinatePerm e q} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e r)
      (plainCoordinatePerm e p) (plainCoordinatePerm e q)
      (fun h => (Ne.symm hpr) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hqr) ((plainCoordinatePerm e).injective h))
      (fun h => hpq ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 r
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 r
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 p
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)))
    · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)
    · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_25 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 r)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 r)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 q) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
    let e := Equiv.swap (2 : Fin 3) 2
    have hi : ({p,q,r} : Finset PlainExp).image (plainCoordinatePerm e) =
        {plainCoordinatePerm e r,plainCoordinatePerm e q,plainCoordinatePerm e p} := by
      simp only [Finset.image_insert,Finset.image_singleton] <;>
        (ext s; simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto)
    have h := plain_two_same_centres_plane (plainCoordinatePerm e r)
      (plainCoordinatePerm e q) (plainCoordinatePerm e p)
      (fun h => (Ne.symm hqr) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpr) ((plainCoordinatePerm e).injective h))
      (fun h => (Ne.symm hpq) ((plainCoordinatePerm e).injective h))
      (by simpa only [hi] using plainAntichain_coordinatePerm e {p,q,r} ha)
      (by simpa only [hi] using plainVariables_coordinatePerm e {p,q,r} hv)
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 0 r
        (by simpa [e,Equiv.swap_apply_def] using hc0)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 1 r
        (by simpa [e,Equiv.swap_apply_def] using hc1)))
      (by simpa only [hi] using (plainCentre_coordinatePerm e {p,q,r} 2 q
        (by simpa [e,Equiv.swap_apply_def] using hc2)))
    right; left
    simp only [plainPlaneSplitPattern,plainCoordinatePerm_apply] at h
    norm_num [e,Equiv.swap_apply_def] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))
    · exact Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))
    · exact Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩)))))))

set_option maxHeartbeats 1600000 in
private theorem plain_centre_assignment_26 (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc0 : PlainDirectionalCentre {p,q,r} 0 r)
    (hc1 : PlainDirectionalCentre {p,q,r} 1 r)
    (hc2 : PlainDirectionalCentre {p,q,r} 2 r) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
  have hp : p∈({p,q,r} : Finset PlainExp) := by simp
  have hq : q∈({p,q,r} : Finset PlainExp) := by simp
  have hr : r∈({p,q,r} : Finset PlainExp) := by simp
  have hnpq : ¬(p 0 ≤ q 0 ∧ p 1 ≤ q 1 ∧ p 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha p hp q hq h)
  have hnpr : ¬(p 0 ≤ r 0 ∧ p 1 ≤ r 1 ∧ p 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides p r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha p hp r hr h)
  have hnqp : ¬(q 0 ≤ p 0 ∧ q 1 ≤ p 1 ∧ q 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpq (ha q hq p hp h).symm
  have hnqr : ¬(q 0 ≤ r 0 ∧ q 1 ≤ r 1 ∧ q 2 ≤ r 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides q r := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha q hq r hr h)
  have hnrp : ¬(r 0 ≤ p 0 ∧ r 1 ≤ p 1 ∧ r 2 ≤ p 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r p := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hpr (ha r hr p hp h).symm
  have hnrq : ¬(r 0 ≤ q 0 ∧ r 1 ≤ q 1 ∧ r 2 ≤ q 2) := by
    rintro ⟨h0,h1,h2⟩
    have h : plainDivides r q := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    exact hqr (ha r hr q hq h).symm
  have active (j : Fin 3) : 0<p j ∨ 0<q j ∨ 0<r j := by
    obtain ⟨s,hs,hjs⟩ := plain_direction_active {p,q,r} hv j
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact Or.inl hjs
    · exact Or.inr (Or.inl hjs)
    · exact Or.inr (Or.inr hjs)
  have hact0 := active 0
  have hact1 := active 1
  have hact2 := active 2
  have h0p (h : 0<p 0) : p 0-1≤r 0 ∧ p 1≤r 1 ∧ p 2≤r 2 := by
    have hb := hc0.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0q (h : 0<q 0) : q 0-1≤r 0 ∧ q 1≤r 1 ∧ q 2≤r 2 := by
    have hb := hc0.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h0r (h : 0<r 0) : r 0-1≤r 0 ∧ r 1≤r 1 ∧ r 2≤r 2 := by
    have hb := hc0.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1p (h : 0<p 1) : p 1-1≤r 1 ∧ p 0≤r 0 ∧ p 2≤r 2 := by
    have hb := hc1.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1q (h : 0<q 1) : q 1-1≤r 1 ∧ q 0≤r 0 ∧ q 2≤r 2 := by
    have hb := hc1.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h1r (h : 0<r 1) : r 1-1≤r 1 ∧ r 0≤r 0 ∧ r 2≤r 2 := by
    have hb := hc1.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2p (h : 0<p 2) : p 2-1≤r 2 ∧ p 0≤r 0 ∧ p 1≤r 1 := by
    have hb := hc2.2 p hp h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2q (h : 0<q 2) : q 2-1≤r 2 ∧ q 0≤r 0 ∧ q 1≤r 1 := by
    have hb := hc2.2 q hq h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have h2r (h : 0<r 2) : r 2-1≤r 2 ∧ r 0≤r 0 ∧ r 1≤r 1 := by
    have hb := hc2.2 r hr h
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    simp only [plainPredecessor_apply] at hb0 hb1 hb2
    norm_num [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hb0 hb1 hb2
    omega
  have he0p (h : 0 < p 0) : p = r ∨ p 0 = r 0 + 1 := by
    by_cases he : p = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hp he h).1
  have he0q (h : 0 < q 0) : q = r ∨ q 0 = r 0 + 1 := by
    by_cases he : q = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hq he h).1
  have he0r (h : 0 < r 0) : r = r ∨ r 0 = r 0 + 1 := by
    by_cases he : r = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc0 hr he h).1
  have he1p (h : 0 < p 1) : p = r ∨ p 1 = r 1 + 1 := by
    by_cases he : p = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hp he h).1
  have he1q (h : 0 < q 1) : q = r ∨ q 1 = r 1 + 1 := by
    by_cases he : q = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hq he h).1
  have he1r (h : 0 < r 1) : r = r ∨ r 1 = r 1 + 1 := by
    by_cases he : r = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc1 hr he h).1
  have he2p (h : 0 < p 2) : p = r ∨ p 2 = r 2 + 1 := by
    by_cases he : p = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hp he h).1
  have he2q (h : 0 < q 2) : q = r ∨ q 2 = r 2 + 1 := by
    by_cases he : q = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hq he h).1
  have he2r (h : 0 < r 2) : r = r ∨ r 2 = r 2 + 1 := by
    by_cases he : r = r
    · exact Or.inl he
    · exact Or.inr (plain_centre_other_root_coordinates {p,q,r} ha hc2 hr he h).1
  simp only [hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr,
    false_or,true_or,implies_true] at he0p he0q he0r he1p he1q he1r he2p he2q he2r
  clear active hp hq hr
  clear hc0 hc1 hc2 ha hv hpq hpr hqr
  by_cases hz0 : r 0 = 0
  ·
    have h : (p 0>0 ∧ p 1=0 ∧ p 2=0 ∧ q 0=0 ∧ r 0=0) ∨ (q 0>0 ∧ q 1=0 ∧ q 2=0 ∧ p 0=0 ∧ r 0=0) := by omega
    right; left
    rcases h with h | h
    · exact Or.inl (h)
    · exact Or.inr (Or.inl (h))
  ·
    by_cases hz1 : r 1 = 0
    ·
      have h : (p 1>0 ∧ p 0=0 ∧ p 2=0 ∧ q 1=0 ∧ r 1=0) ∨ (q 1>0 ∧ q 0=0 ∧ q 2=0 ∧ p 1=0 ∧ r 1=0) := by omega
      right; left
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h)))))
    ·
      by_cases hz2 : r 2 = 0
      ·
        have h : (p 2>0 ∧ p 0=0 ∧ p 1=0 ∧ q 2=0 ∧ r 2=0) ∨ (q 2>0 ∧ q 0=0 ∧ q 1=0 ∧ p 2=0 ∧ r 2=0) := by omega
        right; left
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))))
      ·
        have hpos : 0<r 0 ∧ 0<r 1 ∧ 0<r 2 := by omega
        have haxis1 : plainPureAxis p := by
          simp only [plainPureAxis]
          omega
        have haxis2 : plainPureAxis q := by
          simp only [plainPureAxis]
          omega
        right; right
        exact Or.inr (Or.inr (⟨hpos.1,hpos.2.1,hpos.2.2,haxis1,haxis2⟩))

theorem plain_three_root_coordinate_patterns (p q r : PlainExp)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (ha : PlainRootAntichain {p,q,r}) (hv : PlainVariablesSurvive {p,q,r})
    (hc : HasPlainDirectionalCentres {p,q,r}) :
    plainTrianglePattern p q r ∨ plainPlaneSplitPattern p q r ∨ plainDominantAxisPattern p q r := by
  obtain ⟨c0,hc0⟩ := hc 0
  obtain ⟨c1,hc1⟩ := hc 1
  obtain ⟨c2,hc2⟩ := hc 2
  have hm0 := hc0.1
  have hm1 := hc1.1
  have hm2 := hc2.1
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm0 hm1 hm2
  rcases hm0 with hm0 | hm0 | hm0 <;>
    rcases hm1 with hm1 | hm1 | hm1 <;>
    rcases hm2 with hm2 | hm2 | hm2
  all_goals subst c0 c1 c2
  · exact plain_centre_assignment_0 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_1 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_2 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_3 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_4 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_5 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_6 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_7 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_8 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_9 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_10 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_11 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_12 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_13 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_14 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_15 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_16 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_17 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_18 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_19 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_20 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_21 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_22 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_23 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_24 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_25 p q r hpq hpr hqr ha hv hc0 hc1 hc2
  · exact plain_centre_assignment_26 p q r hpq hpr hqr ha hv hc0 hc1 hc2


end
end P23.Monomial
