import P23.OneTie.RhoFourMixed

#check P23.OneTie.mixed_three_border_no_x_type_le_two
#check P23.OneTie.mixed_three_border_standard_slices
#check P23.OneTie.mixed_three_border_type_three_iff
#check P23.OneTie.mixed_three_border_roots_exact
#check P23.OneTie.mixed_three_border_z_not_trace

open P23.OneTie P23.Artin P23.Presentation
variable {a b c : ℕ} [NeZero a]

example (S : Finset (Normal a b c)) (M : MixedThreeBorderData S)
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) :
    quotientType ℚ S hS hd hl = 3 ↔ b < M.B ∧ c+M.v < M.C :=
  mixed_three_border_type_three_iff M hS hd hl ha

example (S : Finset (Normal a b c)) (M : MixedThreeBorderData S)
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3) :
    let hzS := (mem_standardFinset_iff_standardSet S Normal.zGenerator).mpr hl.2.2.1
    X (k := ℚ) S Normal.zGenerator hzS ∉ TraceSubmodule ℚ S :=
  mixed_three_border_z_not_trace M hS hd hl ha ht
