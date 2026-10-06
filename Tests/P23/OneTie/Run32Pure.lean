import P23.OneTie.RhoFourPure

#check P23.OneTie.pure_three_border_standard_slices
#check P23.OneTie.pure_three_border_type_formula
#check P23.OneTie.pure_three_border_type_three_iff
#check P23.OneTie.pure_three_border_roots_exact
#check P23.OneTie.pure_three_border_ng_forces_endpoints

open P23.OneTie P23.Artin P23.Presentation
variable {a b : ℕ} [NeZero a] {S : Finset (Normal a b 0)}
example (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hl : IsLiveTie S) (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hn : QuotientNearlyGorenstein ℚ S hS hd hl) :
    P.r = 1 ∧ P.v = P.u+b-1 ∧ P.w = P.C-1 :=
  pure_three_border_ng_forces_endpoints P hS hd hl ha ht hn
