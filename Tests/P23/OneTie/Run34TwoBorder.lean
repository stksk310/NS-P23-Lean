import P23.OneTie.TwoBorderTypeOne
open P23.OneTie P23.Artin P23.Presentation
noncomputable section
variable {a b c : ℕ} [NeZero a]

-- Break caught: accepting a two-border live model with more than one socle root.
example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S) :
    2 ≤ (borderFinset S).card := live_one_tie_border_card_ge_two S hS hd hl

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (hc : (borderFinset S).card = 2) : S.card = 1 :=
  live_two_border_root_card_one S hS hd hl ha hc

example {S T : Finset (Normal a b c)} (hS : S.Nonempty) (hT : T.Nonempty)
    (hd : IsLiveParameterDomain a b c) (he : borderFinset S = borderFinset T) :
    standardSet S = standardSet T := standardSet_eq_of_borderFinset_eq hS hT hd he

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hc : 0 < c) :
    2 ≤ (borderFinset S).card := mixed_live_border_card_ge_two S hS hd hc

example (S : Finset (Normal a b 0)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b 0) :
    2 ≤ (borderFinset S).card := pure_live_border_card_ge_two S hS hd

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S) (ha : IsRootAntichain S)
    (hc : 0 < c) (hg : (borderFinset S).card = 2) : S.card = 1 :=
  mixed_live_two_border_root_card_one S hS hd hl ha hc hg

example (S : Finset (Normal a b 0)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b 0) (hl : IsLiveTie S) (ha : IsRootAntichain S)
    (hg : (borderFinset S).card = 2) : S.card = 1 :=
  pure_live_two_border_root_card_one S hS hd hl ha hg

example (k : Type*) [Field k] (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S) (ha : IsRootAntichain S)
    (hg : (borderFinset S).card = 2) : quotientType k S hS hd hl = 1 :=
  live_two_border_quotient_type_eq_one k S hS hd hl ha hg
