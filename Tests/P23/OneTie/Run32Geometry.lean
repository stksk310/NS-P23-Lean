import P23.OneTie.ThreeBorderGeometry

open P23.OneTie P23.Artin P23.Presentation
variable {a b c : ℕ} [NeZero a]

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hc : 0 < c) :
    ∃ B, 0 < B ∧ yAxis B ∈ borderFinset S :=
  mixed_pure_y_border_exists S hS hd hc

example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hb : 0 < b) :
    ∃ C, 0 < C ∧ zAxis C ∈ borderFinset S :=
  pure_z_border_exists S hS hd hb
