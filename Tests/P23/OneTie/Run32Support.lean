import P23.OneTie.ThreeBorderSupport

open P23.OneTie
variable {a b c : ℕ} [NeZero a]

example (q : Normal a b c) : (normalSupport q).card ≤ 3 :=
  normalSupport_card_le_three q

example (S : Finset (Normal a b c)) (hS : S.Nonempty) (hl : IsLiveTie S)
    (q : Normal a b c) (hq : q ∈ borderFinset S) : ¬ NormalIsPureX q :=
  border_not_pure_x hS hl hq
