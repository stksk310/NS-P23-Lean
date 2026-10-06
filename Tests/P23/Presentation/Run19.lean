import P23.Presentation.HL5Quotient

open P23.OneTie P23.Artin P23.Presentation

#check rootCard_eq_three_of_quotientType_eq_three
#check directNearlyGorenstein_of_quotientNearlyGorenstein
#check mixed_quotient_HL5_border_ne_four
#check pure_quotient_HL5_border_ne_four
#check mixed_quotient_HL5_kernel_mu_ne_five
#check pure_quotient_HL5_kernel_mu_ne_five
#check CanonicalFiniteQuotientHL5
#check canonicalFiniteQuotient_HL5

namespace P23.Tests.Run19

noncomputable section

open P23.OneTie P23.Artin P23.Presentation

variable {k : Type*} [Field k]

section Mixed

variable {a b c : ℕ} [NeZero a]

example (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive) :
    (borderFinset S).card ≠ 4 :=
  mixed_quotient_HL5_border_ne_four
    (k := k) S ha hb hc hlive hanti htype hng

example (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive) :
    idealGeneratorMu (k := k)
      (RingHom.ker (polyToDirectAlg (k := k) S).toRingHom) ≠ 5 :=
  mixed_quotient_HL5_kernel_mu_ne_five
    (k := k) S ha hb hc hlive hanti htype hng

end Mixed

section Pure

variable {a b : ℕ} [NeZero a]

example (S : Finset (Normal a b 0)) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive) :
    (borderFinset S).card ≠ 4 :=
  pure_quotient_HL5_border_ne_four
    (k := k) S ha hb hlive hanti htype hng

example (S : Finset (Normal a b 0)) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive) :
    idealGeneratorMu (k := k)
      (RingHom.ker (polyToDirectAlg (k := k) S).toRingHom) ≠ 5 :=
  pure_quotient_HL5_kernel_mu_ne_five
    (k := k) S ha hb hlive hanti htype hng

end Pure

-- Nonprimitive mixed and pure parameters exercise that the public statements
-- impose no hidden primitivity hypothesis.
example (S : Finset (Normal 4 2 2)) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩ hlive) :
    (borderFinset S).card ≠ 4 :=
  mixed_quotient_HL5_border_ne_four
    (k := k) S (by decide) (by decide) (by decide)
      hlive hanti htype hng

example (S : Finset (Normal 4 2 0)) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨by decide, Or.inr ⟨by decide, rfl⟩⟩ hlive) :
    (borderFinset S).card ≠ 4 :=
  pure_quotient_HL5_border_ne_four
    (k := k) S (by decide) (by decide) hlive hanti htype hng

end

end P23.Tests.Run19
