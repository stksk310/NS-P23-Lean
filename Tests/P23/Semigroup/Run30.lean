import P23.Semigroup.RhoFiveExclusion

/-! Typed public contracts: weakening or adding hypotheses, dropping the pure
dependent-index branch, or exposing only a stronger internal API breaks these. -/
namespace P23.Semigroup
open P23.OneTie P23.Artin P23.Presentation

example {a b c : ℕ} [NeZero a] (S : Finset (Normal a b c))
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S)
    (ht : quotientType ℚ S (nonempty_of_isLiveTie S hl) hd hl = 3)
    (hn : QuotientNearlyGorenstein ℚ S (nonempty_of_isLiveTie S hl) hd hl) :
    (borderFinset S).card ≠ 4 :=
  canonicalQuotient_HL5_border_ne_four_of_liveDomain S hd hl ha ht hn

example {a b c : ℕ} [NeZero a] (S : Finset (Normal a b c))
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hl : IsLiveTie S)
    (hanti : IsRootAntichain S)
    (ht : quotientType ℚ S (nonempty_of_isLiveTie S hl)
      ⟨ha, Or.inl ⟨hb,hc⟩⟩ hl = 3)
    (hn : QuotientNearlyGorenstein ℚ S (nonempty_of_isLiveTie S hl)
      ⟨ha, Or.inl ⟨hb,hc⟩⟩ hl) : (borderFinset S).card ≠ 4 :=
  canonicalQuotient_HL5_border_ne_four_of_liveDomain S _ hl hanti ht hn

-- c remains an arbitrary index until the supplied equality is eliminated.
example {a b c : ℕ} [NeZero a] (S : Finset (Normal a b c))
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : c = 0) (hl : IsLiveTie S)
    (hanti : IsRootAntichain S)
    (ht : quotientType ℚ S (nonempty_of_isLiveTie S hl)
      ⟨ha, Or.inr ⟨hb,hc⟩⟩ hl = 3)
    (hn : QuotientNearlyGorenstein ℚ S (nonempty_of_isLiveTie S hl)
      ⟨ha, Or.inr ⟨hb,hc⟩⟩ hl) : (borderFinset S).card ≠ 4 :=
  canonicalQuotient_HL5_border_ne_four_of_liveDomain S _ hl hanti ht hn

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (B : ChosenBaseCanonicalOneTieBridge D i) :
    (borderFinset B.normalization.roots).card ≠ 4 :=
  chosenBaseCanonicalOneTie_HL5_border_ne_four B

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (B : ChosenBaseCanonicalOneTieBridge D i) (hr : D.semigroupRho = 5) :
    (borderFinset B.normalization.roots).card = 4 :=
  chosenBaseCanonicalOneTie_border_card_eq_four_of_rho_five B hr

example (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 1) (ht : D.semigroupType = 3)
    (hn : SemigroupNearlyGorenstein D) : D.semigroupRho ≠ 5 :=
  budget_one_type_three_ng_rho_ne_five D i hB ht hn

example (D : FourGeneratedNumericalSemigroup) (ht : D.semigroupType = 3)
    (hn : SemigroupNearlyGorenstein D) : D.semigroupRho ≠ 5 :=
  type_three_ng_semigroupRho_ne_five D ht hn

example (D : FourGeneratedNumericalSemigroup) (ht : D.semigroupType = 3)
    (hn : SemigroupNearlyGorenstein D) : RhoFiveExclusion D :=
  rhoFiveExclusion D ht hn
end P23.Semigroup
