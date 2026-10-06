import P23.Presentation.LocalDominance
namespace P23.Presentation
open P23.OneTie P23.Artin
variable {k : Type*} [Field k] {a b c : ℕ} [NeZero a]
example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (h : CoverHypotheses S) :
    idealGeneratorMu (finitePresentationIdeal (k:=k) S) ≤ S.card+3 :=
  oneTie_nondominant_kernel_mu_le_type_plus_three S hS hd h
example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (hc : 2≤S.card)
    (hn : QuotientNearlyGorenstein k S hS hd hl) : HasDirectionalCentres S :=
  canonical_ng_hasDirectionalCentres S hS hd hl ha hc hn
example (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (ht : S.card=2 ∨ S.card=3)
    (hn : QuotientNearlyGorenstein k S hS hd hl)
    (hm : S.card+4 ≤ idealGeneratorMu (finitePresentationIdeal (k:=k) S)) :
    ∃ s∈S, IsDominantRoot S s :=
  oneTie_ng_kernel_mu_ge_type_plus_four_has_dominant S hS hd hl ha ht hn hm
end P23.Presentation
