import P23.Semigroup.NormalizedMonomialIdeal

noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
variable {a b c : ℕ} [NeZero a]

example (G : Finset (Normal a b c)) :
    (normalGeneratorIdeal G).comap
      (polyToNormalAlg (k := ℚ) (a := a) (b := b) (c := c)).toRingHom =
        Ideal.span (↑(normalPresentationFinset G) : Set (ThreePoly ℚ)) :=
  normalGeneratorIdeal_comap G

example (G : Finset (Normal a b c)) (n : ℕ)
    (hm : HasMinimalGeneratorCard (Ideal.span (↑(normalPresentationFinset G) : Set (ThreePoly ℚ))) n)
    (hc : (normalPresentationFinset G).card = n) :
    ∀ g ∈ G, ∀ q ∈ G, q ∣ g → q = g := normalGenerators_incomparable_of_minimal G n hm hc

example (G : Finset (Normal a b c))
    (hf : {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}.Finite)
    (hd : IsLiveParameterDomain a b c)
    (h1 : monomial (k := ℚ) (1 : Normal a b c) ∉ normalGeneratorIdeal G)
    (hm : ∀ g ∈ G, ∀ q ∈ G, q ∣ g → q = g) :
    G = borderFinset (normalSurvivorRoots G hf) := normalGenerators_eq_exact_border G hf hd h1 hm
