import P23.Semigroup.NormalizedMonomialIdeal

noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
variable {a b c : ℕ} [NeZero a]
variable (G : Finset (Normal a b c))
variable (hf : {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}.Finite)

example (hdom : IsLiveParameterDomain a b c) (p : Normal a b c) :
    p ∈ standardSet (normalSurvivorRoots G hf) ↔ monomial (k := ℚ) p ∉ normalGeneratorIdeal G :=
  normalSurvivorRoots_standardSet_iff G hf hdom p

example : IsRootAntichain (normalSurvivorRoots G hf) := normalSurvivorRoots_antichain G hf

example (hdom : IsLiveParameterDomain a b c)
    (h1 : monomial (k := ℚ) (1 : Normal a b c) ∉ normalGeneratorIdeal G) :
    (normalSurvivorRoots G hf).Nonempty := normalSurvivorRoots_nonempty G hf hdom h1
