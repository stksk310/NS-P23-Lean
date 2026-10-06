import P23.Semigroup.NormalizedMonomialIdeal

noncomputable section
open P23.Semigroup P23.Presentation P23.OneTie P23.Artin
variable {a b c : ℕ} [NeZero a]

example (G : Finset (Normal a b c)) (p : Normal a b c) :
    monomial (k := ℚ) p ∈ normalGeneratorIdeal G ↔ ∃ g ∈ G, g ∣ p :=
  monomial_mem_normalGeneratorIdeal_iff G p

example (G : Finset (Normal a b c)) (p : Normal a b c)
    (hp : monomial (k := ℚ) p ∉ normalGeneratorIdeal G)
    (f : NormalMonoidAlgebra ℚ a b c) (hf : f ∈ normalGeneratorIdeal G) :
    f.coeff p = 0 := normalGeneratorIdeal_coeff_zero G p hp f hf

example (G : Finset (Normal a b c))
    [Module.Finite ℚ (NormalMonoidAlgebra ℚ a b c ⧸ normalGeneratorIdeal G)] :
    {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}.Finite :=
  normal_survivors_finite G

example (G : Finset (Normal a b c)) {d p : Normal a b c}
    (hp : monomial (k := ℚ) p ∉ normalGeneratorIdeal G) (hdiv : d ∣ p) :
    monomial (k := ℚ) d ∉ normalGeneratorIdeal G := normal_survivor_downward G hp hdiv
