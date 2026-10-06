import P23.Monomial.PlainMonomialIdeal
open P23.Monomial

-- Detects confusing ideal membership with selected-generator equality.
example (k : Type*) [Field k] (G : Finset PlainExp) (p : PlainExp) :
    MvPolynomial.monomial p (1 : k) ∈ plainMonomialIdeal k G ↔
      ∃ g ∈ G, plainDivides g p := monomial_mem_plainMonomialIdeal_iff k G p

example (k : Type*) [Field k] (G : Finset PlainExp)
    [Module.Finite k (MvPolynomial (Fin 3) k ⧸ plainMonomialIdeal k G)] :
    (plainSurvivors k G).Finite := plainSurvivors_finite k G

example (k : Type*) [Field k] (G : Finset PlainExp) (hf : (plainSurvivors k G).Finite)
    (p : PlainExp) :
    p ∈ plainStandardSet (plainSurvivorRoots k G hf) ↔ p ∈ plainSurvivors k G :=
  plainSurvivorRoots_standard_iff k G hf p

example (k : Type*) [Field k] (G : Finset PlainExp) (hf : (plainSurvivors k G).Finite)
    (hm : PlainRootAntichain G) : G = plainBorderFinset (plainSurvivorRoots k G hf) :=
  plainGenerators_eq_border k G hf hm

example (k : Type*) [Field k] (G : Finset PlainExp)
    (hm : P23.Presentation.HasMinimalGeneratorCard (plainMonomialIdeal k G) G.card) :
    PlainRootAntichain G := plainGenerators_antichain_of_minimal k G hm
