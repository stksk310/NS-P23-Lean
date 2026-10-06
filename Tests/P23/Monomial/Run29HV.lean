import P23.Monomial.PlainHV
namespace P23.Monomial
variable {k : Type*} [Field k]
example (G : Finset PlainExp) (hf : (plainSurvivors k G).Finite)
    (h0 : (0 : PlainExp) ∈ plainSurvivors k G)
    (hm : P23.Presentation.HasMinimalGeneratorCard (plainMonomialIdeal k G) G.card)
    (hed : plainEmbeddingDimension k (plainSurvivorRoots k G hf)
      (plainSurvivorRoots_nonempty k G hf h0) = 3)
    (ht : plainDirectType k (plainSurvivorRoots k G hf)
      (plainSurvivorRoots_nonempty k G hf h0) = 3)
    (hn : PlainDirectNearlyGorenstein k (plainSurvivorRoots k G hf)
      (plainSurvivorRoots_nonempty k G hf h0)) :
    P23.Presentation.idealGeneratorMu (plainMonomialIdeal k G) ≠ 5 :=
  plainMonomial_typeThree_nearlyGorenstein_mu_ne_five G hf h0 hm hed ht hn
end P23.Monomial
