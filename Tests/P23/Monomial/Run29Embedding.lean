import P23.Monomial.PlainEmbedding
namespace P23.Monomial
variable {k : Type*} [Field k] (R : Finset PlainExp) (hR : R.Nonempty)
example : plainEmbeddingDimension k R hR = 3 ↔ PlainVariablesSurvive R :=
  plain_embeddingDimension_eq_three_iff_variablesSurvive R hR
end P23.Monomial
