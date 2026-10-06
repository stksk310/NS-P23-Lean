import P23.Semigroup.RhoFourTaggedNormalization

open P23.Semigroup P23.Semigroup.FourGeneratedNumericalSemigroup
open P23.OneTie P23.Presentation

noncomputable section
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

example (hB : D.fourBaseBudget i = 1) :
    Nonempty (TaggedBudgetOneNormalization D i) :=
  taggedBudgetOneNormalization D i hB

example (T : TaggedBudgetOneNormalization D i) (hρ : D.semigroupRho = 4) :
    T.externalTags.card = 3 := by
  rw [T.external_card, hρ]

example (T : TaggedBudgetOneNormalization D i) :
    T.externalTags.image T.normalizedOfExternal = borderFinset T.presentation.roots :=
  T.external_image_exact_border

example (T : TaggedBudgetOneNormalization D i) :
    Set.InjOn T.normalizedOfExternal T.externalTags :=
  T.normalized_external_injective
