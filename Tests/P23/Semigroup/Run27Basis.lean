import P23.Semigroup.ChosenBaseRelationSpace
namespace P23.Semigroup
noncomputable section
variable {k : Type*} [Field k] (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
example : Module.finrank k (ChosenBaseRelationSpace k D i) = D.semigroupRho :=
  chosenBaseRelationSpace_finrank D i
example (g : D.BaseAdaptedGlobalConnector i) :
    chosenBaseRelationBasis (k := k) D i g = displayedChosenBaseRelation D i g :=
  chosenBaseRelationBasis_apply D i g
example (G : Finset (TailPoly k))
    (hG : Ideal.span (↑G : Set (TailPoly k)) = chosenBaseDefiningIdeal D i) :
    Submodule.span k (Set.range (chosenBaseGeneratorClass D i G hG)) = ⊤ :=
  chosenBaseGeneratorClasses_span_eq_top D i G hG
end
end P23.Semigroup
