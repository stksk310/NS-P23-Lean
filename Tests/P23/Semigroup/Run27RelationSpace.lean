import P23.Semigroup.ChosenBaseRelationSpace

noncomputable section

open P23.Semigroup P23.Presentation
open FourGeneratedNumericalSemigroup
variable {k : Type*} [Field k] (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

example (f : chosenBaseDefiningIdeal (k := k) D i) : ChosenBaseRelationSpace k D i :=
  chosenBaseRelationClass D i f.1 f.2

example (f : chosenBaseDefiningIdeal (k := k) D i) :
    f ∈ chosenBaseRelationSubmodule D i ↔
      (f : TailPoly k) ∈ polyVariableIdeal * chosenBaseDefiningIdeal D i :=
  mem_chosenBaseRelationSubmodule_iff D i f
example (q f : TailPoly k) (hf : f ∈ chosenBaseDefiningIdeal D i) :
    chosenBaseRelationClass D i (q * f) ((chosenBaseDefiningIdeal D i).mul_mem_left q hf) =
      MvPolynomial.constantCoeff q • chosenBaseRelationClass D i f hf :=
  chosenBaseRelationClass_mul_eq_smul D i q f hf
example (f g : TailPoly k) (hf : f ∈ chosenBaseDefiningIdeal D i)
    (hg : g ∈ chosenBaseDefiningIdeal D i) :
    chosenBaseRelationClass D i (f + g) ((chosenBaseDefiningIdeal D i).add_mem hf hg) =
      chosenBaseRelationClass D i f hf + chosenBaseRelationClass D i g hg :=
  chosenBaseRelationClass_add D i f g hf hg
example (r : k) (f : TailPoly k) (hf : f ∈ chosenBaseDefiningIdeal D i) :
    chosenBaseRelationClass D i (r • f)
      ((chosenBaseDefiningIdeal D i).restrictScalars k |>.smul_mem r hf) =
      r • chosenBaseRelationClass D i f hf :=
  chosenBaseRelationClass_smul D i r f hf
example : Ideal.span (↑(specializedConnectorFinset (k := k) D i) : Set (TailPoly k)) =
    chosenBaseDefiningIdeal D i := specializedConnectorFinset_span_eq D i
example : (specializedConnectorFinset (k := k) D i).card ≤ D.semigroupRho :=
  specializedConnectorFinset_card_le_rho D i

end
