import P23.Monomial.PlainNoFive
import P23.Monomial.PlainEmbedding
import P23.Monomial.PlainSocle
import P23.Monomial.PlainTraceToCentre
import P23.Monomial.PlainMonomialIdeal

/-! The exact type-three, embedding-dimension-three monomial consequence needed
by the human proof. This is not the full published Huneke--Vraciu classification.
Acceptance remains pending until the corrected combinatorial cover is GREEN
and the complete Run29 layer has passed independent audit. -/
namespace P23.Monomial
noncomputable section
variable {k : Type*} [Field k]

theorem plainMonomial_typeThree_nearlyGorenstein_mu_ne_five
    (G : Finset PlainExp) (hf : (plainSurvivors k G).Finite)
    (h0 : (0 : PlainExp) ∈ plainSurvivors k G)
    (hm : P23.Presentation.HasMinimalGeneratorCard (plainMonomialIdeal k G) G.card)
    (hed : plainEmbeddingDimension k (plainSurvivorRoots k G hf)
      (plainSurvivorRoots_nonempty k G hf h0) = 3)
    (ht : plainDirectType k (plainSurvivorRoots k G hf)
      (plainSurvivorRoots_nonempty k G hf h0) = 3)
    (hn : PlainDirectNearlyGorenstein k (plainSurvivorRoots k G hf)
      (plainSurvivorRoots_nonempty k G hf h0)) :
    P23.Presentation.idealGeneratorMu (plainMonomialIdeal k G) ≠ 5 := by
  let R := plainSurvivorRoots k G hf
  have hR : R.Nonempty := plainSurvivorRoots_nonempty k G hf h0
  have ha : PlainRootAntichain R := plainSurvivorRoots_antichain k G hf
  have hv : PlainVariablesSurvive R :=
    (plain_embeddingDimension_eq_three_iff_variablesSurvive R hR).mp hed
  have hcard : R.card = 3 := by
    rw [plainDirectType_eq_rootCard _ _ ha] at ht
    exact ht
  have htrace : PlainVariablesInTrace k R hv := by
    intro j
    apply hn
    apply plain_PX_mem_augmentation
    intro he
    have he' := congrArg (fun p : PlainExp => p j) he
    simpa using he'
  have hc : HasPlainDirectionalCentres R :=
    plain_hasDirectionalCentres_of_variablesInTrace R hR (by omega) ha hv htrace
  have hno := plain_three_root_no_five R ha hcard hv hc
  have hG := plainGenerators_antichain_of_minimal k G hm
  have he := plainGenerators_eq_border k G hf hG
  rw [plain_idealGeneratorMu_eq_of_minimal _ _ hm,he]
  exact hno

end
end P23.Monomial
