import VV.BBEKVariational
import VV.BBEKConeAverage
import VV.Entropy.EmbeddingEntropy

/-! The positive-entropy seed as a genuine measure on the ambient quotient. -/

noncomputable section
open MeasureTheory Function

namespace VV.BBEKEntropySeed
open BBEKDynamics BBEKQuotient BBEKTopology BBEKReduction P7BoxCover
open BBEKEntropyTrapped BBEKEntropyNets BBEKEntropyExpansion BBEKConeAverage
open BBEKVariational ErgodicTheory.Entropy

theorem toQuotient_entropy (δ : ℝ) (μ : ProbabilityMeasure (trappedQuotient δ))
    (hμT : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (μ:Measure _) (μ:Measure _)) :
    ∃ hνT : MeasurePreserving (timeMap time0) (toQuotient δ μ : Measure X)
      (toQuotient δ μ : Measure X), ksEntropy hνT = ksEntropy hμT := by
  have hi : MeasurePreserving (generatorMap δ 2) (μ:Measure _) (μ:Measure _) := hμT
  have hνT : MeasurePreserving (timeMap time0) (toQuotient δ μ : Measure X)
      (toQuotient δ μ : Measure X) := toQuotient_generator_invariant δ μ 2 hi
  refine ⟨hνT,?_⟩
  have he : MeasurePreserving (Subtype.val : trappedQuotient δ → X)
      (μ:Measure _) (toQuotient δ μ : Measure X) := measurable_subtype_coe.measurePreserving _
  exact (ksEntropy_eq_of_embedding hμT hνT
    (.subtype_coe (isClosed_trappedQuotient δ).measurableSet) he rfl).symm

/-- Failure of zero box dimension supplies an actual probability on X,
supported by K_delta, with positive KS entropy for the designated time map. -/
theorem exists_pos_ksEntropy_supported_K {δ : ℝ} (hδ : 0 < δ)
    (hbox : ¬ GeometricZeroUpperBox (trappedParameters δ)) :
    ∃ ν : ProbabilityMeasure X,
      ∃ hνT : MeasurePreserving (timeMap time0) (ν:Measure X) (ν:Measure X),
        (ν:Measure X) (BBEKOrbit.K δ) = 1 ∧ 0 < ksEntropy hνT := by
  obtain ⟨μ,hμT,hpos⟩ := exists_trapped_pos_ksEntropy hδ hbox
  obtain ⟨hνT,he⟩ := toQuotient_entropy δ μ hμT
  exact ⟨toQuotient δ μ,hνT,toQuotient_K_mass δ μ,he ▸ hpos⟩

end VV.BBEKEntropySeed
