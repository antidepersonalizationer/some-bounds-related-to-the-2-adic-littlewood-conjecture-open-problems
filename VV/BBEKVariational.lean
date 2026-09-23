import VV.BBEKTopology
import VV.BBEKEntropyTrapped
import VV.Entropy.VariationalPrinciple

/-! The actual positive-entropy measure on the BBEK cone-trapped quotient. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace VV.BBEKVariational
open BBEKDynamics BBEKQuotient BBEKTopology BBEKReduction
open BBEKEntropyNets BBEKEntropyTrapped P7BoxCover
open ErgodicTheory.Entropy

/-- Failure of zero box dimension for the actual trapped unstable parameters
produces a probability on the actual compact trapped quotient, invariant
under time `(log 2 + 1, 1)`, with strictly positive KS entropy. -/
theorem exists_trapped_pos_ksEntropy {δ : ℝ} (hδ : 0 < δ)
    (hbox : ¬ GeometricZeroUpperBox (trappedParameters δ)) :
    ∃ μ : ProbabilityMeasure (trappedQuotient δ),
      ∃ hμT : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
        (μ : Measure (trappedQuotient δ)) (μ : Measure (trappedQuotient δ)),
          0 < ksEntropy hμT := by
  letI : CompactSpace (trappedQuotient δ) :=
    isCompact_iff_compactSpace.mp (compact_trappedQuotient hδ)
  letI : MetricSpace (trappedQuotient δ) :=
    TopologicalSpace.metrizableSpaceMetric (trappedQuotient δ)
  have huni : compactUniformSpace (trappedQuotient δ) (compact_trappedQuotient hδ) =
      (inferInstance : UniformSpace (trappedQuotient δ)) := by
    apply UniformSpace.ext
    exact nhdsSet_diagonal_eq_uniformity
  have hE : trappedEntropy δ hδ =
      Dynamics.coverEntropy (restrictedTimeMap (trappedTimeForward δ)) univ := by
    unfold trappedEntropy compactEntropy
    rw [huni]
  apply exists_pos_ksEntropy_of_pos_coverEntropy
    (restrictedTimeMap_continuous (trappedTimeForward δ))
  rw [← hE]
  exact trappedEntropy_pos_of_not_zero_box hδ hbox

end VV.BBEKVariational
