import VV.BBEKEntropySemicontinuity
import VV.BBEKConeEntropy

/-! Positive entropy survives actual cone averaging and the weak limit,
giving a probability invariant under the full real/integer diagonal action. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace VV.BBEKPositiveDiagonal
open BBEKDynamics BBEKQuotient BBEKTopology BBEKReduction P7BoxCover
open BBEKEntropyNets BBEKEntropyTrapped BBEKEntropyExpansion BBEKDiagonalAverage
open BBEKConeAverage BBEKConeEntropy BBEKEntropySeed BBEKEntropySemicontinuity
open ErgodicTheory.Entropy

/-- The positive-topological-entropy obstruction produces an actual
full-psi-invariant probability on the homogeneous space, supported by Kδ,
and retaining strictly positive entropy for the designated diagonal time. -/
theorem exists_psi_invariant_pos_ksEntropy_supported_K {δ : ℝ} (hδ : 0 < δ)
    (hbox : ¬ GeometricZeroUpperBox (trappedParameters δ)) :
    ∃ μ : ProbabilityMeasure X,
      SMulInvariantMeasure H X (μ : Measure X) ∧
      (μ : Measure X) (BBEKOrbit.K δ) = 1 ∧
      ∃ hμT : MeasurePreserving (timeMap time0) (μ : Measure X) (μ : Measure X),
        0 < ksEntropy hμT := by
  obtain ⟨ν,hν,hpos,havg⟩ := exists_pos_ksEntropy_coneAverages hδ hbox
  obtain ⟨c,hc,hcν⟩ := EReal.exists_between_coe_real hpos
  obtain ⟨μ,φ,hφ,hlim,hH,hK⟩ := exists_psi_invariant_coneAverage_subseq hδ (fun _ => ν)
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace (trappedQuotient δ) :=
    isCompact_iff_compactSpace.mp (compact_trappedQuotient hδ)
  have hlength : Tendsto (fun j => φ j + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have hμT : MeasurePreserving (restrictedTimeMap (trappedTimeForward δ))
      (μ : Measure (trappedQuotient δ)) (μ : Measure (trappedQuotient δ)) :=
    (tripleAverage_limit_measurePreserving
      (continuous_generatorMap δ 0) (continuous_generatorMap δ 1) (continuous_generatorMap δ 2)
      (generatorMap_commute δ 0 1) (generatorMap_commute δ 0 2) (generatorMap_commute δ 1 2)
      (fun j => φ j + 1) (fun _ => Nat.zero_lt_succ _) hlength (fun _ => ν) hlim).2.2
  have htime : 0 < time0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans time0_gt_log_two
  have hbound : (c : EReal) ≤ ksEntropy hμT :=
    compact_entropy_lower_bound_limit (compact_trappedQuotient hδ) htime
      (trappedTimeForward δ) hlim hμT
      (fun j => coneAverage_timeInvariant δ (φ j+1) (by omega) ν hν)
      (Filter.Eventually.of_forall (fun j => by rw [havg]; exact hcν.le))
  obtain ⟨hX,hEntropy⟩ := toQuotient_entropy δ μ hμT
  exact ⟨toQuotient δ μ,hH,hK,hX,hEntropy.symm ▸ hc.trans_le hbound⟩

end VV.BBEKPositiveDiagonal
