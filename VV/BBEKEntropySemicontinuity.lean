import VV.BBEKBowenMetric
import VV.BBEKTopology
import VV.BBEKEntropyTrapped
import VV.Entropy.BowenSemicontinuity

/-! Actual system-entropy semicontinuity on compact forward invariant
subsets of the BBEK homogeneous space. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace VV.BBEKEntropySemicontinuity
open BBEKDynamics BBEKQuotient BBEKTopology BBEKEntropyExpansion
open BBEKEntropyNets BBEKEntropyTrapped BBEKFiniteBowen
open ErgodicTheory.Entropy

theorem compact_entropy_eventually_lt {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : 0 < t) (hf : MapsTo (timeMap t) Y Y)
    {J : Type*} {L : Filter J} {μs : J → ProbabilityMeasure Y} {μ : ProbabilityMeasure Y}
    (hμ : Tendsto μs L (𝓝 μ))
    (hT : MeasurePreserving (restrictedTimeMap hf) (μ : Measure Y) (μ : Measure Y))
    (hTs : ∀ j, MeasurePreserving (restrictedTimeMap hf)
      (μs j : Measure Y) (μs j : Measure Y))
    {c : ℝ} (hc : ksEntropy hT < (c : EReal)) :
    ∀ᶠ j in L, ksEntropy (hTs j) < (c : EReal) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  obtain ⟨r,hr,hcover⟩ := compact_uniformBowenCover hY ht hf
  exact ksEntropy_eventually_lt_of_uniformBowenCover (restrictedTimeMap_continuous hf)
    hr hcover hμ hT hTs hc

/-- No geometric cover or entropy equality remains as an input: the actual
homogeneous finite-window theorem supplies all of them. -/
theorem compact_entropy_lower_bound_limit {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : 0 < t) (hf : MapsTo (timeMap t) Y Y)
    {J : Type*} {L : Filter J} [NeBot L]
    {μs : J → ProbabilityMeasure Y} {μ : ProbabilityMeasure Y}
    (hμ : Tendsto μs L (𝓝 μ))
    (hT : MeasurePreserving (restrictedTimeMap hf) (μ : Measure Y) (μ : Measure Y))
    (hTs : ∀ j, MeasurePreserving (restrictedTimeMap hf)
      (μs j : Measure Y) (μs j : Measure Y))
    {c : ℝ} (hc : ∀ᶠ j in L, (c : EReal) ≤ ksEntropy (hTs j)) :
    (c : EReal) ≤ ksEntropy hT := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  obtain ⟨r,hr,hcover⟩ := compact_uniformBowenCover hY ht hf
  exact le_ksEntropy_of_tendsto_of_uniformBowenCover (restrictedTimeMap_continuous hf)
    hr hcover hμ hT hTs hc

end VV.BBEKEntropySemicontinuity
