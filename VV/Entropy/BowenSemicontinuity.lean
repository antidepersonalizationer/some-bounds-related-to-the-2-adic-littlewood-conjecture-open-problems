import VV.Entropy.BowenGenerator

/-! System entropy semicontinuity and retention of entropy lower bounds from
the proved finite-cover form of entropy expansiveness. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace ErgodicTheory.Entropy

variable {X J : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- Full system entropy, rather than just entropy of a supplied partition,
is eventually below any real strict upper bound for the limiting entropy. -/
theorem ksEntropy_eventually_lt_of_uniformBowenCover
    {T : X → X} (hcont : Continuous T) {r : ℝ} (hr : 0 < r)
    (hcover : UniformBowenCover T r)
    {L : Filter J} {μs : J → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs L (𝓝 μ))
    (hT : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (hTs : ∀ j, MeasurePreserving T (μs j : Measure X) (μs j : Measure X))
    {c : ℝ} (hc : ksEntropy hT < (c : EReal)) :
    ∀ᶠ j in L, ksEntropy (hTs j) < (c : EReal) := by
  obtain ⟨m,P,hboundary,hmesh⟩ := exists_small_null_frontier_partition (μ : Measure X) hr
  rw [ksEntropy_eq_of_uniformBowenCover hT P hcover hmesh, EReal.coe_lt_coe_iff] at hc
  have he := ksEntropyPartition_eventually_lt P hμ hcont hT hTs hboundary hc
  filter_upwards [he] with j hj
  rw [ksEntropy_eq_of_uniformBowenCover (hTs j) P hcover hmesh, EReal.coe_lt_coe_iff]
  exact hj

/-- A lower entropy bound survives weak limits of invariant probabilities.
All measure and entropy equalities needed for this passage were proved from
finite Bowen covers; none is assumed as an extra hypothesis. -/
theorem le_ksEntropy_of_tendsto_of_uniformBowenCover
    {T : X → X} (hcont : Continuous T) {r : ℝ} (hr : 0 < r)
    (hcover : UniformBowenCover T r)
    {L : Filter J} [NeBot L] {μs : J → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs L (𝓝 μ))
    (hT : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (hTs : ∀ j, MeasurePreserving T (μs j : Measure X) (μs j : Measure X))
    {c : ℝ} (hc : ∀ᶠ j in L, (c : EReal) ≤ ksEntropy (hTs j)) :
    (c : EReal) ≤ ksEntropy hT := by
  by_contra! hn
  have he := ksEntropy_eventually_lt_of_uniformBowenCover hcont hr hcover hμ hT hTs hn
  obtain ⟨j,hj,hj'⟩ := (hc.and he).exists
  exact hj'.not_le hj

end ErgodicTheory.Entropy
