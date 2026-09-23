import VV.Entropy.InvariantExtreme
import VV.Entropy.BowenSemicontinuity

/-! Positive entropy can be retained when selecting a jointly ergodic
probability. This is proved by maximizing actual KS entropy in moment space,
using the proved finite Bowen cover criterion, not an ergodic decomposition
or a postulated affine entropy functional. -/

noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace ErgodicTheory.Entropy
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

def invariantPartitionEntropy (F : I → X → X) (i : I) {m : ℕ}
    (P : FixedPartition X (Fin m)) (μ : invariantProbabilities F) : ℝ :=
  ksEntropyPartition (μ.property i) (P.toMeasurePartition (μ.val : Measure X))

theorem invariantPartitionEntropy_eq_system (F : I → X → X) (i : I)
    {m : ℕ} (P : FixedPartition X (Fin m)) {r : ℝ}
    (hcover : UniformBowenCover (F i) r)
    (hmesh : ∀ j, ∀ x ∈ P.cells j, ∀ y ∈ P.cells j, dist x y < r)
    (μ : invariantProbabilities F) :
    ksEntropy (μ.property i) = (invariantPartitionEntropy F i P μ : EReal) :=
  ksEntropy_eq_of_uniformBowenCover (μ.property i) P hcover hmesh

theorem upperSemicontinuous_invariantPartitionEntropy (F : I → X → X) (i : I)
    (hcont : Continuous (F i)) {m : ℕ} (P : FixedPartition X (Fin m))
    {r : ℝ} (hr : 0 < r) (hcover : UniformBowenCover (F i) r)
    (hmesh : ∀ j, ∀ x ∈ P.cells j, ∀ y ∈ P.cells j, dist x y < r) :
    UpperSemicontinuous (invariantPartitionEntropy F i P) := by
  intro μ c hc
  have hsys := invariantPartitionEntropy_eq_system F i P hcover hmesh
  have he := ksEntropy_eventually_lt_of_uniformBowenCover hcont hr hcover
    (continuous_subtype_val.continuousAt (x := μ)) (μ.property i)
    (fun ν : invariantProbabilities F => ν.property i)
    (by rw [hsys μ]; exact EReal.coe_lt_coe_iff.mpr hc)
  filter_upwards [he] with ν hν
  rw [hsys ν,EReal.coe_lt_coe_iff] at hν
  exact hν

theorem exists_extreme_entropy_ge (F : I → X → X) (hF : ∀ i, Continuous (F i))
    (i : I) {r : ℝ} (hr : 0 < r) (hcover : UniformBowenCover (F i) r)
    (μ₀ : ProbabilityMeasure X) (hμ₀ : μ₀ ∈ invariantProbabilities F) :
    ∃ μ : ProbabilityMeasure X, ∃ hμ : μ ∈ invariantProbabilities F,
      probabilityMoments μ ∈ extremePoints ℝ (probabilityMoments '' invariantProbabilities F) ∧
      ksEntropy (hμ₀ i) ≤ ksEntropy (hμ i) := by
  classical
  let C := invariantProbabilities F
  letI : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_invariantProbabilities F hF)
  letI : Nonempty C := ⟨⟨μ₀,hμ₀⟩⟩
  obtain ⟨m,P,_,hmesh⟩ := exists_small_null_frontier_partition (μ₀ : Measure X) hr
  let h : C → ℝ := invariantPartitionEntropy F i P
  let σ : C → (X →ᵇ ℝ) → ℝ := fun μ => probabilityMoments μ.val
  have hsys : ∀ μ : C, ksEntropy (μ.property i) = (h μ : EReal) :=
    invariantPartitionEntropy_eq_system F i P hcover hmesh
  have hσ : Continuous σ := continuous_probabilityMoments.comp continuous_subtype_val
  have hinj : Injective σ := probabilityMoments_injective.comp Subtype.val_injective
  have hclosed (c : ℝ) : IsClosed {μ : C | c ≤ h μ} :=
    (upperSemicontinuous_invariantPartitionEntropy F i (hF i) P hr hcover hmesh).isClosed_preimage c
  have haff (μ ν ξ : C) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
      (heq : σ ξ = a • σ μ + b • σ ν) : h ξ = a * h μ + b * h ν := by
    let a' : ℝ≥0 := ⟨a,ha.le⟩
    let b' : ℝ≥0 := ⟨b,hb.le⟩
    have hab' : a' + b' = 1 := by
      apply NNReal.eq
      exact hab
    let ζ := binaryMixture a' b' hab' μ.val ν.val
    have hζ : ζ ∈ invariantProbabilities F := fun j =>
      binaryMixture_measurePreserving a' b' hab' μ.val ν.val (μ.property j) (ν.property j)
    have hξζ : ξ.val = ζ := by
      apply probabilityMoments_injective
      rw [probabilityMoments_binaryMixture]
      exact heq
    have hsub : ξ = (⟨ζ,hζ⟩ : C) := Subtype.ext hξζ
    have hent := ksEntropy_binaryMixture a' b' hab' μ.val ν.val
      (μ.property i) (ν.property i) (h μ) (h ν) (hsys μ) (hsys ν)
    have he : (h ξ : EReal) = ((a * h μ + b * h ν : ℝ) : EReal) := by
      rw [← hsys ξ,hsub]
      exact hent
    exact EReal.coe_injective he
  obtain ⟨μ,hext,hmax⟩ := exists_extreme_max_of_compact_param σ hσ hinj h hclosed haff
  refine ⟨μ.val,μ.property,?_,?_⟩
  · have hrange : range σ = probabilityMoments '' invariantProbabilities F := by
      ext z
      exact ⟨fun ⟨ν,hν⟩ => ⟨ν.val,ν.property,hν⟩,
        fun ⟨ν,hν,hz⟩ => ⟨⟨ν,hν⟩,hz⟩⟩
    rwa [hrange] at hext
  · rw [hsys ⟨μ₀,hμ₀⟩,hsys μ]
    exact EReal.coe_le_coe_iff.mpr (hmax ⟨μ₀,hμ₀⟩)

theorem exists_jointlyErgodic_entropy_ge (F : I → X → X) (hF : ∀ i, Continuous (F i))
    (i : I) {r : ℝ} (hr : 0 < r) (hcover : UniformBowenCover (F i) r)
    (μ₀ : ProbabilityMeasure X) (hμ₀ : μ₀ ∈ invariantProbabilities F) :
    ∃ μ : ProbabilityMeasure X, ∃ hμ : μ ∈ invariantProbabilities F,
      ksEntropy (hμ₀ i) ≤ ksEntropy (hμ i) ∧
      ∀ s : Set X, MeasurableSet s →
        (∀ j, (F j) ⁻¹' s =ᵐ[(μ : Measure X)] s) → EventuallyConst s (ae (μ : Measure X)) := by
  obtain ⟨μ,hμ,hext,hge⟩ := exists_extreme_entropy_ge F hF i hr hcover μ₀ hμ₀
  exact ⟨μ,hμ,hge,fun _ hs hinv => aeconst_of_extreme_invariantMoments F μ hext hs hinv⟩

end ErgodicTheory.Entropy
