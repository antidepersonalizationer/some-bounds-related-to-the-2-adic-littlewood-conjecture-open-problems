import VV.Entropy.CompactProbability
import VV.Entropy.MixtureEntropy
import VV.Entropy.ExtremeMaximum

/-! Compact sets of invariant probabilities embedded into a real locally
convex vector space by all bounded continuous integral tests. -/

noncomputable section
open MeasureTheory Function Set
open scoped Topology BoundedContinuousFunction ENNReal NNReal

namespace ErgodicTheory.Entropy

variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def probabilityMoments (μ : ProbabilityMeasure X) : (X →ᵇ ℝ) → ℝ :=
  fun f => ∫ x, f x ∂(μ : Measure X)

theorem continuous_probabilityMoments : Continuous (probabilityMoments (X := X)) := by
  apply continuous_pi
  intro f
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

theorem probabilityMoments_injective : Injective (probabilityMoments (X := X)) := by
  intro μ ν heq
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact congrFun heq f

theorem probabilityMoments_mixture [Fintype I]
    (w : I → ℝ≥0) (hw : ∑ i, w i = 1) (ν : I → ProbabilityMeasure X) :
    probabilityMoments (probabilityMixture w hw ν) =
      ∑ i, (w i : ℝ) • probabilityMoments (ν i) := by
  funext f
  change (∫ x, f x ∂mixtureMeasure w ν) = _
  rw [mixtureMeasure,integral_finset_sum_measure]
  · simp only [integral_smul_measure,ENNReal.coe_toReal,smul_eq_mul,
      Finset.sum_apply,Pi.smul_apply,probabilityMoments]
  · intro i hi
    exact (f.integrable _).smul_measure (by simp)

def invariantProbabilities (F : I → X → X) : Set (ProbabilityMeasure X) :=
  {μ | ∀ i, MeasurePreserving (F i) (μ : Measure X) (μ : Measure X)}

theorem isClosed_invariantProbabilities (F : I → X → X) (hF : ∀ i, Continuous (F i)) :
    IsClosed (invariantProbabilities F) := by
  have hset : invariantProbabilities F =
      ⋂ i, {μ : ProbabilityMeasure X | μ.map (hF i).measurable.aemeasurable = μ} := by
    ext μ
    simp only [invariantProbabilities,mem_setOf_eq,mem_iInter]
    constructor
    · intro h i
      apply ProbabilityMeasure.toMeasure_injective
      exact (h i).map_eq
    · intro h i
      exact ⟨(hF i).measurable,congrArg ProbabilityMeasure.toMeasure (h i)⟩
  rw [hset]
  exact isClosed_iInter fun i => isClosed_eq (ProbabilityMeasure.continuous_map (hF i)) continuous_id

theorem probabilityMixture_mem_invariantProbabilities [Fintype I]
    {J : Type*} (F : J → X → X) (hF : ∀ j, Measurable (F j))
    (w : I → ℝ≥0) (hw : ∑ i, w i = 1) (ν : I → ProbabilityMeasure X)
    (hν : ∀ i, ν i ∈ invariantProbabilities F) :
    probabilityMixture w hw ν ∈ invariantProbabilities F := by
  intro j
  exact probabilityMixture_measurePreserving w hw ν (hF j) (fun i => hν i j)

variable [CompactSpace X]

theorem isCompact_invariantProbabilities (F : I → X → X) (hF : ∀ i, Continuous (F i)) :
    IsCompact (invariantProbabilities F) := (isClosed_invariantProbabilities F hF).isCompact

theorem isCompact_invariantMoments (F : I → X → X) (hF : ∀ i, Continuous (F i)) :
    IsCompact (probabilityMoments '' invariantProbabilities F) :=
  (isCompact_invariantProbabilities F hF).image continuous_probabilityMoments

end ErgodicTheory.Entropy
