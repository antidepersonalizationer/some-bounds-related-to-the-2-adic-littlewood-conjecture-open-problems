import VV.Entropy.WeakContinuity
import VV.Entropy.CompactProbability
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Actual Cesàro averages of pushforwards of a probability measure. -/
noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace ErgodicTheory.Entropy
variable {X : Type*} [MeasurableSpace X]

def orbitAverageMeasure (T : X → X) (n : ℕ) (ν : ProbabilityMeasure X) : Measure X :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.map (T^[i]) (ν : Measure X)

theorem orbitAverageMeasure_apply {T : X → X} (hT : Measurable T)
    (n : ℕ) (ν : ProbabilityMeasure X) {s : Set X} (hs : MeasurableSet s) :
    orbitAverageMeasure T n ν s =
      (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range n, (ν : Measure X) ((T^[i]) ⁻¹' s) := by
  simp [orbitAverageMeasure, Measure.smul_apply, Measure.finset_sum_apply,
    Measure.map_apply (hT.iterate _) hs]

theorem orbitAverageMeasure_univ {T : X → X} (hT : Measurable T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) :
    orbitAverageMeasure T n ν univ = 1 := by
  rw [orbitAverageMeasure_apply hT n ν MeasurableSet.univ]
  simp [hn.ne', ENNReal.inv_mul_cancel]

def orbitAverage {T : X → X} (hT : Measurable T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) : ProbabilityMeasure X :=
  ⟨orbitAverageMeasure T n ν, ⟨orbitAverageMeasure_univ hT n hn ν⟩⟩

@[simp] theorem orbitAverage_coe {T : X → X} (hT : Measurable T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) :
    (orbitAverage hT n hn ν : Measure X) = orbitAverageMeasure T n ν := rfl

theorem orbitAverage_apply {T : X → X} (hT : Measurable T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) {s : Set X} (hs : MeasurableSet s) :
    (orbitAverage hT n hn ν : Measure X) s =
      (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range n, (ν : Measure X) ((T^[i]) ⁻¹' s) :=
  orbitAverageMeasure_apply hT n ν hs

section Continuous
variable [TopologicalSpace X] [BorelSpace X]

theorem integral_orbitAverage {T : X → X} (hT : Continuous T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) (f : X →ᵇ ℝ) :
    (∫ x, f x ∂(orbitAverage hT.measurable n hn ν : Measure X)) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ x, f ((T^[i]) x) ∂(ν : Measure X) := by
  rw [orbitAverage_coe, orbitAverageMeasure, integral_smul_measure]
  have hint (i : ℕ) : Integrable f (Measure.map (T^[i]) (ν : Measure X)) := by
    letI := isProbabilityMeasure_map (hT.measurable.iterate i).aemeasurable (μ := (ν : Measure X))
    exact f.integrable _
  rw [integral_finset_sum_measure (fun i _ => hint i)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_map (hT.measurable.iterate i).aemeasurable f.continuous.aestronglyMeasurable




/-- The invariance defect of a Cesàro average is exactly its two endpoint terms. -/
theorem integral_orbitAverage_sub {T : X → X} (hT : Continuous T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) (f : X →ᵇ ℝ) :
    (∫ x, f (T x) ∂(orbitAverage hT.measurable n hn ν : Measure X)) -
      (∫ x, f x ∂(orbitAverage hT.measurable n hn ν : Measure X)) =
      ((∫ x, f ((T^[n]) x) ∂(ν : Measure X)) - ∫ x, f x ∂(ν : Measure X)) / n := by
  have hfirst := integral_orbitAverage hT n hn ν (f.compContinuous ⟨T, hT⟩)
  change (∫ x, f (T x) ∂(orbitAverage hT.measurable n hn ν : Measure X)) = _ at hfirst
  rw [hfirst, integral_orbitAverage hT n hn ν, ← mul_sub, ← Finset.sum_sub_distrib]
  have he : (∑ i ∈ Finset.range n,
      ((∫ x, f (T ((T^[i]) x)) ∂(ν : Measure X)) - ∫ x, f ((T^[i]) x) ∂(ν : Measure X))) =
      (∫ x, f ((T^[n]) x) ∂(ν : Measure X)) - ∫ x, f x ∂(ν : Measure X) := by
    simpa only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] using
      (Finset.sum_range_sub (fun i => ∫ x, f ((T^[i]) x) ∂(ν : Measure X)) n)
  change (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n,
      ((∫ x, f (T ((T^[i]) x)) ∂(ν : Measure X)) - ∫ x, f ((T^[i]) x) ∂(ν : Measure X))) = _
  rw [he, div_eq_mul_inv, mul_comm]

/-- The invariance defect is bounded independently of the seed probability. -/
theorem norm_integral_orbitAverage_sub_le {T : X → X} (hT : Continuous T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) (f : X →ᵇ ℝ) :
    ‖(∫ x, f (T x) ∂(orbitAverage hT.measurable n hn ν : Measure X)) -
      (∫ x, f x ∂(orbitAverage hT.measurable n hn ν : Measure X))‖ ≤ 2 * ‖f‖ / n := by
  rw [integral_orbitAverage_sub hT n hn ν f, norm_div, Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have h1 := (f.compContinuous ⟨T^[n], hT.iterate n⟩).norm_integral_le_norm (ν : Measure X)
  change ‖∫ x, f ((T^[n]) x) ∂(ν : Measure X)‖ ≤ _ at h1
  have h2 := f.norm_compContinuous_le ⟨T^[n], hT.iterate n⟩
  have h3 := f.norm_integral_le_norm (ν : Measure X)
  exact (norm_sub_le _ _).trans (by linarith)

/-- The seed probability may vary with the averaging length. -/
theorem integral_orbitAverage_sub_tendsto {J : Type*} {L : Filter J}
    {T : X → X} (hT : Continuous T) (n : J → ℕ) (hn : ∀ j, 0 < n j)
    (hnlim : Tendsto n L atTop) (ν : J → ProbabilityMeasure X) (f : X →ᵇ ℝ) :
    Tendsto (fun j =>
      (∫ x, f (T x) ∂(orbitAverage hT.measurable (n j) (hn j) (ν j) : Measure X)) -
      (∫ x, f x ∂(orbitAverage hT.measurable (n j) (hn j) (ν j) : Measure X))) L (𝓝 0) :=
  squeeze_zero_norm (fun j => norm_integral_orbitAverage_sub_le hT (n j) (hn j) (ν j) f)
    ((tendsto_const_div_atTop_nhds_zero_nat (2 * ‖f‖)).comp hnlim)

/-- Every weak limit of long Cesàro orbit averages is actually invariant. -/
theorem orbitAverage_limit_measurePreserving [HasOuterApproxClosed X]
    {J : Type*} {L : Filter J} [NeBot L]
    {T : X → X} (hT : Continuous T) (n : J → ℕ) (hn : ∀ j, 0 < n j)
    (hnlim : Tendsto n L atTop) (ν : J → ProbabilityMeasure X)
    {μ : ProbabilityMeasure X}
    (hμ : Tendsto (fun j => orbitAverage hT.measurable (n j) (hn j) (ν j)) L (𝓝 μ)) :
    MeasurePreserving T (μ : Measure X) (μ : Measure X) := by
  refine ⟨hT.measurable, ?_⟩
  have he : (μ.map hT.measurable.aemeasurable).toFiniteMeasure = μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    change (∫ x, f x ∂Measure.map T (μ : Measure X)) = ∫ x, f x ∂(μ : Measure X)
    rw [integral_map hT.measurable.aemeasurable f.continuous.aestronglyMeasurable]
    have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ)
      (f.compContinuous ⟨T, hT⟩)
    have h2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
    have hz := integral_orbitAverage_sub_tendsto hT n hn hnlim ν f
    exact sub_eq_zero.mp (tendsto_nhds_unique (h1.sub h2) hz)
  exact congrArg (fun ρ : FiniteMeasure X => (ρ : Measure X)) he

end Continuous
/-- Arbitrary varying seed probabilities and diverging orbit lengths admit
an invariant weak limit along a subsequence on a compact metric space. -/
theorem exists_invariant_orbitAverage_subseq [MetricSpace X] [BorelSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) (n : ℕ → ℕ) (hn : ∀ j, 0 < n j)
    (hnlim : Tendsto n atTop atTop) (ν : ℕ → ProbabilityMeasure X) :
    ∃ μ : ProbabilityMeasure X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun j => orbitAverage hT.measurable (n (φ j)) (hn (φ j)) (ν (φ j)))
        atTop (𝓝 μ) ∧
      MeasurePreserving T (μ : Measure X) (μ : Measure X) := by
  obtain ⟨μ, φ, hφ, hlim⟩ := probability_exists_tendsto_subseq
    (fun j => orbitAverage hT.measurable (n j) (hn j) (ν j))
  refine ⟨μ, φ, hφ, hlim, ?_⟩
  exact orbitAverage_limit_measurePreserving hT (n ∘ φ) (fun j => hn (φ j))
    (hnlim.comp hφ.tendsto_atTop) (ν ∘ φ) hlim

end ErgodicTheory.Entropy



