import VV.Entropy.OrbitAverage

/-! Finite commuting averages and simultaneous invariance of their weak limits. -/

noncomputable section
open MeasureTheory Function Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace ErgodicTheory.Entropy
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

theorem orbitAverage_map_semiconj {Y : Type*} [MeasurableSpace Y]
    {T : X → X} {S : Y → Y} {f : X → Y}
    (hT : Measurable T) (hS : Measurable S) (hf : Measurable f)
    (he : Function.Semiconj f T S) (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) :
    (orbitAverage hT n hn ν).map hf.aemeasurable =
      orbitAverage hS n hn (ν.map hf.aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro s hs
  rw [ProbabilityMeasure.toMeasure_map,Measure.map_apply hf hs,
    orbitAverage_apply hT n hn ν (hs.preimage hf),
    orbitAverage_apply hS n hn (ν.map hf.aemeasurable) hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [ProbabilityMeasure.toMeasure_map,Measure.map_apply hf (hs.preimage (hS.iterate i))]
  congr 1
  ext x
  exact Iff.of_eq (congrArg (fun y => y ∈ s) ((he.iterate_right i) x))

theorem integral_orbitAverage_twice {T S : X → X} (hT : Continuous T) (hS : Continuous S)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (ν : ProbabilityMeasure X) (f : X →ᵇ ℝ) :
    (∫ x, f x ∂(orbitAverage hT.measurable n hn (orbitAverage hS.measurable m hm ν) : Measure X)) =
      (n:ℝ)⁻¹ * (m:ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∫ x, f ((T^[i]) ((S^[j]) x)) ∂(ν:Measure X) := by
  rw [integral_orbitAverage hT]
  have hh (i : ℕ) :
      (∫ x, f ((T^[i]) x) ∂(orbitAverage hS.measurable m hm ν : Measure X)) =
      (m:ℝ)⁻¹ * ∑ j ∈ Finset.range m, ∫ x, f ((T^[i]) ((S^[j]) x)) ∂(ν:Measure X) :=
    integral_orbitAverage hS m hm ν (f.compContinuous ⟨T^[i],hT.iterate i⟩)
  simp_rw [hh]
  rw [← Finset.mul_sum]
  ring

theorem orbitAverage_commute [HasOuterApproxClosed X]
    {T S : X → X} (hT : Continuous T) (hS : Continuous S) (hcomm : Function.Commute T S)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (ν : ProbabilityMeasure X) :
    orbitAverage hT.measurable n hn (orbitAverage hS.measurable m hm ν) =
      orbitAverage hS.measurable m hm (orbitAverage hT.measurable n hn ν) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_orbitAverage_twice hT hS,integral_orbitAverage_twice hS hT]
  rw [mul_comm (n:ℝ)⁻¹ (m:ℝ)⁻¹]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  exact ae_of_all _ (fun x => congrArg f ((hcomm.iterate_iterate i j) x))

def tripleAverage {T S R : X → X} (hT : Measurable T) (hS : Measurable S) (hR : Measurable R)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) : ProbabilityMeasure X :=
  orbitAverage hT n hn (orbitAverage hS n hn (orbitAverage hR n hn ν))

theorem tripleAverage_limit_measurePreserving [HasOuterApproxClosed X]
    {J : Type*} {L : Filter J} [NeBot L]
    {T S R : X → X} (hT : Continuous T) (hS : Continuous S) (hR : Continuous R)
    (hTS : Function.Commute T S) (hTR : Function.Commute T R) (hSR : Function.Commute S R)
    (n : J → ℕ) (hn : ∀ j, 0 < n j) (hnlim : Tendsto n L atTop)
    (ν : J → ProbabilityMeasure X) {μ : ProbabilityMeasure X}
    (hμ : Tendsto (fun j => tripleAverage hT.measurable hS.measurable hR.measurable
      (n j) (hn j) (ν j)) L (𝓝 μ)) :
    MeasurePreserving T (μ:Measure X) (μ:Measure X) ∧
      MeasurePreserving S (μ:Measure X) (μ:Measure X) ∧
      MeasurePreserving R (μ:Measure X) (μ:Measure X) := by
  refine ⟨orbitAverage_limit_measurePreserving hT n hn hnlim _ hμ,?_,?_⟩
  · apply orbitAverage_limit_measurePreserving hS n hn hnlim
      (fun j => orbitAverage hT.measurable (n j) (hn j)
        (orbitAverage hR.measurable (n j) (hn j) (ν j)))
    convert hμ using 1
    funext j
    exact (orbitAverage_commute hT hS hTS _ _ _ _ _).symm
  · apply orbitAverage_limit_measurePreserving hR n hn hnlim
      (fun j => orbitAverage hT.measurable (n j) (hn j)
        (orbitAverage hS.measurable (n j) (hn j) (ν j)))
    convert hμ using 1
    funext j
    rw [tripleAverage,orbitAverage_commute hS hR hSR]
    exact (orbitAverage_commute hT hR hTR _ _ _ _ _).symm

theorem exists_invariant_tripleAverage_subseq
    [TopologicalSpace.MetrizableSpace X] [CompactSpace X]
    {T S R : X → X} (hT : Continuous T) (hS : Continuous S) (hR : Continuous R)
    (hTS : Function.Commute T S) (hTR : Function.Commute T R) (hSR : Function.Commute S R)
    (n : ℕ → ℕ) (hn : ∀ j, 0 < n j) (hnlim : Tendsto n atTop atTop)
    (ν : ℕ → ProbabilityMeasure X) :
    ∃ μ : ProbabilityMeasure X, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => tripleAverage hT.measurable hS.measurable hR.measurable
        (n (φ j)) (hn (φ j)) (ν (φ j))) atTop (𝓝 μ) ∧
      MeasurePreserving T (μ:Measure X) (μ:Measure X) ∧
      MeasurePreserving S (μ:Measure X) (μ:Measure X) ∧
      MeasurePreserving R (μ:Measure X) (μ:Measure X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨μ,φ,hφ,hlim⟩ := probability_exists_tendsto_subseq
    (fun j => tripleAverage hT.measurable hS.measurable hR.measurable (n j) (hn j) (ν j))
  exact ⟨μ,φ,hφ,hlim,tripleAverage_limit_measurePreserving hT hS hR hTS hTR hSR
    (n ∘ φ) (fun j => hn (φ j)) (hnlim.comp hφ.tendsto_atTop) (ν ∘ φ) hlim⟩

end ErgodicTheory.Entropy
