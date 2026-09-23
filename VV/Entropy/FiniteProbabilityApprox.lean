import VV.Entropy.SmallPartition
import VV.Entropy.MixtureEntropy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Finite quantizations of an actual probability measure, converging weakly.
The representatives and weights are constructed from small Borel partitions. -/

noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology ENNReal NNReal

namespace ErgodicTheory.Entropy
variable {X I : Type*} [MeasurableSpace X] [Fintype I]

def FixedPartition.index (P : FixedPartition X I) (x : X) : I :=
  Classical.choose (show ∃ i, x ∈ P.cells i from mem_iUnion.mp (P.cover ▸ mem_univ x))

theorem FixedPartition.mem_index (P : FixedPartition X I) (x : X) :
    x ∈ P.cells (P.index x) :=
  Classical.choose_spec (show ∃ i, x ∈ P.cells i from mem_iUnion.mp (P.cover ▸ mem_univ x))

theorem FixedPartition.index_eq_iff (P : FixedPartition X I) (x : X) (i : I) :
    P.index x = i ↔ x ∈ P.cells i := by
  constructor
  · intro h; simpa only [h] using P.mem_index x
  · intro h
    by_contra hn
    exact Set.disjoint_left.mp (P.disjoint hn) (P.mem_index x) h

theorem FixedPartition.measurable_index (P : FixedPartition X I) :
    @Measurable X I _ ⊤ P.index := by
  classical
  letI : MeasurableSpace I := ⊤
  apply measurable_to_countable'
  intro i
  have he : P.index ⁻¹' {i} = P.cells i := by
    ext x; exact P.index_eq_iff x i
  rw [he]
  exact P.measurable i

def FixedPartition.quantize (P : FixedPartition X I) (p : I → X) (x : X) : X :=
  p (P.index x)

theorem FixedPartition.measurable_quantize (P : FixedPartition X I) (p : I → X) :
    Measurable (P.quantize p) := by
  letI : MeasurableSpace I := ⊤
  exact (measurable_of_countable p).comp P.measurable_index

def FixedPartition.weight (P : FixedPartition X I) (μ : ProbabilityMeasure X) (i : I) : ℝ≥0 :=
  ((μ : Measure X) (P.cells i)).toNNReal

theorem FixedPartition.weight_sum (P : FixedPartition X I) (μ : ProbabilityMeasure X) :
    ∑ i, P.weight μ i = 1 := by
  apply NNReal.coe_injective
  simpa only [NNReal.coe_sum, weight, ENNReal.coe_toNNReal, NNReal.coe_one] using
    (P.toMeasurePartition (μ : Measure X)).sum_toReal_measure_eq_one

theorem FixedPartition.map_quantize (P : FixedPartition X I) (p : I → X)
    (μ : ProbabilityMeasure X) :
    Measure.map (P.quantize p) (μ : Measure X) =
      ∑ i, (P.weight μ i : ℝ≥0∞) • Measure.dirac (p i) := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (P.measurable_quantize p) hs,
    (P.toMeasurePartition (μ : Measure X)).measure_eq_sum_inter
      (hs.preimage (P.measurable_quantize p)), Measure.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (P.quantize p ⁻¹' s) ∩ P.cells i = if p i ∈ s then P.cells i else ∅ := by
    ext x
    by_cases hx : x ∈ P.cells i
    · have hindex := (P.index_eq_iff x i).mpr hx
      simp [quantize, hindex, hx]
    · simp [hx]
  change (μ : Measure X) ((P.quantize p ⁻¹' s) ∩ P.cells i) = _
  rw [he, Measure.smul_apply, Measure.dirac_apply' _ hs]
  by_cases hi : p i ∈ s <;>
    simp [hi, weight, ENNReal.coe_toNNReal, measure_ne_top]

section Metric
variable [MetricSpace X] [BorelSpace X] [CompactSpace X]

/-- The data are actual finite partitions and representatives, including a
pointwise-convergent quantization of every point of the compact space. -/
theorem exists_finite_quantizations (μ : ProbabilityMeasure X) :
    ∃ m : ℕ → ℕ, ∃ P : ∀ n, FixedPartition X (Fin (m n)),
      ∃ p : ∀ n, Fin (m n) → X,
      ∀ x, Tendsto (fun n => (P n).quantize (p n) x) atTop (𝓝 x) := by
  classical
  have hn (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose m P hboundary hmesh using
    fun n => exists_small_null_frontier_partition (μ : Measure X) (hn n)
  let p (n : ℕ) (i : Fin (m n)) : X :=
    if hi : (P n).cells i |>.Nonempty then hi.choose else μ.nonempty.some
  refine ⟨m,P,p,?_⟩
  intro x
  have hdist (n : ℕ) : dist ((P n).quantize (p n) x) x < 1 / ((n : ℝ) + 1) := by
    have hx := (P n).mem_index x
    have hi : ((P n).cells ((P n).index x)).Nonempty := ⟨x,hx⟩
    exact hmesh n _ _ (by simpa [FixedPartition.quantize,p,hi] using hi.choose_spec) x hx
  rw [Metric.tendsto_atTop]
  intro ε hε
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 1)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.1 ht).2 ε hε)
  exact ⟨N,fun n hn => (hdist n).trans (hN n hn)⟩

end Metric

section Weak
variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]

/-- Bounded dominated convergence turns pointwise convergence of measurable
maps into weak convergence of their pushforward probabilities. -/
theorem probability_map_tendsto_of_pointwise
    (μ : ProbabilityMeasure X) {f : ℕ → X → Y} {g : X → Y}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => μ.map (hf n).aemeasurable) atTop (𝓝 (μ.map hg.aemeasurable)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  simp only [ProbabilityMeasure.toMeasure_map,
    integral_map (hf _).aemeasurable φ.continuous.aestronglyMeasurable,
    integral_map hg.aemeasurable φ.continuous.aestronglyMeasurable]
  exact tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
    (fun n => (φ.continuous.measurable.comp (hf n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun x => φ.norm_coe_le_norm _)
    (Filter.Eventually.of_forall fun x => φ.continuous.continuousAt.tendsto.comp (hlim x))

end Weak
end ErgodicTheory.Entropy
