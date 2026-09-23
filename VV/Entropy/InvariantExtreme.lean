import VV.Entropy.ProbabilityMoments
import VV.Entropy.BinaryMixture
import Mathlib.Probability.ConditionalProbability

/-! Extremality in the real vector space of moments implies joint ergodicity
for a family of maps, by an explicit conditional-probability decomposition. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace ErgodicTheory.Entropy
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem probabilityMoments_binaryMixture (a b : ℝ≥0) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure X) :
    probabilityMoments (binaryMixture a b hab μ ν) =
      (a : ℝ) • probabilityMoments μ + (b : ℝ) • probabilityMoments ν := by
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    using probabilityMoments_mixture ![a,b]
      (by simpa only [Fin.sum_univ_two] using hab) ![μ,ν]

theorem aeconst_of_extreme_invariantMoments (F : I → X → X)
    (μ : ProbabilityMeasure X)
    (he : probabilityMoments μ ∈
      extremePoints ℝ (probabilityMoments '' invariantProbabilities F))
    {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ i, (F i) ⁻¹' s =ᵐ[(μ : Measure X)] s) :
    EventuallyConst s (ae (μ : Measure X)) := by
  classical
  have hμ : μ ∈ invariantProbabilities F := by
    obtain ⟨ν,hν,heq⟩ := he.1
    exact probabilityMoments_injective heq ▸ hν
  by_contra hnot
  obtain ⟨hs0,hsc0⟩ : (μ : Measure X) s ≠ 0 ∧ (μ : Measure X) sᶜ ≠ 0 := by
    simpa [eventuallyConst_set,ae_iff,and_comm] using hnot
  let ν : ProbabilityMeasure X := ⟨(μ : Measure X)[|s],cond_isProbabilityMeasure hs0⟩
  let ξ : ProbabilityMeasure X := ⟨(μ : Measure X)[|sᶜ],cond_isProbabilityMeasure hsc0⟩
  have hcond {u : Set X} (hu : MeasurableSet u)
      (huinv : ∀ i, (F i) ⁻¹' u =ᵐ[(μ : Measure X)] u) (i : I) :
      MeasurePreserving (F i) ((μ : Measure X)[|u]) ((μ : Measure X)[|u]) := by
    have hr := (hμ i).restrict_preimage hu
    rw [Measure.restrict_congr_set (huinv i)] at hr
    exact hr.smul_measure ((μ : Measure X) u)⁻¹
  have hν : ν ∈ invariantProbabilities F := hcond hs hinv
  have hξ : ξ ∈ invariantProbabilities F :=
    hcond hs.compl (fun i => by simpa only [preimage_compl] using (hinv i).compl)
  let a : ℝ≥0 := ((μ : Measure X) s).toNNReal
  let b : ℝ≥0 := ((μ : Measure X) sᶜ).toNNReal
  have hab : a + b = 1 := by
    dsimp [a,b]
    rw [← ENNReal.toNNReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hs,measure_univ,ENNReal.toNNReal_one]
  have ha : (0 : ℝ) < a := by
    exact ENNReal.toReal_pos hs0 (measure_ne_top _ _)
  have hb : (0 : ℝ) < b := by
    exact ENNReal.toReal_pos hsc0 (measure_ne_top _ _)
  have hmix : binaryMixture a b hab ν ξ = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [binaryMixture_coe]
    change (a : ℝ≥0∞) • ((μ : Measure X)[|s]) +
      (b : ℝ≥0∞) • ((μ : Measure X)[|sᶜ]) = (μ : Measure X)
    simp [a,b,ENNReal.coe_toNNReal,measure_ne_top,ProbabilityTheory.cond,
      smul_smul,ENNReal.mul_inv_cancel hs0 (measure_ne_top _ _),
      ENNReal.mul_inv_cancel hsc0 (measure_ne_top _ _),
      Measure.restrict_add_restrict_compl hs]
  have hνμ : ν = μ := by
    apply probabilityMoments_injective
    apply (he.2 ⟨ν,hν,rfl⟩ ⟨ξ,hξ,rfl⟩ ?_).1
    refine ⟨(a : ℝ),(b : ℝ),ha,hb,by exact_mod_cast hab,?_⟩
    rw [← probabilityMoments_binaryMixture a b hab ν ξ,hmix]
  have hc : (ν : Measure X) sᶜ = 0 := by
    change ((μ : Measure X)[|s]) sᶜ = 0
    simp [cond_apply hs]
  rw [hνμ] at hc
  exact hsc0 hc

end ErgodicTheory.Entropy
