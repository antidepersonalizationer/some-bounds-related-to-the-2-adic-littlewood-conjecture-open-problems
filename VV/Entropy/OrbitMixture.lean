import VV.Entropy.MixtureEntropy
import VV.Entropy.OrbitAverage
import VV.Entropy.EmbeddingEntropy
import VV.Entropy.CommutingAverage

/-! Actual Cesàro averages as finite mixtures, and entropy under commuting embeddings. -/
noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology ENNReal NNReal
namespace ErgodicTheory.Entropy
variable {X : Type*} [MeasurableSpace X]

theorem uniformWeight_sum (n : ℕ) (hn : 0 < n) :
    ∑ _ : Fin n, (n : ℝ≥0)⁻¹ = 1 := by
  simp [nsmul_eq_mul, Nat.ne_of_gt hn]

/-- Equality of the genuine Cesàro measure with a finite convex combination. -/
theorem orbitAverage_eq_mixture {S : X → X} (hS : Measurable S)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) :
    orbitAverage hS n hn ν = probabilityMixture (fun _ : Fin n => (n : ℝ≥0)⁻¹)
      (uniformWeight_sum n hn) (fun i => ν.map (hS.iterate i.val).aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro s hs
  rw [orbitAverage_apply hS n hn ν hs, probabilityMixture_coe, mixtureMeasure_apply]
  simp only [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (hS.iterate _) hs, ENNReal.coe_inv, ENNReal.coe_natCast,
    ← Finset.mul_sum, Fin.sum_univ_eq_sum_range]
  congr 1
  · rw [ENNReal.coe_inv (Nat.cast_ne_zero.mpr hn.ne'), ENNReal.coe_natCast]
  · exact (Fin.sum_univ_eq_sum_range (fun i => (ν : Measure X) ((S^[i]) ⁻¹' s)) n).symm

/-- A commuting measurable map transports an invariant probability to an invariant probability. -/
theorem measurePreserving_map_commute {T S : X → X} (ν : ProbabilityMeasure X)
    (hT : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (hS : Measurable S) (hcomm : Function.Commute S T) :
    MeasurePreserving T (ν.map hS.aemeasurable : Measure X)
      (ν.map hS.aemeasurable : Measure X) := by
  refine ⟨hT.measurable, ?_⟩
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_map hT.measurable hS,
    ← hcomm.comp_eq, ← Measure.map_map hS hT.measurable, hT.map_eq]

/-- A commuting measurable embedding preserves full system entropy under pushforward. -/
theorem ksEntropy_map_commuting_embedding {T S : X → X} (ν : ProbabilityMeasure X)
    (hT : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (hS : MeasurableEmbedding S) (hcomm : Function.Commute S T) :
    ksEntropy (measurePreserving_map_commute ν hT hS.measurable hcomm) = ksEntropy hT := by
  apply (ksEntropy_eq_of_embedding hT
    (measurePreserving_map_commute ν hT hS.measurable hcomm) hS
    ⟨hS.measurable, rfl⟩ hcomm.comp_eq).symm

theorem measurableEmbedding_iterate {S : X → X} (hS : MeasurableEmbedding S) (n : ℕ) :
    MeasurableEmbedding (S^[n]) := by
  induction n with
  | zero => simpa using MeasurableEmbedding.id
  | succ n ih => simpa only [Function.iterate_succ] using ih.comp hS

theorem ksEntropy_eq_of_probability_eq {T : X → X} {μ ν : ProbabilityMeasure X}
    (he : μ = ν) (hμ : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (hν : MeasurePreserving T (ν : Measure X) (ν : Measure X)) :
    ksEntropy hμ = ksEntropy hν := by
  subst ν
  rfl

/-- Every commuting embedding orbit average is invariant under the original dynamics. -/
theorem orbitAverage_measurePreserving {T S : X → X} (ν : ProbabilityMeasure X)
    (hT : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (hS : Measurable S) (hcomm : Function.Commute S T) (n : ℕ) (hn : 0 < n) :
    MeasurePreserving T (orbitAverage hS n hn ν : Measure X) (orbitAverage hS n hn ν : Measure X) := by
  rw [orbitAverage_eq_mixture]
  exact probabilityMixture_measurePreserving _ _ _ hT.measurable
    (fun i => measurePreserving_map_commute ν hT (hS.iterate i.val)
      (hcomm.iterate_left i.val))

/-- Commuting embedding averages retain every real lower bound on full KS entropy. -/
theorem ksEntropy_orbitAverage_ge {T S : X → X} (ν : ProbabilityMeasure X)
    (hT : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (hS : MeasurableEmbedding S) (hcomm : Function.Commute S T)
    (n : ℕ) (hn : 0 < n) {c : ℝ} (hc : (c : EReal) ≤ ksEntropy hT) :
    (c : EReal) ≤ ksEntropy (orbitAverage_measurePreserving ν hT hS.measurable hcomm n hn) := by
  let μ : Fin n → ProbabilityMeasure X := fun i => ν.map (hS.measurable.iterate i.val).aemeasurable
  let hμ : ∀ i, MeasurePreserving T (μ i : Measure X) (μ i : Measure X) := fun i =>
    measurePreserving_map_commute ν hT (hS.measurable.iterate i.val) (hcomm.iterate_left i.val)
  let hm := probabilityMixture_measurePreserving (fun _ : Fin n => (n : ℝ≥0)⁻¹)
    (uniformWeight_sum n hn) μ hT.measurable hμ
  rw [ksEntropy_eq_of_probability_eq (orbitAverage_eq_mixture hS.measurable n hn ν) _ hm]
  apply ksEntropy_mixture_ge _ _ _ hT.measurable hμ
  intro i
  exact hc.trans_eq (ksEntropy_map_commuting_embedding ν hT
    (measurableEmbedding_iterate hS i.val) (hcomm.iterate_left i.val)).symm

/-- Commuting embedding orbit averages preserve full KS entropy, including `+∞`. -/
theorem ksEntropy_orbitAverage_eq {T S : X → X} (ν : ProbabilityMeasure X)
    (hT : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (hS : MeasurableEmbedding S) (hcomm : Function.Commute S T) (n : ℕ) (hn : 0 < n) :
    ksEntropy (orbitAverage_measurePreserving ν hT hS.measurable hcomm n hn) = ksEntropy hT := by
  apply le_antisymm
  · by_cases htop : ksEntropy hT = ⊤
    · simp only [htop, le_top]
    have hbot : ksEntropy hT ≠ ⊥ := ne_of_gt
      (lt_of_lt_of_le EReal.bot_lt_zero (ksEntropy_nonneg hT))
    have ha := EReal.coe_toReal htop hbot
    let μ : Fin n → ProbabilityMeasure X := fun i => ν.map (hS.measurable.iterate i.val).aemeasurable
    let hμ : ∀ i, MeasurePreserving T (μ i : Measure X) (μ i : Measure X) := fun i =>
      measurePreserving_map_commute ν hT (hS.measurable.iterate i.val) (hcomm.iterate_left i.val)
    let hm := probabilityMixture_measurePreserving (fun _ : Fin n => (n : ℝ≥0)⁻¹)
      (uniformWeight_sum n hn) μ hT.measurable hμ
    rw [ksEntropy_eq_of_probability_eq (orbitAverage_eq_mixture hS.measurable n hn ν) _ hm]
    have hbound := ksEntropy_mixture_le_weighted (fun _ : Fin n => (n : ℝ≥0)⁻¹)
      (uniformWeight_sum n hn) μ hT.measurable hμ (fun _ => (ksEntropy hT).toReal)
      (fun i => (ksEntropy_map_commuting_embedding ν hT (measurableEmbedding_iterate hS i.val)
        (hcomm.iterate_left i.val)).le.trans ha.ge)
    have hw := congrArg (fun x : ℝ≥0 => (x : ℝ)) (uniformWeight_sum n hn)
    simp only [NNReal.coe_sum, NNReal.coe_one] at hw
    simpa only [← Finset.sum_mul, hw, one_mul, ha] using hbound
  · by_contra hnot
    obtain ⟨c, hc, hcT⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
    exact (not_le_of_gt hc) (ksEntropy_orbitAverage_ge ν hT hS hcomm n hn hcT.le)

section Triple
variable [TopologicalSpace X] [BorelSpace X]

theorem tripleAverage_measurePreserving {T A B C : X → X} (ν : ProbabilityMeasure X)
    (hT : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (hAT : Function.Commute A T) (hBT : Function.Commute B T) (hCT : Function.Commute C T)
    (n : ℕ) (hn : 0 < n) :
    MeasurePreserving T (tripleAverage hA hB hC n hn ν : Measure X)
      (tripleAverage hA hB hC n hn ν : Measure X) :=
  orbitAverage_measurePreserving _
    (orbitAverage_measurePreserving _ (orbitAverage_measurePreserving ν hT hC hCT n hn)
      hB hBT n hn) hA hAT n hn

/-- The actual three-direction finite cube average also preserves full KS entropy. -/
theorem ksEntropy_tripleAverage_eq {T A B C : X → X} (ν : ProbabilityMeasure X)
    (hT : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (hA : MeasurableEmbedding A) (hB : MeasurableEmbedding B) (hC : MeasurableEmbedding C)
    (hAT : Function.Commute A T) (hBT : Function.Commute B T) (hCT : Function.Commute C T)
    (n : ℕ) (hn : 0 < n) :
    ksEntropy (tripleAverage_measurePreserving ν hT hA.measurable hB.measurable hC.measurable
      hAT hBT hCT n hn) = ksEntropy hT := by
  let νC := orbitAverage hC.measurable n hn ν
  let hνC := orbitAverage_measurePreserving ν hT hC.measurable hCT n hn
  let νB := orbitAverage hB.measurable n hn νC
  let hνB := orbitAverage_measurePreserving νC hνC hB.measurable hBT n hn
  calc
    _ = ksEntropy hνB := ksEntropy_orbitAverage_eq νB hνB hA hAT n hn
    _ = ksEntropy hνC := ksEntropy_orbitAverage_eq νC hνC hB hBT n hn
    _ = ksEntropy hT := ksEntropy_orbitAverage_eq ν hT hC hCT n hn

end Triple

end ErgodicTheory.Entropy
