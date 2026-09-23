import VV.BBEKLocalDiagonalCovariance

/-! The actual selected expanding plaques line up exactly under one forward
diagonal step, so their local probabilities scale without a free cocycle. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal
namespace VV.BBEKSelectedDiagonal
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques
  BBEKExpandedPlaques BBEKLocalRootFamily BBEKSelectedPlaques
  BBEKLocalDiagonalCovariance BBEKEntropyExpansion BBEKGrowingGlue

theorem selectedChart_succ (c : ℕ → Chart) (index : X → ℕ)
    (t : ℝ) (n : ℕ) (q : X) :
    selectedChart c index t (n+1) (psi t 1 • q) =
      translateChart (selectedChart c index t n q) t 1 := by
  have he : ((psi t 1)⁻¹)^(n+1) • (psi t 1 • q) = ((psi t 1)⁻¹)^n • q := by
    rw [← mul_smul,pow_succ,mul_assoc,inv_mul_cancel,mul_one]
  simp only [selectedChart,he,expandedChart]

/-- Every selected-chart local covariance holds on a single conull set,
conditional only on the selected chart actually containing the point. -/
theorem ae_selectedMeasure_succ (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) (index : X → ℕ) (t : ℝ)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∀ᵐ q ∂μ, ∀ n : ℕ, q ∈ (selectedChart c index t n q).image →
      selectedMeasure μ c index t (n+1) (psi t 1 • q) =
        (selectedMeasure μ c index t n q).map (leafScaling t 1) := by
  have hall : ∀ᵐ q ∂μ, ∀ n k : ℕ, q ∈ (expandedChart (c k) t n).image →
      localMeasure μ (translateChart (expandedChart (c k) t n) t 1) (psi t 1 • q) =
        (localMeasure μ (expandedChart (c k) t n) q).map (leafScaling t 1) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact (ae_restrict_iff' (expandedChart (c k) t n).isOpen_image.measurableSet).mp
      (ae_localMeasure_translate μ _ t 1 hA)
  filter_upwards [hall] with q hq n hn
  unfold selectedMeasure
  rw [selectedChart_succ]
  exact hq n (index (((psi t 1)⁻¹)^n • q)) hn

theorem scaling_preimage_growingBall {t r : ℝ} (ht : Real.log 2 ≤ t) (n : ℕ) :
    (leafScaling t 1) ⁻¹' growingBall r (n+1) ⊆ growingBall r n := by
  intro u hu
  have hscale : (4 : ℝ)*‖u‖ ≤ ‖leafScaling t 1 u‖ := by
    simpa only [pow_one,Function.iterate_one] using expand_iterate_norm_lower ht u 1
  have hnorm : ‖leafScaling t 1 u‖ < (4 : ℝ)^(n+1)*r := by
    simpa only [growingBall,mem_preimage,mem_ball,dist_zero_right] using hu
  change dist u 0 < (4 : ℝ)^n*r
  rw [dist_zero_right]
  rw [pow_succ] at hnorm
  nlinarith

end VV.BBEKSelectedDiagonal
