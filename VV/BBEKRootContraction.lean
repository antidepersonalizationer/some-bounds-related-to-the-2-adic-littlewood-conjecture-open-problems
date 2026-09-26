import VV.BBEKOneRootRecurrence

/-! The normalized expanding covariance of the actual canonical root
families supplies a finite, positive projective covariance for the inverse
contracting time. The reference radius is retained unchanged. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology
namespace VV.BBEKRootContraction
open BBEKDynamics BBEKQuotient BBEKLeafwiseStabilizer BBEKOneRootAtoms
  BBEKLeafAtomDichotomy

variable {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]

theorem inverse_projective_covariance
    {μ : Measure X} [IsFiniteMeasure μ]
    (g : G) (hT : MeasurePreserving (fun q : X => g⁻¹ • q) μ μ)
    (η : X → Measure F) {r : ℝ}
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    {a : F} (ha : a ≠ 0) (hsmall : ‖a⁻¹‖ < 1)
    (hcov : ∀ᵐ q ∂μ,
      η (g • q) = ((η q).map (a * ·) (ball 0 r))⁻¹ • (η q).map (a * ·) ∧
      0 < (η q).map (a * ·) (ball 0 r) ∧ (η q).map (a * ·) (ball 0 r) ≠ ∞) :
    ∀ᵐ q ∂μ, ∃ d : ℝ≥0, d ≠ 0 ∧
      η (g⁻¹ • q) = d • Measure.map (a⁻¹ * ·) (η q) := by
  let σ := rootDilation a ha
  have hs : Measurable σ := (continuous_const.mul continuous_id).measurable
  have hsi : Measurable σ.symm := (continuous_const.mul continuous_id).measurable
  have hnorm (u : F) : ‖σ.symm u‖ ≤ ‖u‖ := by
    change ‖a⁻¹ * u‖ ≤ ‖u‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg u) hsmall.le
  filter_upwards [inverse_covariance g hT η σ hs hsi hcov, hnormal,
    hT.quasiMeasurePreserving.ae hnormal] with q hq hn hnT
  obtain ⟨d,hd⟩ := hq
  have hdle := normalization_scalar_le_one (η q) (η (g⁻¹ • q)) hn hnT
    σ.symm hsi hnorm hd
  have hdf : d ≠ ∞ := ne_of_lt (hdle.trans_lt ENNReal.one_lt_top)
  have hd0 : d ≠ 0 := by
    intro hz
    rw [hz,zero_smul] at hd
    rw [hd] at hnT
    exact zero_ne_one hnT
  refine ⟨d.toNNReal, ENNReal.toNNReal_ne_zero.mpr ⟨hd0,hdf⟩, ?_⟩
  simpa only [ENNReal.smul_def,ENNReal.coe_toNNReal hdf] using hd

end VV.BBEKRootContraction
