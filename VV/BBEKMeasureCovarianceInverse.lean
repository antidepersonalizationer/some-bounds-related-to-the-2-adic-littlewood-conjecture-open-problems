import VV.BBEKRadonModification

/-! Inverting a genuine normalized projective covariance gives the contracting
time direction, with positive finite scalar, by exact measure algebra. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace VV.BBEKMeasureCovarianceInverse

variable {U Z : Type*} [MeasurableSpace U] [MeasurableSpace Z]

theorem inverse_normalized_covariance (ν ν' : Measure U) (σ : U ≃ᵐ U) (B : Set U)
    (hνB : ν B = 1)
    (he : ν' = ((ν.map σ) B)⁻¹ • ν.map σ)
    (hp : 0 < (ν.map σ) B) (hfinite : (ν.map σ) B ≠ ∞) :
    ν = ((ν'.map σ.symm) B)⁻¹ • ν'.map σ.symm ∧
      0 < (ν'.map σ.symm) B ∧ (ν'.map σ.symm) B ≠ ∞ := by
  let a := (ν.map σ) B
  have hmap : ν'.map σ.symm = a⁻¹ • ν := by
    rw [he,Measure.map_smul,Measure.map_map σ.symm.measurable σ.measurable,
      σ.symm_comp_self,Measure.map_id]
  have hmass : (ν'.map σ.symm) B = a⁻¹ := by
    rw [hmap,Measure.smul_apply,hνB]
    exact mul_one _
  refine ⟨?_,?_,?_⟩
  · rw [hmass,hmap,inv_inv,smul_smul,ENNReal.mul_inv_cancel hp.ne' hfinite,one_smul]
  · rw [hmass]
    exact ENNReal.inv_pos.mpr hfinite
  · rw [hmass]
    exact ENNReal.inv_ne_top.mpr hp.ne'

/-- The inverse transformation inherits normalized covariance on one conull
set; no inverse-time covariance premise is supplied. -/
theorem ae_inverse_normalized_covariance (μ : Measure Z) (T : Z ≃ᵐ Z)
    (hT : MeasurePreserving T μ μ) (η : Z → Measure U) (σ : U ≃ᵐ U) (B : Set U)
    (hnormal : ∀ᵐ z ∂μ, η z B = 1)
    (hcov : ∀ᵐ z ∂μ,
      η (T z) = (((η z).map σ) B)⁻¹ • (η z).map σ ∧
        0 < ((η z).map σ) B ∧ ((η z).map σ) B ≠ ∞) :
    ∀ᵐ z ∂μ,
      η (T.symm z) = (((η z).map σ.symm) B)⁻¹ • (η z).map σ.symm ∧
        0 < ((η z).map σ.symm) B ∧ ((η z).map σ.symm) B ≠ ∞ := by
  have hTi := hT.symm T
  filter_upwards [hTi.quasiMeasurePreserving.ae hnormal,
    hTi.quasiMeasurePreserving.ae hcov] with z hn hc
  rw [T.apply_symm_apply] at hc
  exact inverse_normalized_covariance (η (T.symm z)) (η z) σ B hn hc.1 hc.2.1 hc.2.2

end VV.BBEKMeasureCovarianceInverse
