import VV.BBEKLeafAtomDichotomy
import VV.BBEKOneRootUpper

/-!
# The atom dichotomy for the four actual coarse-root families

The families are constructed from the quotient measure, not supplied as
hypotheses. Canonical chart restrictions remain in IsConstructedRootFamily
or its upper-root counterpart. Recurrence proves that a central atom is
zero or the entire measure is unit Dirac. This does not infer nonatomicity
from positive entropy, or translation symmetry from nonatomicity.
-/
noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped Topology ENNReal
namespace VV.BBEKOneRootAtoms
open BBEKDynamics BBEKQuotient BBEKLeafwiseStabilizer BBEKLeafAtomDichotomy
open BBEKRootLeafKernel BBEKOneRootCovariance BBEKOneRootUpper BBEKRootWeyl
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

section General
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U]

/-- Reverse normalized covariance, using its positive finite denominator. -/
theorem inverse_covariance {μ : Measure X} [IsFiniteMeasure μ]
    (g : G) (hT : MeasurePreserving (fun q : X => g⁻¹ • q) μ μ)
    (η : X → Measure U) {r : ℝ} (σ : U ≃+ U)
    (hσ : Measurable σ) (hσi : Measurable σ.symm)
    (hcov : ∀ᵐ q ∂μ,
      η (g • q) = ((η q).map σ (ball 0 r))⁻¹ • (η q).map σ ∧
      0 < (η q).map σ (ball 0 r) ∧ (η q).map σ (ball 0 r) ≠ ∞) :
    ∀ᵐ q ∂μ, ∃ d : ℝ≥0∞,
      η (g⁻¹ • q) = d • Measure.map σ.symm (η q) := by
  filter_upwards [hT.quasiMeasurePreserving.ae hcov] with q hq
  let c := (η (g⁻¹ • q)).map σ (ball 0 r)
  have hc0 : c ≠ 0 := hq.2.1.ne'
  have hcf : c ≠ ∞ := hq.2.2
  have he : η q = c⁻¹ • Measure.map σ (η (g⁻¹ • q)) := by
    simpa only [smul_inv_smul] using hq.1
  refine ⟨c, ?_⟩
  rw [he, Measure.map_smul, Measure.map_map hσi hσ]
  have hfun : (σ.symm : U → U) ∘ σ = id := by
    funext u
    exact σ.symm_apply_apply u
  rw [hfun, Measure.map_id, smul_smul, ENNReal.mul_inv_cancel hc0 hcf, one_smul]
end General

section Scalar
variable {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]

theorem scalar_atom_dichotomy {μ : Measure X} [IsFiniteMeasure μ]
    (g : G) (hT : MeasurePreserving (fun q : X => g⁻¹ • q) μ μ)
    (η : X → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    {a : F} (ha : a ≠ 0) (hsmall : ‖a⁻¹‖ < 1)
    (hcov : ∀ᵐ q ∂μ,
      η (g • q) = ((η q).map (a * ·) (ball 0 r))⁻¹ • (η q).map (a * ·) ∧
      0 < (η q).map (a * ·) (ball 0 r) ∧ (η q).map (a * ·) (ball 0 r) ≠ ∞) :
    ∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0 := by
  let σ := rootDilation a ha
  have hs : Measurable σ := (continuous_const.mul continuous_id).measurable
  have hsi : Measurable σ.symm := (continuous_const.mul continuous_id).measurable
  have hnorm (u : F) : ‖σ.symm u‖ ≤ ‖u‖ := by
    change ‖a⁻¹ * u‖ ≤ ‖u‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg u) hsmall.le
  have hcontract (u : F) : Tendsto (fun n : ℕ => (σ.symm^[n]) u) atTop (𝓝 0) := by
    have he : σ.symm = rootDilation a⁻¹ (inv_ne_zero ha) := by
      apply AddEquiv.ext
      intro v
      rfl
    rw [he]
    exact rootDilation_contracts (inv_ne_zero ha) hsmall u
  exact ae_zero_atom_or_dirac hT η hη hr hnormal σ.symm hsi hnorm hcontract
    (inverse_covariance g hT η σ hs hsi hcov)
end Scalar

theorem real_inverse_scaling_norm_lt_one {t : ℝ} (ht : Real.log 2 ≤ t) :
    ‖(Real.exp (2*t))⁻¹‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.exp_pos _)), ← Real.exp_neg]
  apply Real.exp_lt_one_iff.mpr
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem padic_inverse_scaling_norm_lt_one :
    ‖((2 : Q2)^(-2*(1 : ℤ)))⁻¹‖ < 1 := by
  have he : ((2 : Q2)^(-2*(1 : ℤ)))⁻¹ = (2 : Q2)^2 := by norm_num
  rw [he, norm_pow]
  rw [show ‖(2 : Q2)‖ = (2 : ℝ)⁻¹ from padicNormE.norm_p]
  norm_num

/-- Actual real lower-root data, retaining the canonical chart restrictions. -/
theorem exists_real_lower_atom_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) := by
  obtain ⟨r, hr, η, hη, hgood, hcov, hcanonical⟩ :=
    exists_real_lower_covariant_data μ hK hμK ht hT
  refine ⟨r, hr, η, hη, hgood, hcanonical, ?_⟩
  exact scalar_atom_dichotomy (psi t 1) hT η hη hr
    (hgood.mono fun _ hq => hq.2.2.1) (Real.exp_ne_zero _)
    (real_inverse_scaling_norm_lt_one ht) hcov

/-- Actual 2-adic lower-root data and recurrence, not the joint two-root leaf. -/
theorem exists_padic_lower_atom_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) := by
  obtain ⟨r, hr, η, hη, hgood, hcov, hcanonical⟩ :=
    exists_padic_lower_covariant_data μ hK hμK ht hT
  refine ⟨r, hr, η, hη, hgood, hcanonical, ?_⟩
  exact scalar_atom_dichotomy (psi t 1) hT η hη hr
    (hgood.mono fun _ hq => hq.2.2.1) (zpow_ne_zero _ (by norm_num))
    padic_inverse_scaling_norm_lt_one hcov

section Upper
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]

theorem upperFamily_atom_dichotomy (μ : Measure X) (η : X → Measure U)
    (hatom : ∀ᵐ q ∂reflectedMeasure μ, η q {0} = 0 ∨ η q = Measure.dirac 0) :
    ∀ᵐ q ∂μ, upperFamily η q {0} = 0 ∨ upperFamily η q = Measure.dirac 0 := by
  have hp := ae_of_ae_map (continuous_const_smul W⁻¹).measurable.aemeasurable hatom
  filter_upwards [hp] with q hq
  rcases hq with hzero | hdirac
  · left
    change (η (W⁻¹ • q)).map (fun u => -u) {0} = 0
    rw [Measure.map_apply measurable_neg (measurableSet_singleton 0)]
    have he : (fun u : U => -u) ⁻¹' {0} = {0} := by ext u; simp
    rwa [he]
  · right
    change negateMeasure (η (W⁻¹ • q)) = _
    rw [hdirac, negateMeasure, Measure.map_dirac measurable_neg]
    simp
end Upper

theorem exists_real_upper_atom_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) := by
  obtain ⟨hK', hμK'⟩ := reflectedMeasure_compact_mass μ hK hμK
  obtain ⟨r, hr, η, hη, hgood, hcanonical, hatom⟩ := exists_real_lower_atom_data
    (reflectedMeasure μ) hK' hμK' ht (reflectedMeasure_inverse_invariant μ t 1 hA)
  exact ⟨r, hr, upperFamily η, measurable_upperFamily hη, upperFamily_properties μ η hgood,
    ⟨η, hcanonical, rfl⟩, upperFamily_atom_dichotomy μ η hatom⟩

theorem exists_padic_upper_atom_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) := by
  obtain ⟨hK', hμK'⟩ := reflectedMeasure_compact_mass μ hK hμK
  obtain ⟨r, hr, η, hη, hgood, hcanonical, hatom⟩ := exists_padic_lower_atom_data
    (reflectedMeasure μ) hK' hμK' ht (reflectedMeasure_inverse_invariant μ t 1 hA)
  exact ⟨r, hr, upperFamily η, measurable_upperFamily hη, upperFamily_properties μ η hgood,
    ⟨η, hcanonical, rfl⟩, upperFamily_atom_dichotomy μ η hatom⟩

end VV.BBEKOneRootAtoms
