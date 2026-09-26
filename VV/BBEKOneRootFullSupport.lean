import VV.BBEKLeafSupportGeneration
import VV.BBEKOneRootAtoms

/-! Full support-generation and infinite mass for the four actual canonical
one-root families on their non-Dirac part. Their construction is retained;
no entropy-to-non-Dirac implication or low-entropy dichotomy is assumed. -/
noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped Topology ENNReal
namespace VV.BBEKOneRootFullSupport
open BBEKDynamics BBEKQuotient BBEKLeafwiseStabilizer BBEKLeafAtomDichotomy
open BBEKRootLeafKernel BBEKOneRootCovariance BBEKOneRootUpper BBEKOneRootAtoms
open BBEKLeafSupportGeneration
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The non-Dirac measure is infinite and not carried by a proper closed
additive subgroup. This is a conclusion about support, not invariance. -/
def NonDiracRootSupport {F : Type*} [NormedField F] [MeasurableSpace F]
    (η : Measure F) : Prop :=
  η ≠ Measure.dirac 0 → η univ = ∞ ∧
    ∀ S : AddSubgroup F, IsClosed (S : Set F) → (∀ᵐ u ∂η, u ∈ S) → S = ⊤

section Scalar
variable {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
theorem scalar_nonDirac_infinite {μ : Measure X} [IsFiniteMeasure μ]
    (g : G) (hT : MeasurePreserving (fun q : X => g⁻¹ • q) μ μ)
    (η : X → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    {a : F} (ha : a ≠ 0) (hsmall : ‖a⁻¹‖ < 1)
    (hcov : ∀ᵐ q ∂μ,
      η (g • q) = ((η q).map (a * ·) (ball 0 r))⁻¹ • (η q).map (a * ·) ∧
      0 < (η q).map (a * ·) (ball 0 r) ∧ (η q).map (a * ·) (ball 0 r) ≠ ∞) :
    ∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → η q univ = ∞ := by
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
  have hh := ae_finite_implies_dirac hT η hη hr hnormal σ.symm hsi hnorm hcontract
    (inverse_covariance g hT η σ hs hsi hcov)
  filter_upwards [hh] with q hq hn
  by_contra hf
  exact hn (hq hf)
end Scalar

theorem real_support_of_infinite_and_atoms {μ : Measure X}
    (η : X → Measure ℝ)
    (hinf : ∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → η q univ = ∞)
    (hatoms : ∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0)
    (hpos : ∀ᵐ q ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) :
    ∀ᵐ q ∂μ, NonDiracRootSupport (η q) := by
  filter_upwards [hinf,hatoms,hpos] with q hi ha hp hn
  exact ⟨hi hn,fun S hS hs =>
    real_supported_subgroup_eq_top (η q) hp (ha.resolve_right hn) S hS hs⟩

theorem padic_support_of_infinite {μ : Measure X}
    (η : X → Measure Q2)
    (hinf : ∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → η q univ = ∞)
    (hfinite : ∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q)) :
    ∀ᵐ q ∂μ, NonDiracRootSupport (η q) := by
  filter_upwards [hinf,hfinite] with q hi hf hn
  letI := hf
  refine ⟨hi hn,fun S hS hs => ?_⟩
  by_contra hproper
  exact padic_finite_of_supported_proper (η q) S hS hproper hs (hi hn)
/-- Actual canonical real_lower data, with the full-root support threshold proved. -/
theorem exists_real_lower_full_support_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, NonDiracRootSupport (η q)) := by
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_real_lower_covariant_data μ hK hμK ht hT
  have hi := scalar_nonDirac_infinite (psi t 1) hT η hη hr
    (hgood.mono fun _ hq => hq.2.2.1) (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  refine ⟨r,hr,η,hη,hgood,hcanonical,?_⟩
  exact real_support_of_infinite_and_atoms η hi
    (scalar_atom_dichotomy (psi t 1) hT η hη hr (hgood.mono fun _ hq => hq.2.2.1)
      (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov)
    (hgood.mono fun _ hq => hq.2.2.2)
/-- Actual canonical padic_lower data, with the full-root support threshold proved. -/
theorem exists_padic_lower_full_support_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, NonDiracRootSupport (η q)) := by
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_padic_lower_covariant_data μ hK hμK ht hT
  have hi := scalar_nonDirac_infinite (psi t 1) hT η hη hr
    (hgood.mono fun _ hq => hq.2.2.1) (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  refine ⟨r,hr,η,hη,hgood,hcanonical,?_⟩
  exact padic_support_of_infinite η hi (hgood.mono fun _ hq => hq.1)
/-- Actual canonical real_upper data, with the full-root support threshold proved. -/
theorem exists_real_upper_full_support_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, NonDiracRootSupport (η q)) := by
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_real_upper_covariant_data μ hK hμK ht hT
  have hTi : MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ := by
    simpa only [inv_inv] using hT
  have hi := scalar_nonDirac_infinite ((psi t 1)⁻¹) hTi η hη hr
    (hgood.mono fun _ hq => hq.2.2.1) (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  refine ⟨r,hr,η,hη,hgood,hcanonical,?_⟩
  exact real_support_of_infinite_and_atoms η hi
    (scalar_atom_dichotomy ((psi t 1)⁻¹) hTi η hη hr (hgood.mono fun _ hq => hq.2.2.1)
      (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov)
    (hgood.mono fun _ hq => hq.2.2.2)
/-- Actual canonical padic_upper data, with the full-root support threshold proved. -/
theorem exists_padic_upper_full_support_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, NonDiracRootSupport (η q)) := by
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_padic_upper_covariant_data μ hK hμK ht hT
  have hTi : MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ := by
    simpa only [inv_inv] using hT
  have hi := scalar_nonDirac_infinite ((psi t 1)⁻¹) hTi η hη hr
    (hgood.mono fun _ hq => hq.2.2.1) (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  refine ⟨r,hr,η,hη,hgood,hcanonical,?_⟩
  exact padic_support_of_infinite η hi (hgood.mono fun _ hq => hq.1)
end VV.BBEKOneRootFullSupport
