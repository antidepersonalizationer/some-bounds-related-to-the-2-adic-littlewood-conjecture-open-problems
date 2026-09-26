import VV.BBEKLeafStabilizerDichotomy
import VV.BBEKLeafStabilizerEscape
import VV.BBEKRootContraction

/-!
# Trivial stabilizers of canonical root measures on a Mahler compact

Actual measurable canonical families have a bot/top stabilizer dichotomy by
one contracting diagonal time. The finite escape cover rules out top almost
everywhere. This proves trivial exact and projective stabilizers in all four
root branches without ergodicity or full-diagonal covariance of the leaf field.
The remaining low-entropy argument must contradict this conclusion by
producing a positive-measure set with a nonzero projective stabilizer.
-/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace VV.BBEKCompactLeafStabilizers
open BBEKDynamics BBEKQuotient BBEKOrbit BBEKDiagonal BBEKMautner
open BBEKLeafwiseStabilizer BBEKOneRootCovariance BBEKOneRootUpper BBEKRootLeafKernel
open BBEKOneRootAtoms BBEKOneRootRecurrence BBEKRootContraction
open BBEKLeafStabilizerDichotomy BBEKLeafStabilizerEscape

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩
/-- The actual canonical real_lower family has trivial exact and projective
translation stabilizers under full-diagonal invariance and compact support. -/
theorem exists_real_lower_trivial_stabilizer_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, translationStabilizer (η q) = ⊥ ∧
        projectiveTranslationStabilizer (η q) = ⊥) := by
  have hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ :=
    measurePreserving_smul (⟨(psi t 1)⁻¹,A.inv_mem (psi_mem_A t 1)⟩ : A) μ

  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_real_lower_covariant_data μ (BBEKMahler.compact_K hδ) hmass ht hT
  have hnorm := hgood.mono (fun _ hq => hq.2.2.1)
  have hcovNN := inverse_projective_covariance (psi t 1) hT η hnorm
    (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  have hdichotomy := ae_real_stabilizer_bot_or_top hT η hη
    (hgood.mono (fun _ hq => hq.2.1)) hnorm (a := (Real.exp (2*t))⁻¹)
      (inv_pos.mpr (Real.exp_pos _)) (by
        simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (Real.exp_pos _))] using
          real_inverse_scaling_norm_lt_one ht)
      (hcovNN.mono (fun _ hq => ⟨hq.choose,hq.choose_spec.2⟩))
  have hne := ae_real_lower_stabilizer_ne_top μ hδ hmass hr η hcanonical
    (hgood.mono (fun _ hq => hq.2.2.2))
  have hbot := ae_stabilizer_eq_bot_of_ne_top μ η hne hdichotomy
  have heq := scalar_projective_stabilizer_eq (psi t 1) hT η hη hr
    (hgood.mono (fun _ hq => hq.1)) hnorm (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  refine ⟨r,hr,η,hη,hgood,hcanonical,?_⟩
  filter_upwards [hbot,heq] with q hq heq
  exact ⟨hq,heq.trans hq⟩
/-- The actual canonical real_upper family has trivial exact and projective
translation stabilizers under full-diagonal invariance and compact support. -/
theorem exists_real_upper_trivial_stabilizer_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, translationStabilizer (η q) = ⊥ ∧
        projectiveTranslationStabilizer (η q) = ⊥) := by
  have hT : MeasurePreserving (fun q : X => psi t 1 • q) μ μ :=
    measurePreserving_smul (⟨psi t 1,psi_mem_A t 1⟩ : A) μ
  have hTi : MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ := by
    simpa only [inv_inv] using hT
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_real_upper_covariant_data μ (BBEKMahler.compact_K hδ) hmass ht hT
  have hnorm := hgood.mono (fun _ hq => hq.2.2.1)
  have hcovNN := inverse_projective_covariance ((psi t 1)⁻¹) hTi η hnorm
    (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  have hdichotomy := ae_real_stabilizer_bot_or_top hTi η hη
    (hgood.mono (fun _ hq => hq.2.1)) hnorm (a := (Real.exp (2*t))⁻¹)
      (inv_pos.mpr (Real.exp_pos _)) (by
        simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (Real.exp_pos _))] using
          real_inverse_scaling_norm_lt_one ht)
      (hcovNN.mono (fun _ hq => ⟨hq.choose,hq.choose_spec.2⟩))
  have hne := ae_real_upper_stabilizer_ne_top μ hδ hmass hr η hcanonical
    (hgood.mono (fun _ hq => hq.2.2.2))
  have hbot := ae_stabilizer_eq_bot_of_ne_top μ η hne hdichotomy
  have heq := scalar_projective_stabilizer_eq ((psi t 1)⁻¹) hTi η hη hr
    (hgood.mono (fun _ hq => hq.1)) hnorm (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  refine ⟨r,hr,η,hη,hgood,hcanonical,?_⟩
  filter_upwards [hbot,heq] with q hq heq
  exact ⟨hq,heq.trans hq⟩
/-- The actual canonical padic_lower family has trivial exact and projective
translation stabilizers under full-diagonal invariance and compact support. -/
theorem exists_padic_lower_trivial_stabilizer_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, translationStabilizer (η q) = ⊥ ∧
        projectiveTranslationStabilizer (η q) = ⊥) := by
  have hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ :=
    measurePreserving_smul (⟨(psi t 1)⁻¹,A.inv_mem (psi_mem_A t 1)⟩ : A) μ

  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_padic_lower_covariant_data μ (BBEKMahler.compact_K hδ) hmass ht hT
  have hnorm := hgood.mono (fun _ hq => hq.2.2.1)
  have hcovNN := inverse_projective_covariance (psi t 1) hT η hnorm
    (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  have hdichotomy := ae_padic_stabilizer_bot_or_top hT η hη
    (hgood.mono (fun _ hq => hq.2.1)) hnorm (a := ((2 : Q2)^(-2*(1 : ℤ)))⁻¹)
      (inv_ne_zero (zpow_ne_zero _ (by norm_num))) padic_inverse_scaling_norm_lt_one
      (hcovNN.mono (fun _ hq => ⟨hq.choose,hq.choose_spec.2⟩))
  have hne := ae_padic_lower_stabilizer_ne_top μ hδ hmass hr η hcanonical
    (hgood.mono (fun _ hq => hq.2.2.2))
  have hbot := ae_stabilizer_eq_bot_of_ne_top μ η hne hdichotomy
  have heq := scalar_projective_stabilizer_eq (psi t 1) hT η hη hr
    (hgood.mono (fun _ hq => hq.1)) hnorm (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  refine ⟨r,hr,η,hη,hgood,hcanonical,?_⟩
  filter_upwards [hbot,heq] with q hq heq
  exact ⟨hq,heq.trans hq⟩
/-- The actual canonical padic_upper family has trivial exact and projective
translation stabilizers under full-diagonal invariance and compact support. -/
theorem exists_padic_upper_trivial_stabilizer_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, translationStabilizer (η q) = ⊥ ∧
        projectiveTranslationStabilizer (η q) = ⊥) := by
  have hT : MeasurePreserving (fun q : X => psi t 1 • q) μ μ :=
    measurePreserving_smul (⟨psi t 1,psi_mem_A t 1⟩ : A) μ
  have hTi : MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ := by
    simpa only [inv_inv] using hT
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_padic_upper_covariant_data μ (BBEKMahler.compact_K hδ) hmass ht hT
  have hnorm := hgood.mono (fun _ hq => hq.2.2.1)
  have hcovNN := inverse_projective_covariance ((psi t 1)⁻¹) hTi η hnorm
    (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  have hdichotomy := ae_padic_stabilizer_bot_or_top hTi η hη
    (hgood.mono (fun _ hq => hq.2.1)) hnorm (a := ((2 : Q2)^(-2*(1 : ℤ)))⁻¹)
      (inv_ne_zero (zpow_ne_zero _ (by norm_num))) padic_inverse_scaling_norm_lt_one
      (hcovNN.mono (fun _ hq => ⟨hq.choose,hq.choose_spec.2⟩))
  have hne := ae_padic_upper_stabilizer_ne_top μ hδ hmass hr η hcanonical
    (hgood.mono (fun _ hq => hq.2.2.2))
  have hbot := ae_stabilizer_eq_bot_of_ne_top μ η hne hdichotomy
  have heq := scalar_projective_stabilizer_eq ((psi t 1)⁻¹) hTi η hη hr
    (hgood.mono (fun _ hq => hq.1)) hnorm (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  refine ⟨r,hr,η,hη,hgood,hcanonical,?_⟩
  filter_upwards [hbot,heq] with q hq heq
  exact ⟨hq,heq.trans hq⟩

end VV.BBEKCompactLeafStabilizers
