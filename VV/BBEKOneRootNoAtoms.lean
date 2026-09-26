import VV.BBEKOneRootTranslation
import VV.BBEKOneRootFullSupport
import VV.BBEKKernelAtoms

/-! Genuine absence of atoms for non-Dirac canonical one-root leaves.
Translation covariance transports the central-atom dichotomy to leaf-almost
 every point. Infinite mass on the non-Dirac part rules out a translated Dirac.
This proves NoAtoms, not merely zero mass at the origin. -/
noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped Topology ENNReal
namespace VV.BBEKOneRootNoAtoms
open BBEKDynamics BBEKQuotient BBEKLeafwiseStabilizer BBEKRootLeafKernel
open BBEKOneRootTranslation BBEKOneRootCovariance BBEKOneRootUpper
open BBEKOneRootAtoms BBEKOneRootFullSupport BBEKRootWeyl
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

section General
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

/-- Translation of a measure shifts its atom at u to the origin. -/
theorem translate_neg_singleton_zero (ν : Measure U) (u : U) :
    translate (-u) ν {0} = ν {u} := by
  rw [translate_apply _ _ (measurableSet_singleton 0)]
  congr 1
  ext v
  simp

/-- A pointwise measure argument; its almost-everywhere hypotheses below will
come from the actual canonical disintegration and recurrence. -/
theorem noAtoms_of_infinite_translation_dichotomy
    (ν : Measure U) (hinf : ν univ = ∞) (ρ : U → Measure U) (r : ℝ)
    (hcov : ∀ᵐ u ∂ν,
      ρ u = ((translate (-u) ν) (ball 0 r))⁻¹ • translate (-u) ν ∧
      0 < (translate (-u) ν) (ball 0 r) ∧ (translate (-u) ν) (ball 0 r) ≠ ∞)
    (hatom : ∀ᵐ u ∂ν, ρ u {0} = 0 ∨ ρ u = Measure.dirac 0) : NoAtoms ν := by
  apply BBEKKernelAtoms.noAtoms_of_ae_singleton_zero ν
  filter_upwards [hcov,hatom] with u hc ha
  let c := translate (-u) ν (ball 0 r)
  have hc0 : c ≠ 0 := hc.2.1.ne'
  have hcf : c ≠ ∞ := hc.2.2
  have hci0 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hcf
  have htrans : translate (-u) ν univ = ∞ := by
    rw [translate_apply _ _ MeasurableSet.univ,preimage_univ,hinf]
  rcases ha with ha | ha
  · have hz : c⁻¹ * ν {u} = 0 := by
      rw [hc.1,Measure.smul_apply,smul_eq_mul,translate_neg_singleton_zero] at ha
      exact ha
    exact (mul_eq_zero.mp hz).resolve_left hci0
  · have he := congrArg (fun ξ : Measure U => ξ univ) (hc.1.symm.trans ha)
    change c⁻¹ * translate (-u) ν univ = (Measure.dirac (0 : U)) univ at he
    rw [htrans,ENNReal.mul_top hci0,Measure.dirac_apply_of_mem (mem_univ (0 : U))] at he
    exact False.elim (ENNReal.top_ne_one he)
end General

/-- The same actual real leaf becomes nonatomic on its non-Dirac part. -/
theorem real_lower_noAtoms {μ : Measure X} [IsFiniteMeasure μ]
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily realSplit μ t r η)
    (hinf : ∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → η q univ = ∞)
    (hatom : ∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) :
    ∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → NoAtoms (η q) := by
  have hc := canonical_real_lower_translation μ hr η hnormal hcanonical
  have ha := canonical_ae realSplit (fun u : ℝ => x u 0)
    (continuous_x.comp (continuous_id.prodMk continuous_const)) realMatrix_leaf_add
    μ hr η hcanonical hatom
  filter_upwards [hinf,hc,ha] with q hi hq ha hn
  exact noAtoms_of_infinite_translation_dichotomy (η q) (hi hn)
    (fun u => η (x u 0 • q)) r hq ha

/-- The same actual 2-adic leaf becomes nonatomic on its non-Dirac part. -/
theorem padic_lower_noAtoms {μ : Measure X} [IsFiniteMeasure μ]
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily padicSplit μ t r η)
    (hinf : ∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → η q univ = ∞)
    (hatom : ∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) :
    ∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → NoAtoms (η q) := by
  have hc := canonical_padic_lower_translation μ hr η hnormal hcanonical
  have ha := canonical_ae padicSplit (fun u : Q2 => x 0 u)
    (continuous_x.comp (continuous_const.prodMk continuous_id)) padicMatrix_leaf_add
    μ hr η hcanonical hatom
  filter_upwards [hinf,hc,ha] with q hi hq ha hn
  exact noAtoms_of_infinite_translation_dichotomy (η q) (hi hn)
    (fun u => η (x 0 u • q)) r hq ha



/-- Actual canonical real lower-root data with genuine non-Dirac nonatomicity. -/
theorem exists_real_lower_noAtoms_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → NoAtoms (η q)) := by
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_real_lower_covariant_data μ hK hμK ht hT
  have hn := hgood.mono fun _ hq => hq.2.2.1
  have hi := scalar_nonDirac_infinite (psi t 1) hT η hη hr hn (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  have ha := scalar_atom_dichotomy (psi t 1) hT η hη hr hn (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  exact ⟨r,hr,η,hη,hgood,hcanonical,real_lower_noAtoms hr η hn hcanonical hi ha⟩
/-- Actual canonical padic lower-root data with genuine non-Dirac nonatomicity. -/
theorem exists_padic_lower_noAtoms_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → NoAtoms (η q)) := by
  obtain ⟨r,hr,η,hη,hgood,hcov,hcanonical⟩ :=
    exists_padic_lower_covariant_data μ hK hμK ht hT
  have hn := hgood.mono fun _ hq => hq.2.2.1
  have hi := scalar_nonDirac_infinite (psi t 1) hT η hη hr hn (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  have ha := scalar_atom_dichotomy (psi t 1) hT η hη hr hn (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  exact ⟨r,hr,η,hη,hgood,hcanonical,padic_lower_noAtoms hr η hn hcanonical hi ha⟩
section Upper
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]

/-- Weyl transport preserves genuine absence of atoms on the non-Dirac part. -/
theorem upperFamily_noAtoms (μ : Measure X) (η : X → Measure U)
    (h : ∀ᵐ q ∂reflectedMeasure μ, η q ≠ Measure.dirac 0 → NoAtoms (η q)) :
    ∀ᵐ q ∂μ, upperFamily η q ≠ Measure.dirac 0 → NoAtoms (upperFamily η q) := by
  have hp := ae_of_ae_map (continuous_const_smul W⁻¹).measurable.aemeasurable h
  filter_upwards [hp] with q hq hn
  have hd : η (W⁻¹ • q) ≠ Measure.dirac 0 := by
    intro he
    apply hn
    change (η (W⁻¹ • q)).map (fun u => -u) = _
    rw [he,Measure.map_dirac measurable_neg]
    simp
  letI := hq hd
  constructor
  intro u
  change ((η (W⁻¹ • q)).map (fun v => -v)) {u} = 0
  rw [Measure.map_apply measurable_neg (measurableSet_singleton u)]
  have he : (fun v : U => -v) ⁻¹' {u} = {-u} := by ext v; simp
  rw [he,measure_singleton]
end Upper
/-- Actual canonical real upper-root data, obtained by the arithmetic Weyl action. -/
theorem exists_real_upper_noAtoms_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → NoAtoms (η q)) := by
  obtain ⟨hK',hμK'⟩ := reflectedMeasure_compact_mass μ hK hμK
  obtain ⟨r,hr,η,hη,hgood,hcanonical,hn⟩ :=
    exists_real_lower_noAtoms_data (reflectedMeasure μ) hK' hμK' ht
      (reflectedMeasure_inverse_invariant μ t 1 hT)
  exact ⟨r,hr,upperFamily η,measurable_upperFamily hη,upperFamily_properties μ η hgood,
    ⟨η,hcanonical,rfl⟩,upperFamily_noAtoms μ η hn⟩
/-- Actual canonical padic upper-root data, obtained by the arithmetic Weyl action. -/
theorem exists_padic_upper_noAtoms_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q ≠ Measure.dirac 0 → NoAtoms (η q)) := by
  obtain ⟨hK',hμK'⟩ := reflectedMeasure_compact_mass μ hK hμK
  obtain ⟨r,hr,η,hη,hgood,hcanonical,hn⟩ :=
    exists_padic_lower_noAtoms_data (reflectedMeasure μ) hK' hμK' ht
      (reflectedMeasure_inverse_invariant μ t 1 hT)
  exact ⟨r,hr,upperFamily η,measurable_upperFamily hη,upperFamily_properties μ η hgood,
    ⟨η,hcanonical,rfl⟩,upperFamily_noAtoms μ η hn⟩
end VV.BBEKOneRootNoAtoms
