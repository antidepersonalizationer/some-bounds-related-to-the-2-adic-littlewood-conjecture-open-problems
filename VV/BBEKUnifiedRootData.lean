import VV.BBEKCanonicalCovariance
import VV.BBEKOneRootNoAtoms
import VV.BBEKCompactLeafStabilizers

/-! Unified properties of one and the same actual canonical root family.
All conclusions are derived for a fixed η and its original radius before any
existential wrapper is used. Compact Mahler support is needed only to rule out
nontrivial stabilizers; the conditional exceptional bridge itself needs none. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace VV.BBEKUnifiedRootData
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKOrbit
open BBEKRootLeafKernel BBEKOneRootCovariance BBEKCanonicalCovariance
open BBEKLeafwiseStabilizer BBEKOneRootAtoms BBEKOneRootRecurrence
open BBEKRootContraction BBEKLeafStabilizerDichotomy BBEKLeafStabilizerEscape
open BBEKOneRootFullSupport BBEKOneRootNoAtoms
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- All needed pointwise consequences refer to the literal same leaf measure.
Non-Diracness itself is not inferred from entropy by this definition. -/
def RootProperties {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (ν : Measure F) : Prop :=
  translationStabilizer ν = ⊥ ∧ projectiveTranslationStabilizer ν = ⊥ ∧
    NonDiracRootSupport ν ∧ (ν ≠ Measure.dirac 0 → NoAtoms ν)
/-- Scaling, stabilizers, support generation and nonatomicity for a specified
real lower canonical family; no second existence witness is selected. -/
theorem canonical_real_lower_properties
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (ht : Real.log 2 ≤ t) (hr : 0 < r)
    (η : X → Measure ℝ) (hη : Measurable η)
    (hgood : ∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
      ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    (hc : IsConstructedRootFamily realSplit μ t r η) :
    (∀ᵐ q ∂μ,
      η (psi t 1 • q) = ((η q).map (realLeafScaling t) (ball 0 r))⁻¹ • (η q).map (realLeafScaling t) ∧
      0 < (η q).map (realLeafScaling t) (ball 0 r) ∧ (η q).map (realLeafScaling t) (ball 0 r) ≠ ∞) ∧
    (∀ᵐ q ∂μ, RootProperties (η q)) := by
  have hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ :=
    measurePreserving_smul (⟨psi t 1,psi_mem_A t 1⟩ : A) μ
  have hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ :=
    measurePreserving_smul (⟨(psi t 1)⁻¹,A.inv_mem (psi_mem_A t 1)⟩ : A) μ
  have hn := hgood.mono fun _ h => h.2.2.1
  have hcov := canonical_real_lower_covariance μ ht hr hA η hn hc
  have hcovNN := inverse_projective_covariance (psi t 1) hT η hn (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  have hdichotomy := ae_real_stabilizer_bot_or_top hT η hη
    (hgood.mono (fun _ h => h.2.1)) hn (a := (Real.exp (2*t))⁻¹)
      (inv_pos.mpr (Real.exp_pos _)) (by
        simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (Real.exp_pos _))] using
          real_inverse_scaling_norm_lt_one ht)
      (hcovNN.mono (fun _ h => ⟨h.choose,h.choose_spec.2⟩))
  have hne := ae_real_lower_stabilizer_ne_top μ hδ hmass hr η hc
    (hgood.mono fun _ h => h.2.2.2)
  have hbot := ae_stabilizer_eq_bot_of_ne_top μ η hne hdichotomy
  have hproj := scalar_projective_stabilizer_eq (psi t 1) hT η hη hr
    (hgood.mono fun _ h => h.1) hn (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  have hinf := scalar_nonDirac_infinite (psi t 1) hT η hη hr hn (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  have hatom := scalar_atom_dichotomy (psi t 1) hT η hη hr hn (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  have hno := real_lower_noAtoms hr η hn hc hinf hatom
  have hsupp := real_support_of_infinite_and_atoms η hinf hatom (hgood.mono fun _ h => h.2.2.2)
  refine ⟨hcov,?_⟩
  filter_upwards [hbot,hproj,hsupp,hno] with q hb hp hs hn
  exact ⟨hb,hp.trans hb,hs,hn⟩

/-- One actual real family simultaneously has every property required by
the proved EL backend, with one η and one original normalization radius. -/
theorem exists_real_lower_unified_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ,
        η (psi t 1 • q) = ((η q).map (realLeafScaling t) (ball 0 r))⁻¹ • (η q).map (realLeafScaling t) ∧
        0 < (η q).map (realLeafScaling t) (ball 0 r) ∧ (η q).map (realLeafScaling t) (ball 0 r) ≠ ∞) ∧
      (∀ᵐ q ∂μ, RootProperties (η q)) := by
  have hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ :=
    measurePreserving_smul (⟨(psi t 1)⁻¹,A.inv_mem (psi_mem_A t 1)⟩ : A) μ
  obtain ⟨r,hr,η,hη,hgood,_hcov,hc⟩ :=
    exists_real_lower_covariant_data μ (BBEKMahler.compact_K hδ) hmass ht hT
  exact ⟨r,hr,η,hη,hgood,hc,canonical_real_lower_properties μ hδ hmass ht hr η hη hgood hc⟩
/-- Scaling, stabilizers, support generation and nonatomicity for a specified
padic lower canonical family; no second existence witness is selected. -/
theorem canonical_padic_lower_properties
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t r : ℝ} (_ht : Real.log 2 ≤ t) (hr : 0 < r)
    (η : X → Measure Q2) (hη : Measurable η)
    (hgood : ∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
      ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε))
    (hc : IsConstructedRootFamily padicSplit μ t r η) :
    (∀ᵐ q ∂μ,
      η (psi t 1 • q) = ((η q).map (padicLeafScaling 1) (ball 0 r))⁻¹ • (η q).map (padicLeafScaling 1) ∧
      0 < (η q).map (padicLeafScaling 1) (ball 0 r) ∧ (η q).map (padicLeafScaling 1) (ball 0 r) ≠ ∞) ∧
    (∀ᵐ q ∂μ, RootProperties (η q)) := by
  have hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ :=
    measurePreserving_smul (⟨psi t 1,psi_mem_A t 1⟩ : A) μ
  have hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ :=
    measurePreserving_smul (⟨(psi t 1)⁻¹,A.inv_mem (psi_mem_A t 1)⟩ : A) μ
  have hn := hgood.mono fun _ h => h.2.2.1
  have hcov := canonical_padic_lower_covariance μ hr hA η hn hc
  have hcovNN := inverse_projective_covariance (psi t 1) hT η hn (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  have hdichotomy := ae_padic_stabilizer_bot_or_top hT η hη
    (hgood.mono (fun _ h => h.2.1)) hn (a := ((2 : Q2)^(-2*(1 : ℤ)))⁻¹)
      (inv_ne_zero (zpow_ne_zero _ (by norm_num))) padic_inverse_scaling_norm_lt_one
      (hcovNN.mono (fun _ h => ⟨h.choose,h.choose_spec.2⟩))
  have hne := ae_padic_lower_stabilizer_ne_top μ hδ hmass hr η hc
    (hgood.mono fun _ h => h.2.2.2)
  have hbot := ae_stabilizer_eq_bot_of_ne_top μ η hne hdichotomy
  have hproj := scalar_projective_stabilizer_eq (psi t 1) hT η hη hr
    (hgood.mono fun _ h => h.1) hn (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  have hinf := scalar_nonDirac_infinite (psi t 1) hT η hη hr hn (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  have hatom := scalar_atom_dichotomy (psi t 1) hT η hη hr hn (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  have hno := padic_lower_noAtoms hr η hn hc hinf hatom
  have hsupp := padic_support_of_infinite η hinf (hgood.mono fun _ h => h.1)
  refine ⟨hcov,?_⟩
  filter_upwards [hbot,hproj,hsupp,hno] with q hb hp hs hn
  exact ⟨hb,hp.trans hb,hs,hn⟩

/-- One actual padic family simultaneously has every property required by
the proved EL backend, with one η and one original normalization radius. -/
theorem exists_padic_lower_unified_data
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ,
        η (psi t 1 • q) = ((η q).map (padicLeafScaling 1) (ball 0 r))⁻¹ • (η q).map (padicLeafScaling 1) ∧
        0 < (η q).map (padicLeafScaling 1) (ball 0 r) ∧ (η q).map (padicLeafScaling 1) (ball 0 r) ≠ ∞) ∧
      (∀ᵐ q ∂μ, RootProperties (η q)) := by
  have hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ :=
    measurePreserving_smul (⟨(psi t 1)⁻¹,A.inv_mem (psi_mem_A t 1)⟩ : A) μ
  obtain ⟨r,hr,η,hη,hgood,_hcov,hc⟩ :=
    exists_padic_lower_covariant_data μ (BBEKMahler.compact_K hδ) hmass ht hT
  exact ⟨r,hr,η,hη,hgood,hc,canonical_padic_lower_properties μ hδ hmass ht hr η hη hgood hc⟩
end VV.BBEKUnifiedRootData

