import Mathlib.Dynamics.Ergodic.Extreme
import Mathlib.Dynamics.Ergodic.Action.Basic

/-! An extreme invariant probability with prescribed full-measure support is
ergodic for the entire group. This proves the group version directly and does
not assume an ergodic-decomposition theorem. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped ENNReal

namespace ErgodicTheory.Entropy
variable {H X : Type*} [Group H] [MeasurableSpace H] [MeasurableSpace X]
  [MulAction H X] [MeasurableSMul H X]

def supportedInvariantProbabilities (H : Type*) [Group H] [MulAction H X]
    (Y : Set X) : Set (Measure X) :=
  {μ | SMulInvariantMeasure H X μ ∧ IsProbabilityMeasure μ ∧ μ Y = 1}

theorem cond_smulInvariantMeasure (μ : Measure X) [SMulInvariantMeasure H X μ]
    {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ g : H, (g • ·) ⁻¹' s =ᵐ[μ] s) : SMulInvariantMeasure H X (μ[|s]) := by
  constructor
  intro g u hu
  have hr : MeasurePreserving (fun x : X => g • x) (μ.restrict s) (μ.restrict s) := by
    have hh := (measurePreserving_smul g μ).restrict_preimage hs
    rwa [Measure.restrict_congr_set (hinv g)] at hh
  exact (hr.smul_measure ((μ s)⁻¹)).measure_preimage hu.nullMeasurableSet

theorem groupErgodic_of_extreme_supported {Y : Set X} (hY : MeasurableSet Y)
    {μ : Measure X}
    (he : μ ∈ extremePoints ℝ≥0∞ (supportedInvariantProbabilities H Y)) :
    ErgodicSMul H X μ := by
  letI : SMulInvariantMeasure H X μ := he.1.1
  letI : IsProbabilityMeasure μ := he.1.2.1
  have hY0 : μ Yᶜ = 0 := by
    rw [measure_compl hY (measure_ne_top μ Y),measure_univ,he.1.2.2,tsub_self]
  constructor
  intro s hs hinv
  by_contra hnot
  obtain ⟨hs0,hsc0⟩ : μ s ≠ 0 ∧ μ sᶜ ≠ 0 := by
    simpa [eventuallyConst_set,ae_iff,and_comm] using hnot
  have hcond {u : Set X} (hu : MeasurableSet u) (hu0 : μ u ≠ 0)
      (huint : ∀ g : H, (g • ·) ⁻¹' u =ᵐ[μ] u) :
      μ[|u] ∈ supportedInvariantProbabilities H Y := by
    refine ⟨cond_smulInvariantMeasure μ hu huint,cond_isProbabilityMeasure hu0,?_⟩
    rw [cond_apply hu μ Y,measure_inter_conull hY0,
      ENNReal.inv_mul_cancel hu0 (measure_ne_top μ u)]
  have hc : μ[|s] = μ := by
    apply (he.2 (hcond hs hs0 hinv)
      (hcond hs.compl hsc0 (fun g => by
        simpa only [preimage_compl] using (hinv g).compl)) ?_).1
    refine ⟨μ s,μ sᶜ,pos_iff_ne_zero.mpr hs0,pos_iff_ne_zero.mpr hsc0,?_,?_⟩
    · exact (measure_add_measure_compl hs).trans measure_univ
    · simp [ProbabilityTheory.cond,smul_smul,ENNReal.mul_inv_cancel hs0 (measure_ne_top μ s),
        ENNReal.mul_inv_cancel hsc0 (measure_ne_top μ sᶜ),
        Measure.restrict_add_restrict_compl hs]
  rw [← hc] at hsc0
  simp [cond_apply hs μ sᶜ] at hsc0

end ErgodicTheory.Entropy
