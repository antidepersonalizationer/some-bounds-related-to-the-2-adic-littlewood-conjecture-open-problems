import VV.BBEKMautnerLp
import VV.BBEKNoncompact
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! Full-group ergodicity and full support on the actual arithmetic quotient.
The invariant measure is not constructed here. For any such measure these
properties follow from transitivity, Fubini, and Haar translation, with no
ergodicity or fixed-vector hypothesis. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology ENNReal

namespace VV.BBEKHomogeneousErgodic

/-- A transitive measurable action is ergodic for any invariant S-finite
measure, provided the group has a nonzero S-finite left-invariant measure.
Fubini and right-translation of that measure identify all good fibers. -/
theorem ergodicSMul_of_pretransitive
    {H Y : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
    [MeasurableSpace Y] [MulAction H Y] [MeasurableSMul₂ H Y]
    [MulAction.IsPretransitive H Y]
    (mH : Measure H) [SFinite mH] [mH.IsMulLeftInvariant] [NeZero mH]
    (μ : Measure Y) [SFinite μ] [SMulInvariantMeasure H Y μ] :
    ErgodicSMul H Y μ := by
  refine ⟨fun {s} hsm hs => ?_⟩
  suffices (∃ᵐ x ∂μ, x ∈ s) → ∀ᵐ x ∂μ, x ∈ s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hpos
  have hgood : ∀ᵐ x ∂μ, ∀ᵐ g ∂mH, (g • x ∈ s ↔ x ∈ s) := by
    rw [ae_ae_comm]
    · exact ae_of_all _ fun g => (hs g).mem_iff
    · exact ((hsm.preimage (measurable_snd.smul measurable_fst)).mem.iff
        (hsm.preimage measurable_fst).mem).setOf
  obtain ⟨a,has,ha⟩ := (hpos.and_eventually hgood).exists
  filter_upwards [hgood] with b hb
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H a b
  have ha' := (quasiMeasurePreserving_mul_right mH g).ae ha
  obtain ⟨h,hh,hb'⟩ := (ha'.and hb).exists
  rw [mul_smul,hg] at hh
  exact hb'.mp (hh.mpr has)

/-- Transitivity and inner regularity force a nonzero invariant measure
to give positive mass to every nonempty open set. -/
theorem isOpenPosMeasure_of_pretransitive
    {H Y : Type*} [Group H] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction H Y] [ContinuousConstSMul H Y] [MulAction.IsPretransitive H Y]
    (μ : Measure Y) [μ.InnerRegular] [NeZero μ] [SMulInvariantMeasure H Y μ] :
    IsOpenPosMeasure μ := by
  obtain ⟨C,hC,hCpos⟩ := InnerRegular.exists_isCompact_not_null.mpr (NeZero.ne μ)
  refine ⟨fun U hU hne => ?_⟩
  contrapose! hCpos
  rw [← nonpos_iff_eq_zero]
  obtain ⟨u,hu⟩ := hne
  have hcover : C ⊆ ⋃ g : H, (fun y : Y => g • y) ⁻¹' U := by
    intro y _
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H y u
    exact Set.mem_iUnion.mpr ⟨g, by change g • y ∈ U; rwa [hg]⟩
  obtain ⟨T,hT⟩ := hC.elim_finite_subcover
    (fun g : H => (fun y : Y => g • y) ⁻¹' U)
    (fun g => hU.preimage (continuous_const_smul g)) hcover
  calc
    μ C ≤ μ (⋃ (g : H) (_ : g ∈ T), (fun y : Y => g • y) ⁻¹' U) := measure_mono hT
    _ ≤ ∑ g ∈ T, μ ((fun y : Y => g • y) ⁻¹' U) := measure_biUnion_finset_le _ _
    _ = 0 := by simp [SMulInvariantMeasure.measure_preimage_smul _ hU.measurableSet, hCpos]

open BBEKDynamics BBEKQuotient BBEKDiscrete BBEKMautnerLp
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance {F : Type*} [CommRing F] [TopologicalSpace F] [SecondCountableTopology F] :
    SecondCountableTopology (Matrix.SpecialLinearGroup (Fin 2) F) := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  exact TopologicalSpace.Subtype.secondCountableTopology
    {M : Matrix (Fin 2) (Fin 2) F | M.det = 1}
local instance : MeasurableSpace G := borel G
local instance : BorelSpace G := ⟨rfl⟩
local instance : SecondCountableTopology G := by infer_instance
local instance : MeasurableMul₂ G := ⟨continuous_mul.measurable⟩
local instance : MeasurableInv G := ⟨continuous_inv.measurable⟩
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem quotient_ergodicSMul (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure G X μ] : ErgodicSMul G X μ := by
  letI : MulAction.IsPretransitive G X :=
    inferInstanceAs (MulAction.IsPretransitive G (G ⧸ Gamma))
  exact ergodicSMul_of_pretransitive (Measure.haar : Measure G) μ

theorem quotient_isOpenPosMeasure (μ : Measure X) [μ.InnerRegular] [NeZero μ]
    [SMulInvariantMeasure G X μ] : IsOpenPosMeasure μ := by
  letI : MulAction.IsPretransitive G X :=
    inferInstanceAs (MulAction.IsPretransitive G (G ⧸ Gamma))
  exact isOpenPosMeasure_of_pretransitive (H:=G) μ

/-- The diagonal transformation is ergodic for every invariant Radon
probability on the literal BBEK quotient; full-group ergodicity is proved. -/
theorem quotient_psi_ergodic_of_invariant (μ : Measure X)
    [IsProbabilityMeasure μ] [μ.InnerRegular] [SMulInvariantMeasure G X μ]
    {t : ℝ} (ht : 0 < t) : Ergodic (fun z : X => psi t 1 • z) μ := by
  letI : ErgodicSMul G X μ := quotient_ergodicSMul μ
  exact quotient_psi_ergodic μ ht

/-- A full-group invariant Radon probability cannot be supported by the
actual proper closed Mahler set. This uses full support, not Haar uniqueness. -/
theorem invariant_probability_K_ne_one (μ : Measure X)
    [IsProbabilityMeasure μ] [μ.InnerRegular] [SMulInvariantMeasure G X μ]
    {δ : ℝ} (hδ : 0 < δ) : μ (BBEKOrbit.K δ) ≠ 1 := by
  letI : IsOpenPosMeasure μ := quotient_isOpenPosMeasure μ
  intro he
  exact BBEKNoncompact.K_ne_univ hδ
    ((BBEKOrbit.isClosed_K δ).measure_eq_one_iff_eq_univ.mp he)

end VV.BBEKHomogeneousErgodic

