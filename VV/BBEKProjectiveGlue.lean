import VV.BBEKMeasureGlue

/-! Actual normalization and Radon extension of projectively agreeing local
measures on a countable open cover with a common positive reference set. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal Topology
namespace VV.BBEKProjectiveGlue
open BBEKMeasureGlue
variable {U : Type*} [MeasurableSpace U]

def normalize (η : Measure U) (B : Set U) : Measure U := (η B)⁻¹ • η

theorem normalize_finite (η : Measure U) [IsFiniteMeasure η] (B : Set U)
    (hB : 0 < η B) : IsFiniteMeasure (normalize η B) := by
  constructor
  change (η B)⁻¹ * η univ < ∞
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hB) (measure_lt_top η univ)

theorem normalize_apply (η : Measure U) [IsFiniteMeasure η] (B : Set U)
    (hB : 0 < η B) : normalize η B B = 1 :=
  ENNReal.inv_mul_cancel hB.ne' (measure_ne_top _ _)

/-- The common positive reference mass removes the proportionality constant. -/
theorem normalize_restrict_of_projective (μ ν : Measure U) {B s : Set U}
    (hB : MeasurableSet B) (hBs : B ⊆ s) {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ∞)
    (he : μ.restrict s = c • ν.restrict s) :
    (normalize μ B).restrict s = (normalize ν B).restrict s := by
  have hm : μ B = c * ν B := by
    have hh := congrArg (fun η : Measure U => η B) he
    simpa only [Measure.restrict_apply hB, inter_eq_self_of_subset_left hBs,
      Measure.smul_apply, smul_eq_mul] using hh
  rw [normalize, normalize, Measure.restrict_smul, Measure.restrict_smul,
    he, hm, smul_smul, ENNReal.mul_inv (Or.inl hc) (Or.inl hc')]
  congr 1
  calc
    c⁻¹ * (ν B)⁻¹ * c = (ν B)⁻¹ * (c⁻¹*c) := by ac_rfl
    _ = (ν B)⁻¹ := by rw [ENNReal.inv_mul_cancel hc hc', mul_one]

/-- Projective local data construct a genuine normalized, locally finite
regular measure. Actual leaf-chart data must still be proved to satisfy these
overlap identities on a common conull set before this theorem is instantiated. -/
theorem exists_normalized_extension [PseudoMetricSpace U] [SigmaCompactSpace U] [BorelSpace U]
    (s : ℕ → Set U) (hs : ∀ n, IsOpen (s n)) (hcover : ⋃ n, s n = univ)
    (η : ℕ → Measure U) [∀ n, IsFiniteMeasure (η n)]
    (B : Set U) (hB : MeasurableSet B) (hBs : ∀ n, B ⊆ s n) (hpos : ∀ n, 0 < η n B)
    (hprojective : ∀ n m, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      (η n).restrict (s n ∩ s m) = c • (η m).restrict (s n ∩ s m)) :
    ∃ ν : Measure U, IsLocallyFiniteMeasure ν ∧ ν.Regular ∧ ν B = 1 ∧
      ∀ n, ν.restrict (s n) = (η n B)⁻¹ • (η n).restrict (s n) := by
  let θ : ℕ → Measure U := fun n => normalize (η n) B
  letI : ∀ n, IsFiniteMeasure (θ n) := fun n => normalize_finite (η n) B (hpos n)
  have hagree (n m : ℕ) : (θ n).restrict (s n ∩ s m) = (θ m).restrict (s n ∩ s m) := by
    obtain ⟨c,hc,hc',he⟩ := hprojective n m
    exact normalize_restrict_of_projective (η n) (η m) hB
      (fun _ hu => ⟨hBs n hu,hBs m hu⟩) hc hc' he
  let ν := glue s θ
  have hres (n : ℕ) : ν.restrict (s n) = (θ n).restrict (s n) :=
    glue_restrict s (fun n => (hs n).measurableSet) hcover θ hagree n
  refine ⟨ν,glue_locallyFinite s hs hcover θ hagree,glue_regular s hs hcover θ hagree,?_,?_⟩
  · have hh := congrArg (fun m : Measure U => m B) (hres 0)
    simp only [Measure.restrict_apply hB, inter_eq_self_of_subset_left (hBs 0)] at hh
    exact hh.trans (normalize_apply (η 0) B (hpos 0))
  · intro n
    exact (hres n).trans (Measure.restrict_smul _ _ _)

end VV.BBEKProjectiveGlue
