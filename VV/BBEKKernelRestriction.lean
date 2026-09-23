import VV.BBEKLeafwiseKernel
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Actual normalization of restricted conditional kernels, used when local leaf boxes overlap. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafwiseKernel
variable {B U : Type*} [MeasurableSpace B] [MeasurableSpace U]

/-- Conditioning a kernel to a measurable leaf set. Zero-mass fibers give the zero measure. -/
def conditionKernel (κ : Kernel B U) {s : Set U} (hs : MeasurableSet s) : Kernel B U where
  toFun b := (κ b s)⁻¹ • (κ b).restrict s
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro t ht
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply ht]
    exact ((κ.measurable_coe hs).inv).mul (κ.measurable_coe (ht.inter hs))

theorem conditionKernel_apply (κ : Kernel B U) {s : Set U} (hs : MeasurableSet s) (b : B) :
    conditionKernel κ hs b = (κ b s)⁻¹ • (κ b).restrict s := rfl

instance conditionKernel_finite (κ : Kernel B U) {s : Set U} (hs : MeasurableSet s) :
    IsFiniteKernel (conditionKernel κ hs) := by
  refine ⟨⟨1, by simp, fun b => ?_⟩⟩
  simp only [conditionKernel_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact ENNReal.inv_mul_le_one _

theorem conditionKernel_probability (κ : Kernel B U) [IsFiniteKernel κ]
    {s : Set U} (hs : MeasurableSet s) {b : B} (hb : κ b s ≠ 0) :
    IsProbabilityMeasure (conditionKernel κ hs b) := by
  constructor
  simp only [conditionKernel_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact ENNReal.inv_mul_cancel hb (measure_ne_top _ _)

/-- The restriction and its conditional normalization are genuinely proportional on nonzero fibers. -/
theorem conditionKernel_smul (κ : Kernel B U) [IsFiniteKernel κ]
    {s : Set U} (hs : MeasurableSet s) (b : B) :
    (κ b s) • conditionKernel κ hs b = (κ b).restrict s := by
  by_cases hb : κ b s = 0
  · have hz : (κ b).restrict s = 0 := Measure.restrict_eq_zero.mpr hb
    simp [hb, hz]
  · rw [conditionKernel_apply, smul_smul, ENNReal.mul_inv_cancel hb (measure_ne_top _ _), one_smul]

variable [StandardBorelSpace U] [Nonempty U]

def leafRestrictedMarginal (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set U} (hs : MeasurableSet s) : Measure B :=
  ρ.fst.withDensity (fun b => ρ.condKernel b s)

instance leafRestrictedMarginal_finite (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set U} (hs : MeasurableSet s) : IsFiniteMeasure (leafRestrictedMarginal ρ hs) := by
  refine ⟨lt_of_le_of_lt ?_ (measure_lt_top ρ.fst univ)⟩
  change (ρ.fst.withDensity (fun b => ρ.condKernel b s)) univ ≤ ρ.fst univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ _ : B, 1 ∂ρ.fst := lintegral_mono (fun _ => prob_le_one)
    _ = _ := by simp

/-- Restriction in a leaf coordinate is reconstructed by the weighted transverse marginal
and the explicitly normalized restricted kernel. -/
theorem disintegrate_leafRestriction (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set U} (hs : MeasurableSet s) :
    leafRestrictedMarginal ρ hs ⊗ₘ conditionKernel ρ.condKernel hs =
      ρ.restrict (univ ×ˢ s) := by
  apply Measure.ext
  intro t ht
  rw [Measure.compProd_apply ht]
  change (∫⁻ b, conditionKernel ρ.condKernel hs b (Prod.mk b ⁻¹' t)
      ∂ρ.fst.withDensity (fun b => ρ.condKernel b s)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (ρ.condKernel.measurable_coe hs)
    (Kernel.measurable_kernel_prodMk_left ht)]
  rw [Measure.restrict_apply ht]
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply (ht.inter (MeasurableSet.univ.prod hs))]
  apply lintegral_congr
  intro b
  change (ρ.condKernel b s) * (conditionKernel ρ.condKernel hs b) (Prod.mk b ⁻¹' t) = _
  rw [← smul_eq_mul, ← Measure.smul_apply, conditionKernel_smul,
    Measure.restrict_apply (measurable_prodMk_left ht)]
  congr 1
  ext u
  simp

theorem fst_leafRestriction (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set U} (hs : MeasurableSet s) :
    (ρ.restrict (univ ×ˢ s)).fst = leafRestrictedMarginal ρ hs := by
  apply Measure.ext
  intro t ht
  rw [Measure.fst_apply ht, Measure.restrict_apply (measurable_fst ht)]
  change ρ (Prod.fst ⁻¹' t ∩ univ ×ˢ s) =
    (ρ.fst.withDensity (fun b => ρ.condKernel b s)) t
  rw [withDensity_apply _ ht,
    Measure.setLIntegral_condKernel_eq_measure_prod ht hs]
  congr 1
  ext p
  simp

/-- The canonical conditional kernel after restricting a leaf box is exactly
the normalized restriction of the original conditional kernel, almost everywhere. -/
theorem condKernel_leafRestriction (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set U} (hs : MeasurableSet s) :
    ∀ᵐ b ∂(ρ.restrict (univ ×ˢ s)).fst,
      (ρ.restrict (univ ×ˢ s)).condKernel b =
        (ρ.condKernel b s)⁻¹ • (ρ.condKernel b).restrict s := by
  have he : (ρ.restrict (univ ×ˢ s)).fst ⊗ₘ conditionKernel ρ.condKernel hs =
      ρ.restrict (univ ×ˢ s) := by
    rw [fst_leafRestriction ρ hs]
    exact disintegrate_leafRestriction ρ hs
  have hh := eq_condKernel_of_measure_eq_compProd (conditionKernel ρ.condKernel hs) he.symm
  filter_upwards [hh] with b hb
  exact hb.symm

end VV.BBEKLeafwiseKernel
