import VV.BBEKKernelSkew

/-! Restricting conditional kernels to arbitrary measurable boxes, including
boxes whose leaf sections depend on the transverse coordinate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafwiseKernel
variable {B U : Type*} [MeasurableSpace B] [MeasurableSpace U]

def fiberCondition (κ : Kernel B U) [IsSFiniteKernel κ]
    {s : Set (B × U)} (hs : MeasurableSet s) : Kernel B U where
  toFun b := (κ b (Prod.mk b ⁻¹' s))⁻¹ • (κ b).restrict (Prod.mk b ⁻¹' s)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro t ht
    change Measurable (fun b =>
      ((κ b (Prod.mk b ⁻¹' s))⁻¹ • (κ b).restrict (Prod.mk b ⁻¹' s)) t)
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply ht]
    exact (Kernel.measurable_kernel_prodMk_left hs).inv.mul
      (Kernel.measurable_kernel_prodMk_left ((measurable_snd ht).inter hs))

theorem fiberCondition_apply (κ : Kernel B U) [IsSFiniteKernel κ]
    {s : Set (B × U)} (hs : MeasurableSet s) (b : B) :
    fiberCondition κ hs b =
      (κ b (Prod.mk b ⁻¹' s))⁻¹ • (κ b).restrict (Prod.mk b ⁻¹' s) := rfl

instance fiberCondition_finite (κ : Kernel B U) [IsSFiniteKernel κ]
    {s : Set (B × U)} (hs : MeasurableSet s) : IsFiniteKernel (fiberCondition κ hs) := by
  refine ⟨⟨1, by simp, fun b => ?_⟩⟩
  simp only [fiberCondition_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact ENNReal.inv_mul_le_one _

theorem fiberCondition_smul (κ : Kernel B U) [IsFiniteKernel κ]
    {s : Set (B × U)} (hs : MeasurableSet s) (b : B) :
    (κ b (Prod.mk b ⁻¹' s)) • fiberCondition κ hs b =
      (κ b).restrict (Prod.mk b ⁻¹' s) :=
  conditionKernel_smul κ (measurable_prodMk_left hs) b

variable [StandardBorelSpace U] [Nonempty U]

def fiberRestrictedMarginal (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set (B × U)} (_hs : MeasurableSet s) : Measure B :=
  ρ.fst.withDensity (fun b => ρ.condKernel b (Prod.mk b ⁻¹' s))

instance fiberRestrictedMarginal_finite (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set (B × U)} (hs : MeasurableSet s) :
    IsFiniteMeasure (fiberRestrictedMarginal ρ hs) := by
  refine ⟨lt_of_le_of_lt ?_ (measure_lt_top ρ.fst univ)⟩
  change (ρ.fst.withDensity (fun b => ρ.condKernel b (Prod.mk b ⁻¹' s))) univ ≤ _
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ _ : B, 1 ∂ρ.fst := lintegral_mono (fun _ => prob_le_one)
    _ = _ := by simp

theorem disintegrate_fiberRestriction (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set (B × U)} (hs : MeasurableSet s) :
    fiberRestrictedMarginal ρ hs ⊗ₘ fiberCondition ρ.condKernel hs = ρ.restrict s := by
  apply Measure.ext
  intro t ht
  rw [Measure.compProd_apply ht]
  change (∫⁻ b, fiberCondition ρ.condKernel hs b (Prod.mk b ⁻¹' t)
      ∂ρ.fst.withDensity (fun b => ρ.condKernel b (Prod.mk b ⁻¹' s))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _
    (Kernel.measurable_kernel_prodMk_left hs) (Kernel.measurable_kernel_prodMk_left ht)]
  rw [Measure.restrict_apply ht]
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply (ht.inter hs)]
  apply lintegral_congr
  intro b
  change (ρ.condKernel b (Prod.mk b ⁻¹' s)) *
    (fiberCondition ρ.condKernel hs b) (Prod.mk b ⁻¹' t) = _
  rw [← smul_eq_mul, ← Measure.smul_apply, fiberCondition_smul,
    Measure.restrict_apply (measurable_prodMk_left ht)]
  rfl

theorem fst_fiberRestriction (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set (B × U)} (hs : MeasurableSet s) :
    (ρ.restrict s).fst = fiberRestrictedMarginal ρ hs := by
  apply Measure.ext
  intro t ht
  rw [Measure.fst_apply ht, Measure.restrict_apply (measurable_fst ht)]
  change ρ (Prod.fst ⁻¹' t ∩ s) =
    (ρ.fst.withDensity (fun b => ρ.condKernel b (Prod.mk b ⁻¹' s))) t
  rw [withDensity_apply _ ht]
  rw [← lintegral_indicator ht (fun b => ρ.condKernel b (Prod.mk b ⁻¹' s))]
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply ((measurable_fst ht).inter hs)]
  apply lintegral_congr
  intro b
  by_cases hb : b ∈ t
  · rw [indicator_of_mem hb]
    congr 1
    ext u
    simp [hb]
  · rw [indicator_of_not_mem hb]
    have he : Prod.mk b ⁻¹' (Prod.fst ⁻¹' t ∩ s) = ∅ := by ext u; simp [hb]
    rw [he, measure_empty]

/-- Compatibility on a completely general measurable overlap, not just a product box. -/
theorem condKernel_fiberRestriction (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {s : Set (B × U)} (hs : MeasurableSet s) :
    ∀ᵐ b ∂(ρ.restrict s).fst, (ρ.restrict s).condKernel b =
      (ρ.condKernel b (Prod.mk b ⁻¹' s))⁻¹ • (ρ.condKernel b).restrict (Prod.mk b ⁻¹' s) := by
  have he : (ρ.restrict s).fst ⊗ₘ fiberCondition ρ.condKernel hs = ρ.restrict s := by
    rw [fst_fiberRestriction ρ hs]
    exact disintegrate_fiberRestriction ρ hs
  have hh := eq_condKernel_of_measure_eq_compProd (fiberCondition ρ.condKernel hs) he.symm
  filter_upwards [hh] with b hb
  exact hb.symm

end VV.BBEKLeafwiseKernel
