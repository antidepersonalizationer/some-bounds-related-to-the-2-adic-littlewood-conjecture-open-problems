import VV.BBEKKernelFiberRestriction

/-! Conditional kernels under embeddings of the transverse domain. This lets
local open transverse charts use the same canonical kernels as ambient coordinates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafwiseKernel
variable {B C U V : Type*} [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace U] [MeasurableSpace V]

theorem compProd_map_comap (μ : Measure B) [SFinite μ] (κ : Kernel C U)
    [IsFiniteKernel κ] {f : B → C} (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs,
    Measure.compProd_apply ((hf.prodMap measurable_id) hs),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

theorem fst_map_base (ρ : Measure (B × U)) {f : B → C} (hf : Measurable f) :
    (ρ.map (Prod.map f id)).fst = ρ.fst.map f := by
  simp only [Measure.fst, Measure.map_map measurable_fst (hf.prodMap measurable_id),
    Measure.map_map hf measurable_fst]
  rfl

variable [StandardBorelSpace U] [Nonempty U]

theorem condKernel_map_embedding (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {f : B → C} (hf : MeasurableEmbedding f) :
    ∀ᵐ b ∂ρ.fst, (ρ.map (Prod.map f id)).condKernel (f b) = ρ.condKernel b := by
  let κ := (ρ.map (Prod.map f id)).condKernel
  have he : (ρ.fst ⊗ₘ κ.comap f hf.measurable).map (Prod.map f id) =
      ρ.map (Prod.map f id) := by
    rw [compProd_map_comap, ← fst_map_base ρ hf.measurable]
    exact Measure.disintegrate _ _
  have he' := congrArg (Measure.comap (Prod.map f id)) he
  simp only [(hf.prodMap MeasurableEmbedding.id).comap_map] at he'
  exact eq_condKernel_of_measure_eq_compProd (κ.comap f hf.measurable) he'.symm

variable [StandardBorelSpace V] [Nonempty V]

/-- Skew covariance remains valid for an embedded, rather than surjective,
transverse change. In particular this applies to open-chart inclusions. -/
theorem condKernel_map_skew_embedding (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {f : B → C} (hf : MeasurableEmbedding f) (g : B × U → V) (hg : Measurable g) :
    ∀ᵐ b ∂ρ.fst, (ρ.map (fun p => (f p.1,g p))).condKernel (f b) =
      (ρ.condKernel b).map (fun u => g (b,u)) := by
  let σ := ρ.map (fun p => (p.1,g p))
  have hbase : σ.fst = ρ.fst := by
    exact (fst_map_skew ρ (MeasurableEquiv.refl B) g hg).trans
      (by change ρ.fst.map id = ρ.fst; exact Measure.map_id)
  have hm : Measurable (fun p : B × U => (p.1,g p)) := measurable_fst.prodMk hg
  have hmap : σ.map (Prod.map f id) = ρ.map (fun p => (f p.1,g p)) := by
    dsimp only [σ]
    rw [Measure.map_map (hf.measurable.prodMap measurable_id) hm]
    rfl
  have h₁ := condKernel_map_embedding σ hf
  rw [hbase, condKernel_congr hmap] at h₁
  have h₂ := condKernel_map_skew ρ (MeasurableEquiv.refl B) g hg
  filter_upwards [h₁,h₂] with b hb₁ hb₂
  exact hb₁.trans hb₂

end VV.BBEKLeafwiseKernel
