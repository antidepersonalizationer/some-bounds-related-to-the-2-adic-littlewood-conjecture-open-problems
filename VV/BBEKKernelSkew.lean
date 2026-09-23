import VV.BBEKLeafwiseSupport

/-!
Disintegration covariance under measurable, transverse-dependent leaf maps.
Unlike a product map, this permits a different translation on each plaque;
it is the change-of-coordinates operation needed for leaf-chart overlaps.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafwiseKernel
variable {B C U V : Type*} [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace U] [MeasurableSpace V]

def fiberMapKernel (κ : Kernel B U) [IsSFiniteKernel κ]
    (g : B × U → V) (hg : Measurable g) : Kernel B V where
  toFun b := (κ b).map (fun u => g (b,u))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hm (b : B) : Measurable (fun u => g (b,u)) := hg.comp measurable_prodMk_left
    change Measurable (fun b => ((κ b).map (fun u => g (b,u))) s)
    simp_rw [Measure.map_apply (hm _) hs]
    exact Kernel.measurable_kernel_prodMk_left (hs.preimage hg)

theorem fiberMapKernel_apply (κ : Kernel B U) [IsSFiniteKernel κ]
    (g : B × U → V) (hg : Measurable g) (b : B) :
    fiberMapKernel κ g hg b = (κ b).map (fun u => g (b,u)) := rfl

instance fiberMapKernel_finite (κ : Kernel B U) [IsFiniteKernel κ]
    (g : B × U → V) (hg : Measurable g) : IsFiniteKernel (fiberMapKernel κ g hg) := by
  refine ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun b => ?_⟩⟩
  have hm : Measurable (fun u => g (b,u)) := hg.comp measurable_prodMk_left
  rw [fiberMapKernel_apply, Measure.map_apply hm
    MeasurableSet.univ, preimage_univ]
  exact Kernel.measure_le_bound κ b univ

instance fiberMapKernel_markov (κ : Kernel B U) [IsMarkovKernel κ]
    (g : B × U → V) (hg : Measurable g) : IsMarkovKernel (fiberMapKernel κ g hg) :=
  ⟨fun _ => isProbabilityMeasure_map (hg.comp measurable_prodMk_left).aemeasurable⟩

def skewTransport (f : B ≃ᵐ C) (κ : Kernel B U) [IsSFiniteKernel κ]
    (g : B × U → V) (hg : Measurable g) : Kernel C V :=
  (fiberMapKernel κ g hg).comap f.symm f.symm.measurable

instance skewTransport_finite (f : B ≃ᵐ C) (κ : Kernel B U) [IsFiniteKernel κ]
    (g : B × U → V) (hg : Measurable g) : IsFiniteKernel (skewTransport f κ g hg) := by
  unfold skewTransport
  infer_instance

theorem skewTransport_apply (f : B ≃ᵐ C) (κ : Kernel B U) [IsSFiniteKernel κ]
    (g : B × U → V) (hg : Measurable g) (b : B) :
    skewTransport f κ g hg (f b) = (κ b).map (fun u => g (b,u)) := by
  simp only [skewTransport, Kernel.comap_apply, f.symm_apply_apply, fiberMapKernel_apply]

theorem fst_map_skew (ρ : Measure (B × U)) (f : B ≃ᵐ C)
    (g : B × U → V) (hg : Measurable g) :
    (ρ.map (fun p => (f p.1, g p))).fst = ρ.fst.map f := by
  have hm : Measurable (fun p : B × U => (f p.1,g p)) :=
    (f.measurable.comp measurable_fst).prodMk hg
  simp only [Measure.fst, Measure.map_map measurable_fst
    hm,
    Measure.map_map f.measurable measurable_fst]
  rfl

theorem compProd_skewTransport (μ : Measure B) [SFinite μ]
    (κ : Kernel B U) [IsFiniteKernel κ] (f : B ≃ᵐ C)
    (g : B × U → V) (hg : Measurable g) :
    μ.map f ⊗ₘ skewTransport f κ g hg =
      (μ ⊗ₘ κ).map (fun p => (f p.1, g p)) := by
  have hm : Measurable (fun p : B × U => (f p.1,g p)) :=
    (f.measurable.comp measurable_fst).prodMk hg
  apply Measure.ext
  intro s hs
  rw [Measure.compProd_apply hs, f.measurableEmbedding.lintegral_map,
    Measure.map_apply hm hs, Measure.compProd_apply (hs.preimage hm)]
  apply lintegral_congr
  intro b
  have hm' : Measurable (fun u => g (b,u)) := hg.comp measurable_prodMk_left
  rw [skewTransport_apply, Measure.map_apply hm'
    (measurable_prodMk_left hs)]
  rfl

variable [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace V] [Nonempty V]

/-- A single conull set gives equality of the full conditional measures under
jointly measurable skew changes of leaf coordinates. -/
theorem condKernel_map_skew (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    (f : B ≃ᵐ C) (g : B × U → V) (hg : Measurable g) :
    ∀ᵐ b ∂ρ.fst, (ρ.map (fun p => (f p.1, g p))).condKernel (f b) =
      (ρ.condKernel b).map (fun u => g (b,u)) := by
  have hd : (ρ.map (fun p => (f p.1, g p))).fst ⊗ₘ
      skewTransport f ρ.condKernel g hg = ρ.map (fun p => (f p.1,g p)) := by
    rw [fst_map_skew ρ f g hg, compProd_skewTransport _ _ f g hg, Measure.disintegrate]
  have hh := eq_condKernel_of_measure_eq_compProd _ hd.symm
  rw [fst_map_skew ρ f g hg] at hh
  have hh' := ae_of_ae_map f.measurable.aemeasurable hh
  filter_upwards [hh'] with b hb
  exact hb.symm.trans (skewTransport_apply f ρ.condKernel g hg b)

end VV.BBEKLeafwiseKernel
