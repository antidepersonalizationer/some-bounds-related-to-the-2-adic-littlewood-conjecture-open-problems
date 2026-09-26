import VV.BBEKLeafEntropyRefinement

/-!
# Conditional laws of the constructed codes in actual quotient charts

The leaf-neighborhood property is transported from the quotient to the genuine
chart pullback. This proves positive code-fiber mass and the normalized
restriction formula for the same conditional kernel used by local root measures.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped Topology ENNReal ProbabilityTheory
namespace VV.BBEKLeafEntropyChartConditionals
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKLocalRootFamily BBEKLeafEntropyRefinement
  BBEKLeafEntropySubordinate BBEKLeafEntropySubordinateCharts
  BBEKLeafEntropySubordinateTime BBEKRootLeafKernel

variable {B U Y : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]
  [MeasurableSpace Y] [StandardBorelSpace Y]

def chartPoint (s : GroupParams ≃ₜ B × U) (c : Chart) (p : B × U) : X :=
  quotientCoordinates c.base (s.symm p)

theorem measurable_chartPoint (s : GroupParams ≃ₜ B × U) (c : Chart) :
    Measurable (chartPoint s c) :=
  (continuous_quotientCoordinates c.base).measurable.comp s.symm.measurable

theorem map_split_coordinateMeasure (s : GroupParams ≃ₜ B × U)
    (μ : Measure X) (c : Chart) :
    ((coordinateMeasureOf μ c).map s).map (chartPoint s c) = μ.restrict c.image := by
  rw [Measure.map_map (measurable_chartPoint s c) s.measurable]
  have he : chartPoint s c ∘ s = quotientCoordinates c.base := by
    funext p
    simp only [chartPoint,Function.comp_apply,Homeomorph.symm_apply_apply]
  rw [he]
  exact map_localCoordinateMeasure μ c.base c.isOpen_domain c.embedding

omit [MeasurableSpace B] [BorelSpace B] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U] [MeasurableSpace Y] [StandardBorelSpace Y] in
theorem chartPoint_shift (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (c : Chart) (p : B × U) (u : U) :
    chartPoint s c (p.1,u+p.2) = x (axis u).1 (axis u).2 • chartPoint s c p := by
  have he : s.symm (p.1,u+p.2) = leafShift (s.symm p) (axis u) := by
    apply s.injective
    simp only [Homeomorph.apply_symm_apply,hs]
  unfold chartPoint
  rw [he,quotient_leafShift]

theorem ae_chartCode_local_const (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) (F : X → Y)
    (hlocal : ∀ᵐ q ∂μ, ∃ ε : ℝ, 0 < ε ∧ ∀ u : U, ‖u‖ < ε →
      F (x (axis u).1 (axis u).2 • q) = F q) :
    ∀ᵐ p ∂(coordinateMeasureOf μ c).map s, ∃ ε : ℝ, 0 < ε ∧
      ∀ v : U, dist v p.2 < ε → F (chartPoint s c (p.1,v)) = F (chartPoint s c p) := by
  have hq := ae_restrict_of_ae (s := c.image) hlocal
  rw [← map_split_coordinateMeasure s μ c] at hq
  have hp := ae_of_ae_map (measurable_chartPoint s c).aemeasurable hq
  filter_upwards [hp] with p hp
  obtain ⟨ε,hε,hεgood⟩ := hp
  refine ⟨ε,hε,?_⟩
  intro v hv
  have he := chartPoint_shift s axis hs c p (v-p.2)
  simp only [sub_add_cancel] at he
  rw [he]
  exact hεgood (v-p.2) (by simpa only [dist_eq_norm] using hv)

/-- For an actual locally root-constant code, the refined conditional kernel
is proved to be the normalized restriction of the actual chart leaf kernel. -/
theorem chartCode_conditional_eq (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) {F : X → Y} (hF : Measurable F)
    (hlocal : ∀ᵐ q ∂μ, ∃ ε : ℝ, 0 < ε ∧ ∀ u : U, ‖u‖ < ε →
      F (x (axis u).1 (axis u).2 • q) = F q) :
    let ρ := (coordinateMeasureOf μ c).map s
    let f := F ∘ chartPoint s c
    ∀ᵐ p ∂ρ, 0 < ρ.condKernel p.1 (codeFiber (f := f) p.1 (f p)) ∧
      (refinedMeasure ρ f).condKernel (p.1,f p) =
        (ρ.condKernel p.1 (codeFiber (f := f) p.1 (f p)))⁻¹ •
          (ρ.condKernel p.1).restrict (codeFiber (f := f) p.1 (f p)) := by
  dsimp only
  have hf := hF.comp (measurable_chartPoint s c)
  have hp := codeMass_pos_of_ae_local_const ((coordinateMeasureOf μ c).map s)
    (F ∘ chartPoint s c) (ae_chartCode_local_const s axis hs μ c F hlocal)
  have he := refined_condKernel_eq_normalized_restrict ((coordinateMeasureOf μ c).map s) hf
    (hp.mono (fun p h => ne_of_gt h))
  filter_upwards [hp,he] with p hp he
  exact ⟨hp,he⟩

end VV.BBEKLeafEntropyChartConditionals
