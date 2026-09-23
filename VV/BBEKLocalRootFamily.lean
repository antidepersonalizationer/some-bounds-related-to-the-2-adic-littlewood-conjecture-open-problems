import VV.BBEKPlaqueSelection

/-! Actual measurable centered conditional leaf measures of a quotient
probability in every Gauss chart, with all positive-radius balls positive a.e. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLocalRootFamily
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques

def coordinateMeasureOf (μ : Measure X) (c : Chart) : Measure GroupParams :=
  localCoordinateMeasure μ c.base c.domain

instance coordinateMeasureOf_finite (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    IsFiniteMeasure (coordinateMeasureOf μ c) :=
  localCoordinateMeasure_finite μ c.base c.isOpen_domain c.embedding

def localLeafKernel (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) : Kernel Transverse Leaf :=
  leafKernel (coordinateMeasureOf μ c)

instance localLeafKernel_markov (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    IsMarkovKernel (localLeafKernel μ c) := by unfold localLeafKernel leafKernel; infer_instance

/-- This is a total measurable family, defined using the actual chart pullback
and canonical disintegration; outside the chart image its coordinates are arbitrary. -/
def localMeasure (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) (q : X) : Measure Leaf :=
  centeredLeafKernel (localLeafKernel μ c) (splitCoordinates (chartCoordinates c q))

theorem measurable_localMeasure (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    Measurable (localMeasure μ c) :=
  (centeredLeafKernel (localLeafKernel μ c)).measurable.comp
    (splitCoordinates.measurable.comp (measurable_chartCoordinates c))

instance localMeasure_probability (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) (q : X) :
    IsProbabilityMeasure (localMeasure μ c q) := by
  unfold localMeasure
  infer_instance

/-- The local family is positive on every centered neighborhood on the actual
quotient measure restricted to the chart, simultaneously for all radii. -/
theorem ae_localMeasure_ball_pos (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    ∀ᵐ q ∂μ.restrict c.image, ∀ ε : ℝ, 0 < ε → 0 < localMeasure μ c q (ball 0 ε) := by
  have hg := centeredLeafKernel_ae_pos (coordinateMeasure (coordinateMeasureOf μ c))
  have hg₁ := ae_of_ae_map splitCoordinates.measurable.aemeasurable hg
  have hg₂ := ae_of_ae_map measurable_subtype_coe.aemeasurable hg₁
  have hm : (μ.comap (c.domain.restrict (quotientCoordinates c.base))).map
      (c.domain.restrict (quotientCoordinates c.base)) = μ.restrict c.image := by
    rw [c.embedding.measurableEmbedding.map_comap,Set.range_restrict]
    rfl
  rw [← hm]
  apply c.embedding.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hg₂] with p hp
  change ∀ ε : ℝ, 0 < ε →
    0 < centeredLeafKernel (localLeafKernel μ c)
      (splitCoordinates (chartCoordinates c (quotientCoordinates c.base p.val))) (ball 0 ε)
  rw [chartCoordinates_apply]
  exact hp

end VV.BBEKLocalRootFamily
