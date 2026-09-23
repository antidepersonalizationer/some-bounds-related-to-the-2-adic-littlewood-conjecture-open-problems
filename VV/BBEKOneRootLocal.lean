import VV.BBEKRootLeafKernel
import VV.BBEKLocalRootFamily

/-! Actual centered one-dimensional root conditional measures in every
quotient chart. The unused matrix factor belongs to the transverse space;
these are conditional measures, not marginals of the joint lower measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKOneRootLocal
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKLocalRootFamily
  BBEKRootLeafKernel
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

section Center
variable {B U : Type*} [MeasurableSpace B] [NormedAddCommGroup U]
  [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]

def centeredKernel (κ : Kernel B U) [IsSFiniteKernel κ] : Kernel (B × U) U where
  toFun p := (κ p.1).map (fun v => v-p.2)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hm (p : B × U) : Measurable (fun v : U => v-p.2) :=
      measurable_id.sub measurable_const
    change Measurable (fun p : B × U => ((κ p.1).map (fun v => v-p.2)) s)
    simp_rw [Measure.map_apply (hm _) hs]
    let κ' : Kernel (B × U) U := κ.comap Prod.fst measurable_fst
    exact Kernel.measurable_kernel_prodMk_left (κ := κ')
      (hs.preimage (measurable_snd.sub measurable_fst.snd))

instance centeredKernel_markov (κ : Kernel B U) [IsMarkovKernel κ] :
    IsMarkovKernel (centeredKernel κ) :=
  ⟨fun p => isProbabilityMeasure_map (measurable_id.sub_const p.2).aemeasurable⟩

theorem centeredKernel_ball (κ : Kernel B U) [IsSFiniteKernel κ]
    (p : B × U) (ε : ℝ) : centeredKernel κ p (ball 0 ε)=κ p.1 (ball p.2 ε) := by
  change (κ p.1).map (fun v => v-p.2) (ball 0 ε)=_
  have hm : Measurable (fun v : U => v-p.2) := measurable_id.sub measurable_const
  rw [Measure.map_apply hm (isOpen_ball.measurableSet : MeasurableSet (ball (0 : U) ε))]
  congr 1
  ext v
  simp [mem_ball,dist_eq_norm]

theorem centeredKernel_ae_pos [StandardBorelSpace U]
    (ρ : Measure (B × U)) [IsFiniteMeasure ρ] :
    ∀ᵐ p ∂ρ, ∀ ε : ℝ, 0 < ε → 0 < centeredKernel ρ.condKernel p (ball 0 ε) := by
  simpa only [centeredKernel_ball] using condKernel_ae_all_ball_pos ρ
end Center

section Local
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]

def localMeasureWith (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : Chart) (q : X) : Measure U :=
  centeredKernel ((coordinateMeasureOf μ c).map s).condKernel
    (s (chartCoordinates c q))

theorem measurable_localMeasureWith (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : Chart) : Measurable (localMeasureWith s μ c) :=
  (centeredKernel ((coordinateMeasureOf μ c).map s).condKernel).measurable.comp
    (s.measurable.comp (measurable_chartCoordinates c))

instance localMeasureWith_probability (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : Chart) (q : X) : IsProbabilityMeasure (localMeasureWith s μ c q) := by
  unfold localMeasureWith
  infer_instance

theorem ae_localMeasureWith_ball_pos (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : Chart) :
    ∀ᵐ q ∂μ.restrict c.image, ∀ ε : ℝ, 0 < ε → 0 < localMeasureWith s μ c q (ball 0 ε) := by
  have hg := centeredKernel_ae_pos ((coordinateMeasureOf μ c).map s)
  have hg₁ := ae_of_ae_map s.measurable.aemeasurable hg
  have hg₂ := ae_of_ae_map measurable_subtype_coe.aemeasurable hg₁
  have hm : (μ.comap (c.domain.restrict (quotientCoordinates c.base))).map
      (c.domain.restrict (quotientCoordinates c.base)) = μ.restrict c.image := by
    rw [c.embedding.measurableEmbedding.map_comap,Set.range_restrict]
    rfl
  rw [← hm]
  apply c.embedding.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hg₂] with p hp
  change ∀ ε : ℝ, 0 < ε → 0 < centeredKernel
    ((coordinateMeasureOf μ c).map s).condKernel
      (s (chartCoordinates c (quotientCoordinates c.base p.val))) (ball 0 ε)
  rw [chartCoordinates_apply]
  exact hp
end Local

def realLocalMeasure (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) : X → Measure ℝ :=
  localMeasureWith realSplit μ c

def padicLocalMeasure (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) : X → Measure Q2 :=
  localMeasureWith padicSplit μ c

theorem measurable_realLocalMeasure (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    Measurable (realLocalMeasure μ c) := measurable_localMeasureWith realSplit μ c

theorem measurable_padicLocalMeasure (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    Measurable (padicLocalMeasure μ c) := measurable_localMeasureWith padicSplit μ c

theorem ae_realLocalMeasure_ball_pos (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    ∀ᵐ q ∂μ.restrict c.image, ∀ ε : ℝ, 0 < ε → 0 < realLocalMeasure μ c q (ball 0 ε) :=
  ae_localMeasureWith_ball_pos realSplit μ c

theorem ae_padicLocalMeasure_ball_pos (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    ∀ᵐ q ∂μ.restrict c.image, ∀ ε : ℝ, 0 < ε → 0 < padicLocalMeasure μ c q (ball 0 ε) :=
  ae_localMeasureWith_ball_pos padicSplit μ c

end VV.BBEKOneRootLocal
