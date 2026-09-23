import VV.BBEKOneRootLocal
import VV.BBEKLocalDiagonalCovariance

/-! Diagonal covariance of genuine separate-root local conditional
probabilities. The other full matrix factor remains transverse. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKOneRootLocalDiagonal
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKExpandedPlaques
  BBEKLocalRootFamily BBEKRootLeafKernel BBEKOneRootLocal BBEKLocalDiagonalCovariance

section General
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]

theorem ae_localMeasureWith_translate
    (s : GroupParams ≃ₜ B × U) (β : B ≃ₜ B) (σ : U ≃ₜ U)
    (hσ : ∀ u v : U, σ (u-v)=σ u-σ v)
    (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) (t : ℝ) (n : ℤ)
    (hcoords : ∀ p : GroupParams, s (psiParams t n p)=Prod.map β σ (s p))
    (hA : MeasurePreserving (fun q : X => psi t n • q) μ μ) :
    ∀ᵐ q ∂μ.restrict c.image,
      localMeasureWith s μ (translateChart c t n) (psi t n • q)=
        (localMeasureWith s μ c q).map σ := by
  let ρ := (coordinateMeasureOf μ c).map s
  have hmeasure : (coordinateMeasureOf μ (translateChart c t n)).map s =
      ρ.map (Prod.map β σ) := by
    rw [coordinateMeasureOf_translate μ c t n hA]
    dsimp only [ρ]
    rw [Measure.map_map s.measurable (measurable_psiParams t n),
      Measure.map_map (β.measurable.prodMap σ.measurable) s.measurable]
    congr 1
    funext p
    exact hcoords p
  have hκ := condKernel_map_prod ρ β.toMeasurableEquiv σ.measurable
  change ∀ᵐ b ∂ρ.fst, (ρ.map (Prod.map β σ)).condKernel (β b) =
    (ρ.condKernel b).map σ at hκ
  rw [← condKernel_congr hmeasure] at hκ
  have hpoint := ae_of_ae_map measurable_fst.aemeasurable hκ
  have hparams := ae_of_ae_map s.measurable.aemeasurable hpoint
  have hsub := ae_of_ae_map measurable_subtype_coe.aemeasurable hparams
  have hmap : (μ.comap (c.domain.restrict (quotientCoordinates c.base))).map
      (c.domain.restrict (quotientCoordinates c.base)) = μ.restrict c.image := by
    rw [c.embedding.measurableEmbedding.map_comap,Set.range_restrict]
    rfl
  rw [← hmap]
  apply c.embedding.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hsub] with p hp
  unfold localMeasureWith
  dsimp only [Set.restrict]
  rw [chartCoordinates_translate,chartCoordinates_apply,hcoords]
  change (((coordinateMeasureOf μ (translateChart c t n)).map s).condKernel (β (s p.val).1)).map
      (fun v : U => v-σ (s p.val).2) =
    ((ρ.condKernel (s p.val).1).map (fun v : U => v-(s p.val).2)).map σ
  rw [hp]
  have hc₁ : Measurable (fun v : U => v-σ (s p.val).2) := measurable_id.sub measurable_const
  have hc₂ : Measurable (fun v : U => v-(s p.val).2) := measurable_id.sub measurable_const
  rw [Measure.map_map hc₁ σ.measurable,Measure.map_map σ.measurable hc₂]
  congr 1
  funext v
  exact (hσ v (s p.val).2).symm
end General

theorem ae_realLocalMeasure_translate (μ : Measure X) [IsFiniteMeasure μ]
    (c : Chart) (t : ℝ) (n : ℤ)
    (hA : MeasurePreserving (fun q : X => psi t n • q) μ μ) :
    ∀ᵐ q ∂μ.restrict c.image,
      realLocalMeasure μ (translateChart c t n) (psi t n • q)=
        (realLocalMeasure μ c q).map (realLeafScaling t) :=
  ae_localMeasureWith_translate realSplit (realTransverseScaling t n) (realLeafScaling t)
    (fun u v => by simp [realLeafScaling,mul_sub]) μ c t n (realSplit_psiParams t n) hA

theorem ae_padicLocalMeasure_translate (μ : Measure X) [IsFiniteMeasure μ]
    (c : Chart) (t : ℝ) (n : ℤ)
    (hA : MeasurePreserving (fun q : X => psi t n • q) μ μ) :
    ∀ᵐ q ∂μ.restrict c.image,
      padicLocalMeasure μ (translateChart c t n) (psi t n • q)=
        (padicLocalMeasure μ c q).map (padicLeafScaling n) :=
  ae_localMeasureWith_translate padicSplit (padicTransverseScaling t n) (padicLeafScaling n)
    (fun u v => by simp [padicLeafScaling,mul_sub]) μ c t n (padicSplit_psiParams t n) hA

end VV.BBEKOneRootLocalDiagonal


