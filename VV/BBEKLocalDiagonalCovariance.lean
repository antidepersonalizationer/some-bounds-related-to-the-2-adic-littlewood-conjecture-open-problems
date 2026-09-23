import VV.BBEKGlobalLowerMeasure

/-! Exact diagonal covariance of the actual quotient-chart pullbacks and
their centered conditional kernels, using invariance of the original measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLocalDiagonalCovariance
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques
  BBEKExpandedPlaques BBEKLocalRootFamily

def chartScaling (c : Chart) (t : ℝ) (n : ℤ) :
    c.domain ≃ₜ (translateChart c t n).domain :=
  (paramsHomeomorph t n).image c.domain

theorem chartScaling_quotient (c : Chart) (t : ℝ) (n : ℤ) :
    (translateChart c t n).domain.restrict
        (quotientCoordinates (translateChart c t n).base) ∘ chartScaling c t n =
      (fun q : X => psi t n • q) ∘ c.domain.restrict (quotientCoordinates c.base) := by
  funext p
  exact quotient_diagonal_params c t n p

/-- Pulling the invariant quotient measure back through the translated chart
is exactly the coordinate pushforward of its original chart pullback. -/
theorem coordinateMeasureOf_translate (μ : Measure X) (c : Chart) (t : ℝ) (n : ℤ)
    (hA : MeasurePreserving (fun q : X => psi t n • q) μ μ) :
    coordinateMeasureOf μ (translateChart c t n) =
      (coordinateMeasureOf μ c).map (psiParams t n) := by
  let d := translateChart c t n
  let e := chartScaling c t n
  let A : X ≃ₜ X := Homeomorph.smul (psi t n)
  have ha : μ.comap A = μ := by
    calc
      μ.comap A = (μ.map A).comap A := by
        have he : μ.map A = μ := hA.map_eq
        rw [he]
      _ = μ := A.measurableEmbedding.comap_map μ
  have hcomp : (μ.comap (d.domain.restrict (quotientCoordinates d.base))).comap e =
      μ.comap (c.domain.restrict (quotientCoordinates c.base)) := by
    rw [Measure.comap_comap (fun _ hs => e.measurableEmbedding.measurableSet_image' hs)
      d.embedding.injective (fun _ hs => d.embedding.measurableEmbedding.measurableSet_image' hs),
      chartScaling_quotient]
    change μ.comap (A ∘ c.domain.restrict (quotientCoordinates c.base)) = _
    rw [← Measure.comap_comap
      (fun _ hs => c.embedding.measurableEmbedding.measurableSet_image' hs)
      A.injective (fun _ hs => A.measurableEmbedding.measurableSet_image' hs),ha]
  have hsub : μ.comap (d.domain.restrict (quotientCoordinates d.base)) =
      (μ.comap (c.domain.restrict (quotientCoordinates c.base))).map e := by
    rw [← hcomp,e.measurableEmbedding.map_comap,e.surjective.range_eq,Measure.restrict_univ]
  change (μ.comap (d.domain.restrict (quotientCoordinates d.base))).map Subtype.val = _
  rw [hsub,Measure.map_map measurable_subtype_coe e.measurable]
  unfold coordinateMeasureOf localCoordinateMeasure
  rw [Measure.map_map (measurable_psiParams t n) measurable_subtype_coe]
  rfl

/-- The point coordinates transform by the actual diagonal parameter map. -/
theorem chartCoordinates_translate (c : Chart) (t : ℝ) (n : ℤ) (p : c.domain) :
    chartCoordinates (translateChart c t n) (psi t n • quotientCoordinates c.base p) =
      psiParams t n p := by
  rw [← quotient_diagonal_params]
  exact chartCoordinates_apply _ (chartScaling c t n p)

/-- Exact covariance of centered local leaf probabilities on each actual
chart. Invariance is a property of the given quotient measure, not a supplied
conditional-kernel identity. -/
theorem ae_localMeasure_translate (μ : Measure X) [IsFiniteMeasure μ]
    (c : Chart) (t : ℝ) (n : ℤ)
    (hA : MeasurePreserving (fun q : X => psi t n • q) μ μ) :
    ∀ᵐ q ∂μ.restrict c.image,
      localMeasure μ (translateChart c t n) (psi t n • q) =
        (localMeasure μ c q).map (leafScaling t n) := by
  have hκ := leafKernel_diagonal_covariance (coordinateMeasureOf μ c) t n
  have hκε : leafKernel ((coordinateMeasureOf μ c).map (psiParams t n)) =
      localLeafKernel μ (translateChart c t n) := by
    unfold leafKernel localLeafKernel
    exact condKernel_congr (congrArg coordinateMeasure (coordinateMeasureOf_translate μ c t n hA).symm)
  rw [hκε] at hκ
  have hpoint := ae_of_ae_map measurable_fst.aemeasurable hκ
  have hparams := ae_of_ae_map splitCoordinates.measurable.aemeasurable hpoint
  have hsub := ae_of_ae_map measurable_subtype_coe.aemeasurable hparams
  have hmap : (μ.comap (c.domain.restrict (quotientCoordinates c.base))).map
      (c.domain.restrict (quotientCoordinates c.base)) = μ.restrict c.image := by
    rw [c.embedding.measurableEmbedding.map_comap,Set.range_restrict]
    rfl
  rw [← hmap]
  apply c.embedding.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hsub] with p hp
  unfold localMeasure
  dsimp only [Set.restrict]
  rw [chartCoordinates_translate,chartCoordinates_apply,splitCoordinates_psiParams]
  simp only [centeredLeafKernel_apply,Prod.map_fst,Prod.map_snd]
  change ((localLeafKernel μ (translateChart c t n))
      (transverseScaling t n (splitCoordinates p.val).1)).map
        (fun v => v-leafScaling t n (splitCoordinates p.val).2) = _
  rw [hp]
  have hc₁ : Measurable (fun v : Leaf => v-leafScaling t n (splitCoordinates p.val).2) :=
    measurable_id.sub measurable_const
  have hc₂ : Measurable (fun v : Leaf => v-(splitCoordinates p.val).2) :=
    measurable_id.sub measurable_const
  rw [Measure.map_map hc₁ (leafScaling t n).measurable,
    Measure.map_map (leafScaling t n).measurable hc₂]
  congr 1
  funext v
  apply Prod.ext <;> simp [leafScaling,mul_sub]

end VV.BBEKLocalDiagonalCovariance


