import VV.Entropy.FiniteProbabilityApprox
import VV.Entropy.OrbitMixture
import VV.Entropy.BowenSemicontinuity
import Mathlib.MeasureTheory.Measure.Prod

/-! Continuous compact families of commuting embeddings: their actual product
measure average retains entropy by finite quantization and upper semicontinuity. -/

noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology ENNReal NNReal
namespace ErgodicTheory.Entropy

variable {K Y I : Type*} [MeasurableSpace K] [MeasurableSpace Y]

def probabilityProduct (κ : ProbabilityMeasure K) (μ : ProbabilityMeasure Y) :
    ProbabilityMeasure (K × Y) := ⟨(κ : Measure K).prod (μ : Measure Y), inferInstance⟩

def familyAverage {F : K × Y → Y} (hF : Measurable F)
    (κ : ProbabilityMeasure K) (μ : ProbabilityMeasure Y) : ProbabilityMeasure Y :=
  (probabilityProduct κ μ).map hF.aemeasurable

theorem familyAverage_quantize_eq_mixture [Fintype I]
    {F : K × Y → Y} (hF : Measurable F)
    (κ : ProbabilityMeasure K) (μ : ProbabilityMeasure Y)
    (P : FixedPartition K I) (p : I → K) :
    familyAverage hF (κ.map (P.measurable_quantize p).aemeasurable) μ =
      probabilityMixture (P.weight κ) (P.weight_sum κ)
        (fun i => μ.map (hF.comp (measurable_const.prodMk measurable_id) : Measurable (fun y => F (p i,y))).aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map F ((Measure.map (P.quantize p) (κ : Measure K)).prod (μ : Measure Y)) = _
  rw [P.map_quantize, ← Measure.sum_fintype, Measure.prod_sum_left,
    Measure.map_sum hF.aemeasurable, Measure.sum_fintype]
  change (∑ i, Measure.map F (((P.weight κ i : ℝ≥0∞) • Measure.dirac (p i)).prod
    (μ : Measure Y))) = ∑ i, (P.weight κ i : ℝ≥0∞) • _
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
    Measure.map_map hF measurable_prodMk_left]
  rfl

theorem familyAverage_quantize_eq_map
    {F : K × Y → Y} (hF : Measurable F)
    (κ : ProbabilityMeasure K) (μ : ProbabilityMeasure Y)
    {q : K → K} (hq : Measurable q) :
    familyAverage hF (κ.map hq.aemeasurable) μ =
      (probabilityProduct κ μ).map (hF.comp (hq.prodMap measurable_id)).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map F ((Measure.map q (κ : Measure K)).prod (μ : Measure Y)) = _
  rw [← Measure.map_id (μ := (μ : Measure Y)), Measure.map_prod_map _ _ hq measurable_id,
    Measure.map_map hF (hq.prodMap measurable_id)]
  rfl

theorem familyAverage_measurePreserving
    {F : K × Y → Y} (hF : Measurable F)
    (κ : ProbabilityMeasure K) (μ : ProbabilityMeasure Y)
    {T : Y → Y} (hT : MeasurePreserving T (μ : Measure Y) (μ : Measure Y))
    (hc : ∀ k, Function.Commute (fun y => F (k,y)) T) :
    MeasurePreserving T (familyAverage hF κ μ : Measure Y)
      (familyAverage hF κ μ : Measure Y) := by
  refine ⟨hT.measurable,?_⟩
  change Measure.map T (Measure.map F ((κ : Measure K).prod (μ : Measure Y))) = _
  rw [Measure.map_map hT.measurable hF]
  have he : T ∘ F = F ∘ Prod.map id T := by
    funext p; exact (hc p.1 p.2).symm
  rw [he, ← Measure.map_map hF (measurable_id.prodMap hT.measurable),
    ← Measure.map_prod_map _ _ measurable_id hT.measurable, Measure.map_id, hT.map_eq]
  rfl

section Topological
variable [MetricSpace K] [BorelSpace K] [CompactSpace K]
  [MetricSpace Y] [BorelSpace Y] [CompactSpace Y]

theorem le_ksEntropy_familyAverage
    {F : K × Y → Y} (hF : Continuous F)
    (κ : ProbabilityMeasure K) (μ : ProbabilityMeasure Y)
    {T : Y → Y} (hcont : Continuous T)
    (hT : MeasurePreserving T (μ : Measure Y) (μ : Measure Y))
    (hEmb : ∀ k, MeasurableEmbedding (fun y => F (k,y)))
    (hc : ∀ k, Function.Commute (fun y => F (k,y)) T)
    {r : ℝ} (hr : 0 < r) (hcover : UniformBowenCover T r)
    {c : ℝ} (hbound : (c : EReal) ≤ ksEntropy hT) :
    (c : EReal) ≤ ksEntropy (familyAverage_measurePreserving hF.measurable κ μ hT hc) := by
  classical
  obtain ⟨m,P,p,hq⟩ := exists_finite_quantizations κ
  let κn (n : ℕ) := κ.map ((P n).measurable_quantize (p n)).aemeasurable
  have hlim : Tendsto (fun n => familyAverage hF.measurable (κn n) μ) atTop
      (𝓝 (familyAverage hF.measurable κ μ)) := by
    simp_rw [κn, familyAverage_quantize_eq_map hF.measurable κ μ
      ((P _).measurable_quantize (p _))]
    change Tendsto _ atTop (𝓝 ((probabilityProduct κ μ).map hF.measurable.aemeasurable))
    apply probability_map_tendsto_of_pointwise (probabilityProduct κ μ)
      (fun n => hF.measurable.comp (((P n).measurable_quantize (p n)).prodMap measurable_id))
      hF.measurable
    intro z
    exact hF.continuousAt.tendsto.comp ((hq z.1).prodMk_nhds
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z.2) atTop (𝓝 z.2)))
  apply le_ksEntropy_of_tendsto_of_uniformBowenCover hcont hr hcover hlim
    (familyAverage_measurePreserving hF.measurable κ μ hT hc)
    (fun n => familyAverage_measurePreserving hF.measurable (κn n) μ hT hc)
  apply Filter.Eventually.of_forall
  intro n
  have he := familyAverage_quantize_eq_mixture hF.measurable κ μ (P n) (p n)
  let ν (i : Fin (m n)) := μ.map (hEmb (p n i)).measurable.aemeasurable
  let hν (i : Fin (m n)) := measurePreserving_map_commute μ hT (hEmb (p n i)).measurable (hc _)
  rw [ksEntropy_eq_of_probability_eq he _
    (probabilityMixture_measurePreserving _ _ ν hT.measurable hν)]
  apply ksEntropy_mixture_ge _ _ ν hT.measurable hν
  intro i
  exact hbound.trans_eq (ksEntropy_map_commuting_embedding μ hT (hEmb _) (hc _)).symm

/-- The full extended-real entropy inequality, including infinite entropy. -/
theorem ksEntropy_le_familyAverage
    {F : K × Y → Y} (hF : Continuous F)
    (κ : ProbabilityMeasure K) (μ : ProbabilityMeasure Y)
    {T : Y → Y} (hcont : Continuous T)
    (hT : MeasurePreserving T (μ : Measure Y) (μ : Measure Y))
    (hEmb : ∀ k, MeasurableEmbedding (fun y => F (k,y)))
    (hc : ∀ k, Function.Commute (fun y => F (k,y)) T)
    {r : ℝ} (hr : 0 < r) (hcover : UniformBowenCover T r) :
    ksEntropy hT ≤ ksEntropy (familyAverage_measurePreserving hF.measurable κ μ hT hc) := by
  by_contra hnot
  obtain ⟨c,hc₁,hc₂⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
  exact (not_le_of_gt hc₁)
    (le_ksEntropy_familyAverage hF κ μ hcont hT hEmb hc hr hcover hc₂.le)

end Topological
end ErgodicTheory.Entropy

