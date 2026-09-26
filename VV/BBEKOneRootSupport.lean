import VV.BBEKOneRootLocalInvariance

/-! Support of the actual centered conditional root measures, and of their
canonical growing-ball extensions. No invariance of the leaf measure is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Function
open scoped Topology ENNReal
namespace VV.BBEKOneRootSupport
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
open BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKExpandedPlaques
open BBEKLocalRootFamily BBEKRootLeafKernel BBEKOneRootLocal BBEKSelectedPlaques
open BBEKRootGrowingGlue BBEKOneRootGlobal BBEKOneRootCovariance

section General
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]

/-- Disintegration and recentering preserve the support of the actual chart measure. -/
theorem local_supported (s : GroupParams ≃ₜ B × U) (root : U → G)
    (hroot : Continuous root)
    (hcoords : ∀ b u v, groupMatrixOf (s.symm (b,v+u)) =
      root v * groupMatrixOf (s.symm (b,u)))
    (μ : Measure X) [IsFiniteMeasure μ] (c : Chart)
    {K : Set X} (hK : MeasurableSet K) (hμK : ∀ᵐ q ∂μ, q ∈ K) :
    ∀ᵐ q ∂μ.restrict c.image, ∀ᵐ u ∂localMeasureWith s μ c q, root u • q ∈ K := by
  let ρ := (coordinateMeasureOf μ c).map s
  let F : B × U → X := quotientCoordinates c.base ∘ s.symm
  have hF : Continuous F := (continuous_quotientCoordinates c.base).comp s.symm.continuous
  have hmapF : ρ.map F = μ.restrict c.image := by
    dsimp only [ρ]
    rw [Measure.map_map hF.measurable s.measurable]
    have he : F ∘ s = quotientCoordinates c.base := by
      funext p
      simp [F]
    rw [he]
    exact map_localCoordinateMeasure μ c.base c.isOpen_domain c.embedding
  have hρ : ∀ᵐ p ∂ρ, F p ∈ K :=
    ae_of_ae_map hF.measurable.aemeasurable (hmapF.symm ▸ ae_restrict_of_ae hμK)
  have hκ : ∀ᵐ b ∂ρ.fst, ∀ᵐ v ∂ρ.condKernel b, F (b,v) ∈ K := by
    apply (Measure.ae_compProd_iff (hK.preimage hF.measurable)).mp
    rwa [Measure.disintegrate]
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
  rw [chartCoordinates_apply]
  change ∀ᵐ u ∂(ρ.condKernel (s p.val).1).map (fun v => v-(s p.val).2),
    root u • quotientCoordinates c.base p.val ∈ K
  apply (ae_map_iff (measurable_id.sub_const _).aemeasurable
    (hK.preimage (hroot.smul continuous_const).measurable)).mpr
  filter_upwards [hp] with v hv
  have he : root (v-(s p.val).2) • quotientCoordinates c.base p.val = F ((s p.val).1,v) := by
    have hc := hcoords (s p.val).1 (s p.val).2 (v-(s p.val).2)
    rw [sub_add_cancel] at hc
    simp only [Prod.mk.eta,s.symm_apply_apply] at hc
    simp only [F,Function.comp_apply,quotientCoordinates,smul_mk,hc,mul_assoc]
  change root (v-(s p.val).2) • quotientCoordinates c.base p.val ∈ K
  rwa [he]

variable [SigmaCompactSpace U]

/-- The exact canonical restrictions transfer support to the whole leaf. -/
theorem canonical_supported (s : GroupParams ≃ₜ B × U) (root : U → G)
    (hroot : Continuous root)
    (hcoords : ∀ b u v, groupMatrixOf (s.symm (b,v+u)) =
      root v * groupMatrixOf (s.symm (b,u)))
    (μ : Measure X) [IsFiniteMeasure μ] {K : Set X}
    (hK : MeasurableSet K) (hμK : ∀ᵐ q ∂μ, q ∈ K)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure U)
    (hcanonical : IsConstructedRootFamily s μ t r η) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂η q, root u • q ∈ K := by
  obtain ⟨c,index,hi,hη,hres⟩ := hcanonical
  have hall : ∀ᵐ q ∂μ, ∀ n k : ℕ,
      q ∈ (expandedChart (c k) t n).image →
      ∀ᵐ u ∂localMeasureWith s μ (expandedChart (c k) t n) q, root u • q ∈ K := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact (ae_restrict_iff' (Chart.isOpen_image _).measurableSet).mp
      (local_supported s root hroot hcoords μ _ hK hμK)
  filter_upwards [hall,hres] with q hq hqr
  have hn : ∀ n : ℕ, ∀ᵐ u ∂(η q).restrict (growingBall r n), root u • q ∈ K := by
    intro n
    rw [(hqr n).1]
    apply Measure.ae_smul_measure
    apply ae_restrict_of_ae
    exact hq n (index (((psi t 1)⁻¹)^n • q)) (hqr n).2.1
  have hh := (ae_restrict_iUnion_iff (growingBall (U := U) r)
    (fun u => root u • q ∈ K)).mpr hn
  simpa only [growingBall_cover hr,Measure.restrict_univ] using hh
end General

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem canonical_real_lower_supported (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : MeasurableSet K) (hμK : μ K = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ)
    (hcanonical : IsConstructedRootFamily realSplit μ t r η) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂η q, x u 0 • q ∈ K :=
  canonical_supported realSplit (fun u => x u 0)
    (continuous_x.comp (continuous_id.prodMk continuous_const)) realMatrix_leaf_add
    μ hK ((mem_ae_iff_prob_eq_one hK).mpr hμK) hr η hcanonical

theorem canonical_padic_lower_supported (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : MeasurableSet K) (hμK : μ K = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2)
    (hcanonical : IsConstructedRootFamily padicSplit μ t r η) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂η q, x 0 u • q ∈ K :=
  canonical_supported padicSplit (fun u => x 0 u)
    (continuous_x.comp (continuous_const.prodMk continuous_id)) padicMatrix_leaf_add
    μ hK ((mem_ae_iff_prob_eq_one hK).mpr hμK) hr η hcanonical




open BBEKRootWeyl BBEKOneRootUpper BBEKMautner

/-- Weyl transport preserves the support assertion, including its parameter sign. -/
theorem upper_support_transport {U : Type*} [NormedAddCommGroup U]
    [MeasurableSpace U] [BorelSpace U]
    (root rootUp : U → G)
    (hconj : ∀ (u : U) (q : X), W⁻¹ • (rootUp u • q) = root (-u) • (W⁻¹ • q))
    (μ : Measure X) (η : X → Measure U) {K : Set X}
    (hη : ∀ᵐ q ∂reflectedMeasure μ, ∀ᵐ u ∂η q,
      root u • q ∈ (fun z : X => W • z) ⁻¹' K) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂upperFamily η q, rootUp u • q ∈ K := by
  have hp := ae_of_ae_map (continuous_const_smul W⁻¹).measurable.aemeasurable hη
  filter_upwards [hp] with q hq
  change ∀ᵐ u ∂(η (W⁻¹ • q)).map (fun u => -u), rootUp u • q ∈ K
  apply (Homeomorph.neg U).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hq] with u hu
  have he := congrArg (fun z : X => W • z) (hconj (-u) q)
  simp only [neg_neg,smul_inv_smul] at he
  change W • (root u • (W⁻¹ • q)) ∈ K at hu
  exact he.symm ▸ hu

/-- The reflected full-mass set is a literal inverse image; compactness is unnecessary. -/
theorem reflected_preimage_mass (μ : Measure X) {K : Set X}
    (hK : MeasurableSet K) (hμK : μ K = 1) :
    reflectedMeasure μ ((fun z : X => W • z) ⁻¹' K) = 1 := by
  rw [reflectedMeasure,Measure.map_apply (continuous_const_smul _).measurable
    (hK.preimage (continuous_const_smul _).measurable)]
  have he : (fun q : X => W⁻¹ • q) ⁻¹' ((fun z : X => W • z) ⁻¹' K) = K := by
    ext q
    simp only [mem_preimage,smul_inv_smul]
  rwa [he]

theorem canonical_real_upper_supported (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : MeasurableSet K) (hμK : μ K = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ)
    (hcanonical : IsConstructedUpperRootFamily realSplit μ t r η) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂η q, upperPoint u 0 • q ∈ K := by
  obtain ⟨η₀,hη₀,rfl⟩ := hcanonical
  apply upper_support_transport (fun u => x u 0) (fun u => upperPoint u 0)
    (fun u q => by simpa only [neg_zero] using inverse_W_upper_action u 0 q)
  exact canonical_real_lower_supported (reflectedMeasure μ)
    (hK.preimage (continuous_const_smul W).measurable)
    (reflected_preimage_mass μ hK hμK) hr η₀ hη₀

theorem canonical_padic_upper_supported (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : MeasurableSet K) (hμK : μ K = 1)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2)
    (hcanonical : IsConstructedUpperRootFamily padicSplit μ t r η) :
    ∀ᵐ q ∂μ, ∀ᵐ u ∂η q, upperPoint 0 u • q ∈ K := by
  obtain ⟨η₀,hη₀,rfl⟩ := hcanonical
  apply upper_support_transport (fun u => x 0 u) (fun u => upperPoint 0 u)
    (fun u q => by simpa only [neg_zero] using inverse_W_upper_action 0 u q)
  exact canonical_padic_lower_supported (reflectedMeasure μ)
    (hK.preimage (continuous_const_smul W).measurable)
    (reflected_preimage_mass μ hK hμK) hr η₀ hη₀

end VV.BBEKOneRootSupport


