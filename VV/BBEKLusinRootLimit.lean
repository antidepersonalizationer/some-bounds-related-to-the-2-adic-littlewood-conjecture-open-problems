import VV.BBEKLusin
import VV.BBEKRootFieldSeparation

/-! The terminal compact-Lusin step: a genuine root limit of paired returns,
whose canonical leaf tests become equal, gives equality of the two limiting
leaf measures. This does not assert the paired-test hypothesis itself. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace VV.BBEKLusinRootLimit

variable {U Z H : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [ProperSpace U] [SecondCountableTopology U]
  [MetricSpace Z] [TopologicalSpace H] [SMul H Z] [ContinuousSMul H Z]

/-- Compactness selects a genuine base-point limit; continuity of the actual
action gives the translated limit. Countable compact-support tests then
identify the two Radon leaf measures. -/
theorem exists_equal_leaf_root_return
    (root : U → H) (η : Z → Measure U) {S : Set Z} (hS : IsCompact S)
    (hreg : ∀ q ∈ S, (η q).Regular)
    (hcont : ∀ j : ℕ, ContinuousOn
      (fun q => ∫ v, BBEKLeafMeasureTests.testFunction j v ∂η q) S)
    {u : U} {g : ℕ → H} (hg : Tendsto g atTop (𝓝 (root u)))
    {p q : ℕ → Z} (hp : ∀ i, p i ∈ S) (hq : ∀ i, q i ∈ S)
    (hrel : ∀ i, p i = g i • q i)
    (htests : ∀ j : ℕ, Tendsto (fun i =>
      (∫ v, BBEKLeafMeasureTests.testFunction j v ∂η (p i)) -
      (∫ v, BBEKLeafMeasureTests.testFunction j v ∂η (q i))) atTop (𝓝 0)) :
    ∃ z ∈ S, root u • z ∈ S ∧ η (root u • z) = η z := by
  obtain ⟨z,hz,φ,hφ,hqφ⟩ := hS.isSeqCompact hq
  have hpφ : Tendsto (p ∘ φ) atTop (𝓝 (root u • z)) := by
    have ht := (hg.comp hφ.tendsto_atTop).smul hqφ
    simpa only [Function.comp_apply,← hrel] using ht
  have hrootz : root u • z ∈ S := hS.isClosed.mem_of_tendsto hpφ
    (Eventually.of_forall fun i => hp (φ i))
  refine ⟨z,hz,hrootz,?_⟩
  letI : (η z).Regular := hreg z hz
  letI : (η (root u • z)).Regular := hreg _ hrootz
  apply BBEKLeafMeasureTests.ext_of_test_integrals
  intro j
  have hpwithin : Tendsto (p ∘ φ) atTop (𝓝[S] (root u • z)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpφ,Eventually.of_forall fun i => hp (φ i)⟩
  have hqwithin : Tendsto (q ∘ φ) atTop (𝓝[S] z) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqφ,Eventually.of_forall fun i => hq (φ i)⟩
  have hptest := (hcont j _ hrootz).tendsto.comp hpwithin
  have hqtest := (hcont j z hz).tendsto.comp hqwithin
  have he := tendsto_nhds_unique (hptest.sub hqtest)
    ((htests j).comp hφ.tendsto_atTop)
  exact sub_eq_zero.mp he

/-- Actual equality along the returning pairs implies the preceding test
hypothesis, without any weak-convergence assumption on infinite measures. -/
theorem exists_equal_leaf_root_return_of_eq
    (root : U → H) (η : Z → Measure U) {S : Set Z} (hS : IsCompact S)
    (hreg : ∀ q ∈ S, (η q).Regular)
    (hcont : ∀ j : ℕ, ContinuousOn
      (fun q => ∫ v, BBEKLeafMeasureTests.testFunction j v ∂η q) S)
    {u : U} {g : ℕ → H} (hg : Tendsto g atTop (𝓝 (root u)))
    {p q : ℕ → Z} (hp : ∀ i, p i ∈ S) (hq : ∀ i, q i ∈ S)
    (hrel : ∀ i, p i = g i • q i) (heq : ∀ i, η (p i) = η (q i)) :
    ∃ z ∈ S, root u • z ∈ S ∧ η (root u • z) = η z := by
  apply exists_equal_leaf_root_return root η hS hreg hcont hg hp hq hrel
  intro j
  simpa only [heq,sub_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- For a field which separates points on each root leaf, the terminal
comparison forces the genuine root limit to be the identity parameter.
The actual canonical separation theorem supplies this premise on one
conull set under the established compact-support hypotheses. -/
theorem root_limit_eq_zero_of_separation
    (root : U → H) (η : Z → Measure U) {S : Set Z} (hS : IsCompact S)
    (hreg : ∀ q ∈ S, (η q).Regular)
    (hcont : ∀ j : ℕ, ContinuousOn
      (fun q => ∫ v, BBEKLeafMeasureTests.testFunction j v ∂η q) S)
    (hsep : ∀ z ∈ S, ∀ u : U, root u • z ∈ S → η (root u • z) = η z → u = 0)
    {u : U} {g : ℕ → H} (hg : Tendsto g atTop (𝓝 (root u)))
    {p q : ℕ → Z} (hp : ∀ i, p i ∈ S) (hq : ∀ i, q i ∈ S)
    (hrel : ∀ i, p i = g i • q i)
    (htests : ∀ j : ℕ, Tendsto (fun i =>
      (∫ v, BBEKLeafMeasureTests.testFunction j v ∂η (p i)) -
      (∫ v, BBEKLeafMeasureTests.testFunction j v ∂η (q i))) atTop (𝓝 0)) : u = 0 := by
  obtain ⟨z,hz,hrootz,heq⟩ :=
    exists_equal_leaf_root_return root η hS hreg hcont hg hp hq hrel htests
  exact hsep z hz u hrootz heq



/-- The compact Lusin set can be chosen inside a specified measurable conull
set. This preserves pointwise canonical covariance, regularity, and root
separation rather than incorrectly upgrading almost-everywhere properties
on an arbitrary compact set. -/
theorem exists_compact_test_continuity_in_conull
    [MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (η : Z → Measure U) (hη : Measurable η)
    {C : Set Z} (hC : MeasurableSet C) (hCae : ∀ᵐ q ∂μ, q ∈ C)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ S : Set Z, IsCompact S ∧ S ⊆ C ∧ μ Sᶜ < ε ∧
      ∀ j : ℕ, ContinuousOn
        (fun q => ∫ v, BBEKLeafMeasureTests.testFunction j v ∂η q) S := by
  have hhalf : ε/2 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε,by norm_num⟩
  obtain ⟨L,hL,hLbad,hcont⟩ := BBEKLusin.exists_compact_test_continuity μ η hη hhalf
  obtain ⟨K,hKC,hK,hKbad⟩ := hC.exists_isCompact_diff_lt (measure_ne_top μ C) hhalf
  have hCzero : μ Cᶜ = 0 := by simpa only [ae_iff] using hCae
  have hKcompl : μ Kᶜ < ε/2 := by
    have he : Kᶜ = (C \ K) ∪ Cᶜ := by ext q; simp only [mem_compl_iff,mem_union,mem_diff]; tauto
    rw [he]
    exact (measure_union_le _ _).trans_lt (by simpa [hCzero] using hKbad)
  refine ⟨K ∩ L,hK.inter_right hL.isClosed,inter_subset_left.trans hKC,?_,?_⟩
  · rw [compl_inter]
    apply (measure_union_le _ _).trans_lt
    have hh := ENNReal.add_lt_add hKcompl hLbad
    simpa only [ENNReal.add_halves] using hh
  · intro j
    exact (hcont j).mono inter_subset_right

end VV.BBEKLusinRootLimit

