import VV.BBEKLeafEntropyChartConditionals

/-! Removing a transverse coordinate that is already recorded by the actual code. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafEntropyCodeConditioning
open BBEKLeafEntropyRefinement

variable {B U Y : Type*} [MeasurableSpace B] [MeasurableSpace U] [MeasurableSpace Y]
  [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace Y]

omit [StandardBorelSpace Y] in
theorem refined_condKernel_eq_condDistrib_of_factor
    (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {f : B × U → Y} (hf : Measurable f) {g : Y → B} (hg : Measurable g)
    (hfactor : ∀ᵐ p ∂ρ, p.1 = g (f p)) :
    ∀ᵐ p ∂ρ, (refinedMeasure ρ f).condKernel (p.1,f p) =
      condDistrib Prod.snd f ρ (f p) := by
  let κ := condDistrib Prod.snd f ρ
  let η : Kernel (B × Y) U := κ.comap Prod.snd measurable_snd
  let E : Y → B × Y := fun y => (g y,y)
  let L : Y × U → (B × Y) × U := fun p => ((g p.1,p.1),p.2)
  have hE : Measurable E := hg.prodMk measurable_id
  have hL : Measurable L := ((hg.comp measurable_fst).prodMk measurable_fst).prodMk measurable_snd
  have hfst : (refinedMeasure ρ f).fst = (ρ.map f).map E := by
    rw [refinedMeasure_fst ρ hf,Measure.map_map hE hf]
    apply Measure.map_congr
    filter_upwards [hfactor] with p hp
    exact Prod.ext hp rfl
  have hmeasure : refinedMeasure ρ f = ((ρ.map f) ⊗ₘ κ).map L := by
    rw [compProd_map_condDistrib measurable_snd.aemeasurable,
      Measure.map_map hL (hf.prodMk measurable_snd)]
    apply Measure.map_congr
    filter_upwards [hfactor] with p hp
    exact Prod.ext (Prod.ext hp rfl) rfl
  have hd : refinedMeasure ρ f = (refinedMeasure ρ f).fst ⊗ₘ η := by
    rw [hfst,hmeasure]
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply hL hs,Measure.compProd_apply (hs.preimage hL),
      Measure.compProd_apply hs,
      lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hE]
    rfl
  have he := eq_condKernel_of_measure_eq_compProd η hd
  rw [refinedMeasure_fst ρ hf] at he
  have hh := ae_of_ae_map (measurable_fst.prodMk hf).aemeasurable he
  filter_upwards [hh] with p hp
  exact hp.symm

section Charts
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKLocalRootFamily BBEKLeafEntropySafety BBEKLeafEntropySubordinate
  BBEKLeafEntropyChartConditionals
variable [TopologicalSpace B] [BorelSpace B] [NormedAddCommGroup U]
  [BorelSpace U] [SecondCountableTopology U]

omit [TopologicalSpace B] [BorelSpace B] in
theorem standardBorel_sum_unit [StandardBorelSpace B] : StandardBorelSpace (Unit ⊕ B) := by
  let tU := upgradeStandardBorel Unit
  letI : TopologicalSpace Unit := tU.toTopologicalSpace
  letI : BorelSpace Unit := tU.toBorelSpace
  letI : SecondCountableTopology Unit := tU.toPolishSpace.toSecondCountableTopology
  letI : TopologicalSpace.IsCompletelyMetrizableSpace Unit := tU.toPolishSpace.toIsCompletelyMetrizableSpace
  letI := upgradeStandardBorel B
  have hb : (inferInstance : MeasurableSpace (Unit ⊕ B)) = borel (Unit ⊕ B) := by
    apply le_antisymm
    · intro S hS
      obtain ⟨hl,hr⟩ := measurableSet_sum_iff.mp hS
      letI : MeasurableSpace (Unit ⊕ B) := borel (Unit ⊕ B)
      letI : BorelSpace (Unit ⊕ B) := ⟨rfl⟩
      have hleft := (Topology.IsOpenEmbedding.inl (X := Unit) (Y := B)).measurableEmbedding.measurableSet_image.mpr hl
      have hright := (Topology.IsOpenEmbedding.inr (X := Unit) (Y := B)).measurableEmbedding.measurableSet_image.mpr hr
      have he : Sum.inl '' (Sum.inl ⁻¹' S) ∪ Sum.inr '' (Sum.inr ⁻¹' S) = S := by
        ext z
        constructor
        · rintro (h | h) <;> rcases h with ⟨u,hu,rfl⟩ <;> exact hu
        · intro hz
          cases z with
          | inl u => exact Or.inl ⟨u,hz,rfl⟩
          | inr u => exact Or.inr ⟨u,hz,rfl⟩
      rw [← he]
      exact hleft.union hright
    · apply MeasurableSpace.generateFrom_le
      intro S hS
      exact measurableSet_sum_iff.mpr
        ⟨(hS.preimage continuous_inl).measurableSet,(hS.preimage continuous_inr).measurableSet⟩
  letI : BorelSpace (Unit ⊕ B) := ⟨hb⟩
  letI : SecondCountableTopology (Unit ⊕ B) := inferInstance
  letI : TopologicalSpace.IsCompletelyMetrizableSpace (Unit ⊕ B) := inferInstance
  letI : PolishSpace (Unit ⊕ B) := PolishSpace.mk
  exact standardBorel_of_polish

def decodeTransverse {ι : Type*} (b₀ : B) (i : ι) (ω : ℕ → ι → Unit ⊕ B) : B :=
  (ω 0 i).elim (fun _ => b₀) id

theorem measurable_decodeTransverse {ι : Type*} (b₀ : B) (i : ι) :
    Measurable (decodeTransverse b₀ i) :=
  (measurable_const.sumElim measurable_id).comp
    ((measurable_pi_apply i).comp (measurable_pi_apply 0))

theorem decodeTransverse_pastPlaqueCode {ι : Type*} (s : GroupParams ≃ₜ B × U)
    (b₀ : B) (c : ι → Chart) (r : ι → ℝ) (T : X → X) (q : X) (i : ι)
    (hi : r i < safetyRadius (c i) q) :
    decodeTransverse b₀ i (pastPlaqueCode s c r T q) = (s (chartCoordinates (c i) q)).1 := by
  simp only [decodeTransverse,pastPlaqueCode,Function.iterate_zero,Function.id_def,
    plaqueCode,if_pos hi,Sum.elim_inr,id_eq]

theorem ae_chartCoordinates_chartPoint (s : GroupParams ≃ₜ B × U)
    (μ : Measure X) (c : Chart) :
    ∀ᵐ p ∂(coordinateMeasureOf μ c).map s,
      s (chartCoordinates c (chartPoint s c p)) = p := by
  rw [s.measurableEmbedding.ae_map_iff]
  change ∀ᵐ p ∂(μ.comap (c.domain.restrict (quotientCoordinates c.base))).map Subtype.val,
    s (chartCoordinates c (chartPoint s c (s p))) = s p
  rw [(MeasurableEmbedding.subtype_coe c.isOpen_domain.measurableSet).ae_map_iff]
  apply ae_of_all
  intro p
  simp only [chartPoint,Homeomorph.symm_apply_apply,chartCoordinates_apply]

theorem active_pastCode_factor {ι : Type*} (s : GroupParams ≃ₜ B × U)
    (b₀ : B) (μ : Measure X) (c : ι → Chart) (r : ι → ℝ) (T : X → X) (i : ι) :
    let A := {q | r i < safetyRadius (c i) q}
    ∀ᵐ p ∂(coordinateMeasureOf (μ.restrict A) (c i)).map s,
      p.1 = decodeTransverse b₀ i
        (pastPlaqueCode s c r T (chartPoint s (c i) p)) := by
  dsimp only
  let A := {q | r i < safetyRadius (c i) q}
  have hA : MeasurableSet A := (isOpen_safetyRadius_superlevel (c i) (r i)).measurableSet
  have hq : ∀ᵐ q ∂(μ.restrict A).restrict (c i).image, q ∈ A :=
    ae_restrict_of_ae (ae_restrict_mem hA)
  rw [← map_split_coordinateMeasure s (μ.restrict A) (c i)] at hq
  have hp := ae_of_ae_map (measurable_chartPoint s (c i)).aemeasurable hq
  filter_upwards [hp,ae_chartCoordinates_chartPoint s (μ.restrict A) (c i)] with p hp hcoord
  rw [decodeTransverse_pastPlaqueCode s b₀ c r T _ i hp,hcoord]

variable [StandardBorelSpace B]

/-- On an active chart, conditioning on the constructed code itself gives the
normalized restriction of its actual leaf kernel. The extra transverse
coordinate has been recovered from the code and removed. -/
theorem pastCode_condDistrib_on_active_chart {ι : Type*} [Countable ι]
    (s : GroupParams ≃ₜ B × U) (axis : U → BBEKLeafwiseKernel.Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (b₀ : B) (μ : Measure X) [IsFiniteMeasure μ]
    (c : ι → Chart) (r : ι → ℝ) {T : X → X} (hT : Measurable T) (i : ι)
    (hlocal : ∀ᵐ q ∂μ, ∃ ε : ℝ, 0 < ε ∧ ∀ u : U, ‖u‖ < ε →
      pastPlaqueCode s c r T (x (axis u).1 (axis u).2 • q) = pastPlaqueCode s c r T q) :
    let F := pastPlaqueCode s c r T
    let A := {q | r i < safetyRadius (c i) q}
    let ρ := (coordinateMeasureOf (μ.restrict A) (c i)).map s
    let f := F ∘ chartPoint s (c i)
    ∀ᵐ p ∂ρ, 0 < ρ.condKernel p.1 (codeFiber (f := f) p.1 (f p)) ∧
      condDistrib Prod.snd f ρ (f p) =
        (ρ.condKernel p.1 (codeFiber (f := f) p.1 (f p)))⁻¹ •
          (ρ.condKernel p.1).restrict (codeFiber (f := f) p.1 (f p)) := by
  dsimp only
  let F := pastPlaqueCode s c r T
  let A := {q | r i < safetyRadius (c i) q}
  let ρ := (coordinateMeasureOf (μ.restrict A) (c i)).map s
  let f := F ∘ chartPoint s (c i)
  letI : StandardBorelSpace (Unit ⊕ B) := standardBorel_sum_unit
  have hF : Measurable F := measurable_pastPlaqueCode s c r hT
  have hf : Measurable f := hF.comp (measurable_chartPoint s (c i))
  have hformula := chartCode_conditional_eq s axis hs (μ.restrict A) (c i) hF
    (ae_restrict_of_ae hlocal)
  have he := refined_condKernel_eq_condDistrib_of_factor ρ hf
    (measurable_decodeTransverse b₀ i) (active_pastCode_factor s b₀ μ c r T i)
  filter_upwards [hformula,he] with p hp he
  exact ⟨hp.1,he.symm.trans hp.2⟩

end Charts

end VV.BBEKLeafEntropyCodeConditioning
