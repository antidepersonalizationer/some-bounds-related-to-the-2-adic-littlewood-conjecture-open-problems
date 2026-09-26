import VV.BBEKLeafEntropyCodeConditioning
import VV.BBEKStandardBorel

/-! Global conditional distributions: code-measurable restriction and chart transport. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafEntropyGlobalConditionals
open BBEKLeafwiseKernel BBEKLeafEntropyRefinement

section Restriction
variable {Z U Y : Type*} [MeasurableSpace Z] [MeasurableSpace U] [MeasurableSpace Y]
  [StandardBorelSpace U] [Nonempty U]

/-- Restricting to an event already recorded by the code leaves its
conditional probabilities unchanged on that event. -/
theorem condDistrib_restrict_code_event (μ : Measure Z) [IsFiniteMeasure μ]
    {F : Z → Y} (hF : Measurable F) {v : Z → U} (hv : Measurable v)
    {A : Set Y} (hA : MeasurableSet A) :
    ∀ᵐ z ∂μ.restrict (F ⁻¹' A),
      condDistrib v F (μ.restrict (F ⁻¹' A)) (F z) = condDistrib v F μ (F z) := by
  let ρ := μ.map (fun z => (F z,v z))
  have hpair : Measurable (fun z => (F z,v z)) := hF.prodMk hv
  have hmap : ρ.restrict (Prod.fst ⁻¹' A) =
      (μ.restrict (F ⁻¹' A)).map (fun z => (F z,v z)) := by
    exact Measure.restrict_map hpair (measurable_fst hA)
  have hh := condKernel_fiberRestriction ρ (measurable_fst hA)
  have hκ := condKernel_congr hmap
  have hfst : (ρ.restrict (Prod.fst ⁻¹' A)).fst = (μ.restrict (F ⁻¹' A)).map F := by
    rw [hmap,Measure.fst_map_prodMk hv]
  rw [hκ,hfst] at hh
  have hp := ae_of_ae_map hF.aemeasurable hh
  filter_upwards [hp,ae_restrict_mem (hF hA)] with z hz hzA
  have he : (Prod.mk (F z) : U → Y × U) ⁻¹' (Prod.fst ⁻¹' A) = univ := by
    ext u
    simp only [mem_preimage,mem_univ,iff_true]
    exact hzA
  rw [he,measure_univ,inv_one,one_smul,Measure.restrict_univ] at hz
  simpa only [condDistrib,ρ] using hz

end Restriction

section Transport
variable {B U Y Z : Type*} [MeasurableSpace B] [MeasurableSpace U]
  [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace Z] [Nonempty Z]

def fiberImageKernel (κ : Kernel Y U) [IsSFiniteKernel κ]
    {Q : B × U → Z} (hQ : Measurable Q) {g : Y → B} (hg : Measurable g) : Kernel Y Z where
  toFun y := (κ y).map (fun u => Q (g y,u))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have hm (y : Y) : Measurable (fun u => Q (g y,u)) := hQ.comp measurable_prodMk_left
    simp only [Measure.map_apply (hm _) hS]
    exact Kernel.measurable_kernel_prodMk_left
      (hS.preimage (hQ.comp ((hg.comp measurable_fst).prodMk measurable_snd)))

instance fiberImageKernel_markov (κ : Kernel Y U) [IsMarkovKernel κ]
    {Q : B × U → Z} (hQ : Measurable Q) {g : Y → B} (hg : Measurable g) :
    IsMarkovKernel (fiberImageKernel κ hQ hg) :=
  ⟨fun _ => isProbabilityMeasure_map (hQ.comp measurable_prodMk_left).aemeasurable⟩

/-- Push the actual leaf conditional through the actual chart map. -/
theorem condDistrib_fiberImage_of_factor (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {f : B × U → Y} (hf : Measurable f) {g : Y → B} (hg : Measurable g)
    {Q : B × U → Z} (hQ : Measurable Q)
    (hfactor : ∀ᵐ p ∂ρ, p.1 = g (f p)) :
    ∀ᵐ p ∂ρ, condDistrib Q f ρ (f p) =
      (condDistrib Prod.snd f ρ (f p)).map (fun u => Q (p.1,u)) := by
  let κ := condDistrib Prod.snd f ρ
  let η := fiberImageKernel κ hQ hg
  let L : Y × U → Y × Z := fun p => (p.1,Q (g p.1,p.2))
  have hL : Measurable L := measurable_fst.prodMk
    (hQ.comp ((hg.comp measurable_fst).prodMk measurable_snd))
  have he : (ρ.map f) ⊗ₘ η = ((ρ.map f) ⊗ₘ κ).map L := by
    apply Measure.ext
    intro S hS
    rw [Measure.compProd_apply hS,Measure.map_apply hL hS,
      Measure.compProd_apply (hS.preimage hL)]
    apply lintegral_congr
    intro y
    change ((κ y).map (fun u => Q (g y,u))) (Prod.mk y ⁻¹' S) = _
    have hm : Measurable (fun u : U => Q (g y,u)) := hQ.comp measurable_prodMk_left
    rw [Measure.map_apply hm (measurable_prodMk_left hS)]
    rfl
  have hd : ρ.map (fun p => (f p,Q p)) = ρ.map f ⊗ₘ η := by
    rw [he,compProd_map_condDistrib measurable_snd.aemeasurable,
      Measure.map_map hL (hf.prodMk measurable_snd)]
    apply Measure.map_congr
    filter_upwards [hfactor] with p hp
    dsimp only [Function.comp_apply,L]
    rw [← hp]
  have heq := condDistrib_ae_eq_of_measure_eq_compProd hf hQ η hd
  have hp := ae_of_ae_map hf.aemeasurable heq
  filter_upwards [hp,hfactor] with p hp hfct
  rw [← hp]
  change (κ (f p)).map (fun u => Q (g (f p),u)) = _
  rw [← hfct]

omit [StandardBorelSpace U] [Nonempty U] in
theorem condDistrib_map_chart (ρ : Measure (B × U)) [IsFiniteMeasure ρ]
    {Q : B × U → Z} (hQ : Measurable Q) {F : Z → Y} (hF : Measurable F) :
    condDistrib Q (F ∘ Q) ρ = condDistrib id F (ρ.map Q) := by
  rw [condDistrib,condDistrib]
  apply condKernel_congr
  rw [Measure.map_map (hF.prodMk measurable_id) hQ]
  rfl

end Transport

section ActualCharts
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKLocalRootFamily BBEKLeafEntropySafety BBEKLeafEntropySubordinate
  BBEKLeafEntropyChartConditionals BBEKLeafEntropyCodeConditioning
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [StandardBorelSpace B] [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]
local instance : Nonempty X := ⟨mk 1⟩

/-- The conditional distribution for the original quotient measure is the
actual active-chart leaf kernel restricted to the code fiber, normalized,
and pushed through the actual chart. -/
theorem global_pastCode_conditional {ι : Type*} [Countable ι]
    (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (b₀ : B) (μ : Measure X) [IsFiniteMeasure μ]
    (c : ι → Chart) (r : ι → ℝ) {T : X → X} (hT : Measurable T) (i : ι)
    (hr : 0 ≤ r i)
    (hlocal : ∀ᵐ q ∂μ, ∃ ε : ℝ, 0 < ε ∧ ∀ u : U, ‖u‖ < ε →
      pastPlaqueCode s c r T (x (axis u).1 (axis u).2 • q) = pastPlaqueCode s c r T q) :
    let F := pastPlaqueCode s c r T
    let A := {q | r i < safetyRadius (c i) q}
    let ρ := (coordinateMeasureOf (μ.restrict A) (c i)).map s
    let f := F ∘ chartPoint s (c i)
    ∀ᵐ p ∂ρ, condDistrib id F μ (f p) =
      ((ρ.condKernel p.1 (codeFiber (f := f) p.1 (f p)))⁻¹ •
        (ρ.condKernel p.1).restrict (codeFiber (f := f) p.1 (f p))).map
          (fun u => chartPoint s (c i) (p.1,u)) := by
  dsimp only
  letI : Nonempty X := ⟨mk 1⟩
  letI : StandardBorelSpace (Unit ⊕ B) := standardBorel_sum_unit
  let F := pastPlaqueCode s c r T
  let A := {q | r i < safetyRadius (c i) q}
  let ρ := (coordinateMeasureOf (μ.restrict A) (c i)).map s
  let Q := chartPoint s (c i)
  let f := F ∘ Q
  have hF : Measurable F := measurable_pastPlaqueCode s c r hT
  have hQ : Measurable Q := measurable_chartPoint s (c i)
  have hf : Measurable f := hF.comp hQ
  have hA : MeasurableSet A := (isOpen_safetyRadius_superlevel (c i) (r i)).measurableSet
  have hAi : A ⊆ (c i).image := by
    intro q hq
    obtain ⟨p,hp,hpq⟩ := mem_safeImage_of_lt_safetyRadius hr hq
    refine ⟨p,?_,hpq⟩
    simpa only [leafShift_zero] using hp 0 (by simpa only [Metric.mem_closedBall,dist_self] using hr)
  have hmap : ρ.map Q = μ.restrict A := by
    rw [map_split_coordinateMeasure s (μ.restrict A) (c i)]
    exact Measure.restrict_eq_self_of_ae_mem ((ae_restrict_mem hA).mono (fun q hq => hAi hq))
  let E : Set (ℕ → ι → Unit ⊕ B) := {ω | ω 0 i ≠ Sum.inl ()}
  have hE : MeasurableSet E := by
    have heval : Measurable (fun ω : ℕ → ι → Unit ⊕ B => ω 0 i) :=
      (measurable_pi_apply i).comp (measurable_pi_apply 0)
    exact (heval (measurableSet_singleton (Sum.inl () : Unit ⊕ B))).compl
  have hpre : F ⁻¹' E = A := by
    ext q
    by_cases hq : r i < safetyRadius (c i) q
    · simp [F,E,A,pastPlaqueCode,plaqueCode,hq]
    · simp [F,E,A,pastPlaqueCode,plaqueCode,hq]
  have hrestrict := condDistrib_restrict_code_event μ hF measurable_id hE
  rw [hpre] at hrestrict
  have hrestrict' : ∀ᵐ p ∂ρ,
      condDistrib id F (μ.restrict A) (f p) = condDistrib id F μ (f p) := by
    have hh : ∀ᵐ q ∂ρ.map Q,
        condDistrib id F (μ.restrict A) (F q) = condDistrib id F μ (F q) := by
      rwa [hmap]
    exact ae_of_ae_map hQ.aemeasurable hh
  have hpush := condDistrib_fiberImage_of_factor ρ hf (measurable_decodeTransverse b₀ i) hQ
    (active_pastCode_factor s b₀ μ c r T i)
  have hformula := pastCode_condDistrib_on_active_chart s axis hs b₀ μ c r hT i hlocal
  have hnat : condDistrib Q f ρ = condDistrib id F (μ.restrict A) := by
    calc
      condDistrib Q f ρ = condDistrib id F (ρ.map Q) := condDistrib_map_chart ρ hQ hF
      _ = condDistrib id F (μ.restrict A) := by
        have hc : ∀ (ν : Measure X) [IsFiniteMeasure ν], ν = μ.restrict A →
            condDistrib id F ν = condDistrib id F (μ.restrict A) := by
          intro ν _ hν
          subst ν
          rfl
        exact hc _ hmap
  rw [hnat] at hpush
  filter_upwards [hpush,hformula,hrestrict'] with p hp hformula hrp
  rw [← hrp,hp,hformula.2]

end ActualCharts

end VV.BBEKLeafEntropyGlobalConditionals
