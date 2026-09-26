import VV.BBEKLeafEntropyGlobalConditionals
import VV.BBEKOneRootOverlap
import VV.BBEKNormalizedRestriction

/-! The global past-code conditional uses the original quotient measure's
chart kernel. Restriction to the active chart introduces no new leaf measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafEntropyCanonicalConditionals
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKLocalRootFamily BBEKLeafEntropySafety BBEKLeafEntropySubordinate
  BBEKLeafEntropyChartConditionals BBEKLeafEntropyCodeConditioning
  BBEKLeafEntropyGlobalConditionals BBEKLeafEntropyRefinement BBEKOneRootOverlap
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [StandardBorelSpace B] [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]
local instance : Nonempty X := ⟨mk 1⟩

omit [StandardBorelSpace B] [StandardBorelSpace U] in
theorem split_coordinateMeasure_restrict (s : GroupParams ≃ₜ B × U)
    (μ : Measure X) (c : Chart) (A : Set X) :
    (coordinateMeasureOf (μ.restrict A) c).map s =
      ((coordinateMeasureOf μ c).map s).restrict (chartPoint s c ⁻¹' A) := by
  rw [← splitMeasureWith_eq,← splitMeasureWith_eq]
  unfold splitMeasureWith
  rw [c.embedding.measurableEmbedding.comap_restrict,
    (splitEmbeddingWith_measurableEmbedding s c).restrict_map]
  congr 2
  ext p
  simp [splitEmbeddingWith,chartPoint]

theorem active_chart_condKernel (s : GroupParams ≃ₜ B × U)
    (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) {A : Set X} (hA : MeasurableSet A) :
    let ν := (coordinateMeasureOf μ c).map s
    let ρ := (coordinateMeasureOf (μ.restrict A) c).map s
    ∀ᵐ p ∂ρ, ρ.condKernel p.1 =
      (ν.condKernel p.1 (Prod.mk p.1 ⁻¹' (chartPoint s c ⁻¹' A)))⁻¹ •
        (ν.condKernel p.1).restrict (Prod.mk p.1 ⁻¹' (chartPoint s c ⁻¹' A)) := by
  dsimp only
  let ν := (coordinateMeasureOf μ c).map s
  let ρ := (coordinateMeasureOf (μ.restrict A) c).map s
  have he : ρ = ν.restrict (chartPoint s c ⁻¹' A) :=
    split_coordinateMeasure_restrict s μ c A
  have hh := condKernel_fiberRestriction ν ((measurable_chartPoint s c) hA)
  have hk := condKernel_congr he
  rw [← hk,← he] at hh
  exact ae_of_ae_map measurable_fst.aemeasurable hh

omit [MeasurableSpace B] [BorelSpace B] [StandardBorelSpace B]
  [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U] [StandardBorelSpace U] in
theorem pastCode_fiber_subset_active {ι : Type*}
    (s : GroupParams ≃ₜ B × U) (c : ι → Chart) (r : ι → ℝ) (T : X → X)
    (i : ι) (p : B × U) (hp : r i < safetyRadius (c i) (chartPoint s (c i) p)) :
    codeFiber (f := pastPlaqueCode s c r T ∘ chartPoint s (c i)) p.1
        ((pastPlaqueCode s c r T ∘ chartPoint s (c i)) p) ⊆
      Prod.mk p.1 ⁻¹' (chartPoint s (c i) ⁻¹' {q | r i < safetyRadius (c i) q}) := by
  intro u hu
  have he := congrFun (congrFun hu 0) i
  change r i < safetyRadius (c i) (chartPoint s (c i) (p.1,u))
  by_contra hh
  simp only [Function.comp_apply,pastPlaqueCode,Function.iterate_zero_apply,
    plaqueCode,if_pos hp,if_neg hh] at he
  exact Sum.noConfusion he

theorem active_chart_original_mass_pos (s : GroupParams ≃ₜ B × U)
    (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) {A : Set X} (hA : MeasurableSet A) :
    let ν := (coordinateMeasureOf μ c).map s
    let ρ := (coordinateMeasureOf (μ.restrict A) c).map s
    ∀ᵐ p ∂ρ, 0 < ν.condKernel p.1 (Prod.mk p.1 ⁻¹' (chartPoint s c ⁻¹' A)) := by
  dsimp only
  have hh := active_chart_condKernel s μ c hA
  filter_upwards [hh] with p hp
  apply pos_iff_ne_zero.mpr
  intro hz
  have hzres := Measure.restrict_eq_zero.mpr hz
  rw [hzres,smul_zero] at hp
  have hmass := congrArg (fun ν : Measure U => ν univ) hp
  simp at hmass

set_option maxHeartbeats 300000 in
/-- The global conditional probability of the actual past code is a
normalized restriction of the original measure's chart leaf kernel.
The intermediate restriction to the active chart has been eliminated. -/
theorem global_pastCode_original_conditional {ι : Type*} [Countable ι]
    (s : GroupParams ≃ₜ B × U) (axis : U → Leaf)
    (hs : ∀ p u, s (leafShift p (axis u)) = ((s p).1,u+(s p).2))
    (b₀ : B) (μ : Measure X) [IsFiniteMeasure μ]
    (c : ι → Chart) (r : ι → ℝ) {T : X → X} (hT : Measurable T) (i : ι)
    (hr : 0 ≤ r i)
    (hlocal : ∀ᵐ q ∂μ, ∃ ε : ℝ, 0 < ε ∧ ∀ u : U, ‖u‖ < ε →
      pastPlaqueCode s c r T (x (axis u).1 (axis u).2 • q) = pastPlaqueCode s c r T q) :
    let F := pastPlaqueCode s c r T
    let A := {q | r i < safetyRadius (c i) q}
    let ν := (coordinateMeasureOf μ (c i)).map s
    let ρ := (coordinateMeasureOf (μ.restrict A) (c i)).map s
    let f := F ∘ chartPoint s (c i)
    ∀ᵐ p ∂ρ, 0 < ν.condKernel p.1 (codeFiber (f := f) p.1 (f p)) ∧
      condDistrib id F μ (f p) =
        ((ν.condKernel p.1 (codeFiber (f := f) p.1 (f p)))⁻¹ •
          (ν.condKernel p.1).restrict (codeFiber (f := f) p.1 (f p))).map
    (fun u => chartPoint s (c i) (p.1,u)) := by
  letI : StandardBorelSpace (Unit ⊕ B) := standardBorel_sum_unit
  let F := pastPlaqueCode s c r T
  let A := {q | r i < safetyRadius (c i) q}
  let ν := (coordinateMeasureOf μ (c i)).map s
  let ρ := (coordinateMeasureOf (μ.restrict A) (c i)).map s
  let Q := chartPoint s (c i)
  let f := F ∘ Q
  change ∀ᵐ p ∂ρ, 0 < ν.condKernel p.1 (codeFiber (f := f) p.1 (f p)) ∧
    condDistrib id F μ (f p) =
      ((ν.condKernel p.1 (codeFiber (f := f) p.1 (f p)))⁻¹ •
        (ν.condKernel p.1).restrict (codeFiber (f := f) p.1 (f p))).map
          (fun u => Q (p.1,u))
  have hF : Measurable F := measurable_pastPlaqueCode s c r hT
  have hQ : Measurable Q := measurable_chartPoint s (c i)
  have hf : Measurable f := hF.comp hQ
  have hA : MeasurableSet A := (isOpen_safetyRadius_superlevel (c i) (r i)).measurableSet
  have he : ρ = ν.restrict (Q ⁻¹' A) := split_coordinateMeasure_restrict s μ (c i) A
  have hactive : ∀ᵐ p ∂ρ, Q p ∈ A := by
    rw [he]
    exact ae_restrict_mem (hQ hA)
  have hκ : ∀ᵐ p ∂ρ, ρ.condKernel p.1 =
      (ν.condKernel p.1 (Prod.mk p.1 ⁻¹' (Q ⁻¹' A)))⁻¹ •
        (ν.condKernel p.1).restrict (Prod.mk p.1 ⁻¹' (Q ⁻¹' A)) :=
    active_chart_condKernel s μ (c i) hA
  have hpositive : ∀ᵐ p ∂ρ, 0 < ρ.condKernel p.1 (codeFiber (f := f) p.1 (f p)) :=
    (pastCode_condDistrib_on_active_chart s axis hs b₀ μ c r hT i hlocal).mono
      (fun _ hp => hp.1)
  have hglobal : ∀ᵐ p ∂ρ, condDistrib id F μ (f p) =
      ((ρ.condKernel p.1 (codeFiber (f := f) p.1 (f p)))⁻¹ •
        (ρ.condKernel p.1).restrict (codeFiber (f := f) p.1 (f p))).map
          (fun u => Q (p.1,u)) :=
    global_pastCode_conditional s axis hs b₀ μ c r hT i hr hlocal
  filter_upwards [hactive,hκ,hpositive,hglobal] with p hp hκ hpositive hglobal
  let S := codeFiber (f := f) p.1 (f p)
  let V := Prod.mk p.1 ⁻¹' (Q ⁻¹' A)
  change ρ.condKernel p.1 = (ν.condKernel p.1 V)⁻¹ • (ν.condKernel p.1).restrict V at hκ
  have hS : MeasurableSet S := by
    have hI : Measurable (fun u : U => ((p.1,f p),u)) := measurable_const.prodMk measurable_id
    exact hI (measurableSet_code_relation hf)
  have hSV : S ⊆ V := pastCode_fiber_subset_active s c r T i p hp
  have hmass : ρ.condKernel p.1 S =
      (ν.condKernel p.1 V)⁻¹ * ν.condKernel p.1 S := by
    have hm := congrArg (fun η : Measure U => η S) hκ
    simpa only [Measure.smul_apply,Measure.restrict_apply hS,
      inter_eq_self_of_subset_left hSV,smul_eq_mul] using hm
  have hpos : ν.condKernel p.1 S ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hmass
    exact hpositive.ne' hmass
  have hnorm : (ρ.condKernel p.1 S)⁻¹ • (ρ.condKernel p.1).restrict S =
      (ν.condKernel p.1 S)⁻¹ • (ν.condKernel p.1).restrict S := by
    exact (congrArg (fun η : Measure U => (η S)⁻¹ • η.restrict S) hκ).trans
      (BBEKNormalizedRestriction.normalize_restrict_normalize (ν.condKernel p.1) hS hSV hpos)
  refine ⟨pos_iff_ne_zero.mpr hpos,?_⟩
  exact hglobal.trans (congrArg (fun η : Measure U => η.map (fun u => Q (p.1,u))) hnorm)

end VV.BBEKLeafEntropyCanonicalConditionals
