import VV.BBEKKernelSkew
import VV.BBEKLeafEntropyDisintegration
import VV.BBEKExceptionalCentralizer

/-! Conditioning on an invariant measurable observable preserves the actual
measure-preserving transformation on almost every conditional probability.
The kernel is the literal condDistrib of the identity, and its invariance is
derived from disintegration uniqueness. It is not an additional hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Function
open scoped Topology ENNReal ProbabilityTheory MatrixGroups
namespace VV.BBEKInvariantConditionals
open BBEKLeafwiseKernel

section General
variable {Z B : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableSpace B]

/-- Almost every conditional probability over an invariant observable is
invariant under T. Neither ergodicity nor an invertible T is needed. -/
theorem condDistrib_id_measurePreserving
    (μ : Measure Z) [IsFiniteMeasure μ] {T : Z → Z}
    (hT : MeasurePreserving T μ μ) (f : Z → B) (hf : Measurable f)
    (hinv : ∀ᵐ z ∂μ, f (T z) = f z) :
    ∀ᵐ b ∂μ.map f, MeasurePreserving T (condDistrib id f μ b) (condDistrib id f μ b) := by
  let ρ : Measure (B × Z) := μ.map (fun z => (f z,z))
  have hpair : Measurable (fun z : Z => (f z,z)) := hf.prodMk measurable_id
  have hmap : ρ.map (fun p : B × Z => (p.1,T p.2)) = ρ := by
    change (μ.map (fun z => (f z,z))).map (fun p : B × Z => (p.1,T p.2)) = ρ
    have hskew : Measurable (fun p : B × Z => (p.1,T p.2)) := measurable_fst.prodMk (hT.measurable.comp measurable_snd)
    rw [Measure.map_map hskew hpair]
    have he : μ.map ((fun p : B × Z => (p.1,T p.2)) ∘ (fun z : Z => (f z,z))) =
        μ.map ((fun z : Z => (f z,z)) ∘ T) := by
      apply Measure.map_congr
      filter_upwards [hinv] with z hz
      exact Prod.ext hz.symm rfl
    rw [he,← Measure.map_map hpair hT.measurable,hT.map_eq]
  have hfst : ρ.fst = μ.map f := by
    change (μ.map (fun z => (f z,z))).map Prod.fst = μ.map f
    rw [Measure.map_map measurable_fst hpair]
    rfl
  have hc := condKernel_map_skew ρ (MeasurableEquiv.refl B)
    (fun p : B × Z => T p.2) (hT.measurable.comp measurable_snd)
  have hc' : ∀ᵐ b ∂ρ.fst, ρ.condKernel b = (ρ.condKernel b).map T := by
    simpa only [MeasurableEquiv.refl_apply,hmap] using hc
  rw [hfst] at hc'
  filter_upwards [hc'] with b hb
  refine ⟨hT.measurable,?_⟩
  rw [condDistrib]
  change (ρ.condKernel b).map T = ρ.condKernel b
  exact hb.symm
end General

open BBEKDynamics BBEKQuotient BBEKExceptionalCentralizer
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Nonempty X := ⟨basePoint⟩

/-- The actual conditionals of a real-root invariant observable cannot all
concentrate on its opposite-root common-centralizer orbits. Invariance of
the conditionals is proved above, not included among the assumptions. -/
theorem no_real_centralizer_conditional_concentration
    {B : Type*} [MeasurableSpace B]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → B) (hf : Measurable f)
    (hT : MeasurePreserving (fun z : X =>
      ((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) • z) μ μ)
    (hinv : ∀ᵐ z ∂μ,
      f (((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) • z) = f z)
    (hconcentration : ∀ᵐ b ∂μ.map f, ∃ q : X,
      (condDistrib id f μ b) (centralizerOrbit realCommonCentralizer q) = 1) : False := by
  have hi := condDistrib_id_measurePreserving μ hT f hf hinv
  letI : IsProbabilityMeasure (μ.map f) := isProbabilityMeasure_map hf.aemeasurable
  obtain ⟨b,hb,q,hq⟩ := (hi.and hconcentration).exists
  exact no_real_centralizer_orbit_probability (condDistrib id f μ b) q hb hq

/-- The symmetric actual conditional-probability exclusion for a 2-adic-root
observable fixed by the real kernel-of-root diagonal time. -/
theorem no_padic_centralizer_conditional_concentration
    {B : Type*} [MeasurableSpace B]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → B) (hf : Measurable f)
    (hT : MeasurePreserving (fun z : X =>
      (diagonal (1/2 : ℝ) (by norm_num),(1 : SL(2,Q2))) • z) μ μ)
    (hinv : ∀ᵐ z ∂μ,
      f ((diagonal (1/2 : ℝ) (by norm_num),(1 : SL(2,Q2))) • z) = f z)
    (hconcentration : ∀ᵐ b ∂μ.map f, ∃ q : X,
      (condDistrib id f μ b) (centralizerOrbit padicCommonCentralizer q) = 1) : False := by
  have hi := condDistrib_id_measurePreserving μ hT f hf hinv
  letI : IsProbabilityMeasure (μ.map f) := isProbabilityMeasure_map hf.aemeasurable
  obtain ⟨b,hb,q,hq⟩ := (hi.and hconcentration).exists
  exact no_padic_centralizer_orbit_probability (condDistrib id f μ b) q hb hq




/-- Almost every actual conditional assigns less than full mass to every
real common-centralizer orbit; this also excludes concentration on a positive
measure set of fibers. -/
theorem ae_no_real_centralizer_conditional_concentration
    {B : Type*} [MeasurableSpace B]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → B) (hf : Measurable f)
    (hT : MeasurePreserving (fun z : X =>
      ((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) • z) μ μ)
    (hinv : ∀ᵐ z ∂μ,
      f (((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) • z) = f z) :
    ∀ᵐ b ∂μ.map f, ∀ q : X,
      (condDistrib id f μ b) (centralizerOrbit realCommonCentralizer q) ≠ 1 := by
  filter_upwards [condDistrib_id_measurePreserving μ hT f hf hinv] with b hb q hq
  exact no_real_centralizer_orbit_probability (condDistrib id f μ b) q hb hq

/-- The corresponding exclusion for every 2-adic common-centralizer orbit. -/
theorem ae_no_padic_centralizer_conditional_concentration
    {B : Type*} [MeasurableSpace B]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → B) (hf : Measurable f)
    (hT : MeasurePreserving (fun z : X =>
      (diagonal (1/2 : ℝ) (by norm_num),(1 : SL(2,Q2))) • z) μ μ)
    (hinv : ∀ᵐ z ∂μ,
      f ((diagonal (1/2 : ℝ) (by norm_num),(1 : SL(2,Q2))) • z) = f z) :
    ∀ᵐ b ∂μ.map f, ∀ q : X,
      (condDistrib id f μ b) (centralizerOrbit padicCommonCentralizer q) ≠ 1 := by
  filter_upwards [condDistrib_id_measurePreserving μ hT f hf hinv] with b hb q hq
  exact no_padic_centralizer_orbit_probability (condDistrib id f μ b) q hb hq
end VV.BBEKInvariantConditionals
