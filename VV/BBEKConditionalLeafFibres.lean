import VV.BBEKInvariantConditionals
import VV.BBEKLeafMeasureTests

/-! Actual disintegration over Radon leaf fields is supported on their true
fibres. Countable compact-support integral tests determine infinite Radon
measures; no standard-Borel assertion about all measures is imposed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Function
open scoped Topology ENNReal
namespace VV.BBEKConditionalLeafFibres
open BBEKLeafMeasureTests

variable {Z B : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableSpace B]

theorem condDistrib_id_ae_relation (μ : Measure Z) [IsFiniteMeasure μ]
    (f : Z → B) (hf : Measurable f) {R : B × Z → Prop}
    (hR : MeasurableSet {p | R p}) (h : ∀ᵐ z ∂μ, R (f z,z)) :
    ∀ᵐ b ∂μ.map f, ∀ᵐ z ∂condDistrib id f μ b, R (b,z) := by
  let ρ : Measure (B × Z) := μ.map (fun z => (f z,z))
  have hpair : Measurable (fun z : Z => (f z,z)) := hf.prodMk measurable_id
  have hh : ∀ᵐ p ∂ρ, R p := (ae_map_iff hpair.aemeasurable hR).mpr h
  have hh' : ∀ᵐ p ∂ρ.fst ⊗ₘ ρ.condKernel, R p := by
    rwa [Measure.disintegrate]
  have hb := Measure.ae_ae_of_ae_compProd hh'
  have hfst : ρ.fst = μ.map f := by
    change (μ.map (fun z => (f z,z))).map Prod.fst = μ.map f
    rw [Measure.map_map measurable_fst hpair]
    rfl
  rw [hfst] at hb
  simpa only [condDistrib,id_eq] using hb

/-- Every ambient conull property holds almost surely for almost every actual
conditional probability; the property itself need not be measurable. -/
theorem condDistrib_id_ae_of_ae (μ : Measure Z) [IsFiniteMeasure μ]
    (f : Z → B) (hf : Measurable f) {P : Z → Prop} (hP : ∀ᵐ z ∂μ, P z) :
    ∀ᵐ b ∂μ.map f, ∀ᵐ z ∂condDistrib id f μ b, P z := by
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hn : ∀ᵐ z ∂μ, z ∈ Nᶜ := by
    apply ae_iff.mpr
    simpa only [mem_compl_iff,not_not] using hN0
  have hh := condDistrib_id_ae_relation μ f hf
    (hNm.compl.preimage measurable_snd) hn
  filter_upwards [hh] with b hb
  filter_upwards [hb] with z hz
  by_contra hp
  exact hz (hN hp)

section Radon
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [ProperSpace U] [SecondCountableTopology U]

/-- A measurable Radon-measure field that factors through the conditioned
observable is literally constant on almost every sampled conditional fibre. -/
theorem condDistrib_id_leaf_fibre (μ : Measure Z) [IsFiniteMeasure μ]
    (f : Z → B) (hf : Measurable f)
    (η : Z → Measure U) (hη : Measurable η)
    (e : B → Measure U) (he : Measurable e)
    (hfactor : ∀ z, e (f z) = η z)
    (hreg : ∀ᵐ z ∂μ, (η z).Regular) :
    ∀ᵐ q ∂μ, ∀ᵐ z ∂condDistrib id f μ (f q), η z = η q := by
  have hj (j : ℕ) : ∀ᵐ b ∂μ.map f, ∀ᵐ z ∂condDistrib id f μ b,
      ∫ u, testFunction (U := U) j u ∂η z =
        ∫ u, testFunction (U := U) j u ∂e b := by
    apply condDistrib_id_ae_relation μ f hf
      (measurableSet_eq_fun
        ((measurable_integral_family η hη _).comp measurable_snd)
        ((measurable_integral_family e he _).comp measurable_fst))
    exact ae_of_all _ fun z => congrArg (fun ν : Measure U => ∫ u, testFunction j u ∂ν)
      (hfactor z).symm
  have hh : ∀ᵐ b ∂μ.map f, ∀ᵐ z ∂condDistrib id f μ b, ∀ j : ℕ,
      ∫ u, testFunction (U := U) j u ∂η z =
        ∫ u, testFunction (U := U) j u ∂e b := by
    filter_upwards [ae_all_iff.mpr hj] with b hb
    exact ae_all_iff.mpr hb
  have hp := ae_of_ae_map hf.aemeasurable hh
  have hr := ae_of_ae_map hf.aemeasurable (condDistrib_id_ae_of_ae μ f hf hreg)
  filter_upwards [hreg,hp,hr] with q hq hpq hrq
  filter_upwards [hpq,hrq] with z hz hrz
  letI := hq
  letI := hrz
  apply ext_of_test_integrals
  intro j
  simpa only [hfactor] using hz j

/-- In particular, disintegration over a pair of actual Radon leaf fields
carries both original fields unchanged, including when their total masses
are infinite. No finite-measure normalization is substituted. -/
theorem condDistrib_id_leaf_pair_fibre (μ : Measure Z) [IsFiniteMeasure μ]
    (ηplus ηminus : Z → Measure U) (hplus : Measurable ηplus) (hminus : Measurable ηminus)
    (hrplus : ∀ᵐ z ∂μ, (ηplus z).Regular) (hrminus : ∀ᵐ z ∂μ, (ηminus z).Regular) :
    ∀ᵐ q ∂μ, ∀ᵐ z ∂condDistrib id (fun z => (ηplus z,ηminus z)) μ (ηplus q,ηminus q),
      ηplus z = ηplus q ∧ ηminus z = ηminus q := by
  have hp := condDistrib_id_leaf_fibre μ (fun z => (ηplus z,ηminus z)) (hplus.prodMk hminus)
    ηplus hplus Prod.fst measurable_fst (fun _ => rfl) hrplus
  have hm := condDistrib_id_leaf_fibre μ (fun z => (ηplus z,ηminus z)) (hplus.prodMk hminus)
    ηminus hminus Prod.snd measurable_snd (fun _ => rfl) hrminus
  filter_upwards [hp,hm] with q hpq hmq
  exact hpq.and hmq
end Radon
end VV.BBEKConditionalLeafFibres

