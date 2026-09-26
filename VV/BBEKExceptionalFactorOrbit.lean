import VV.BBEKStandardBorel
import VV.BBEKStabilizerRecurrence

/-! A single local-factor orbit in the actual arithmetic quotient carries no
probability invariant under a strictly contracting diagonal time. The orbit
need not be closed: its parameterization is a measurable embedding. -/
noncomputable section
open Matrix Set MeasureTheory Function Filter
open scoped MatrixGroups Topology
namespace VV.BBEKExceptionalFactorOrbit
open BBEKDynamics BBEKQuotient BBEKTopology BBEKLeafwiseStabilizer
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace Q2 := borel Q2
local instance : BorelSpace Q2 := ⟨rfl⟩

local instance slMeasurable {F : Type*} [CommRing F] [TopologicalSpace F] :
    MeasurableSpace SL(2,F) := borel SL(2,F)
local instance slBorel {F : Type*} [CommRing F] [TopologicalSpace F] :
    BorelSpace SL(2,F) := ⟨rfl⟩
local instance slPolish {F : Type*} [NormedField F] [CompleteSpace F] [SecondCountableTopology F] :
    PolishSpace SL(2,F) := by
  letI : PolishSpace (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → F))
  exact (isClosed_eq continuous_id.matrix_det continuous_const).polishSpace

theorem gamma_eq_one_of_fst_eq_one {g : G} (hg : g ∈ Gamma) (h : g.1 = 1) : g = 1 := by
  obtain ⟨B,rfl⟩ := hg
  have hB : B = 1 := by
    apply SpecialLinearGroup.ext
    intro i j
    apply dyadicToReal_injective
    have he := congrArg (fun M : SL(2,ℝ) => M i j) h
    change dyadicToReal (B i j) = (1 : SL(2,ℝ)) i j at he
    exact he.trans (congrArg (fun M : SL(2,ℝ) => M i j)
      (map_one (SpecialLinearGroup.map dyadicToReal))).symm
  simp [hB]

theorem gamma_eq_one_of_snd_eq_one {g : G} (hg : g ∈ Gamma) (h : g.2 = 1) : g = 1 := by
  obtain ⟨B,rfl⟩ := hg
  have hB : B = 1 := by
    apply SpecialLinearGroup.ext
    intro i j
    apply dyadicToQ2_injective
    have he := congrArg (fun M : SL(2,Q2) => M i j) h
    change dyadicToQ2 (B i j) = (1 : SL(2,Q2)) i j at he
    exact he.trans (congrArg (fun M : SL(2,Q2) => M i j)
      (map_one (SpecialLinearGroup.map dyadicToQ2))).symm
  simp [hB]

def realFactorOrbitMap (q : X) (g : SL(2,ℝ)) : X := (g, (1 : SL(2,Q2))) • q
def padicFactorOrbitMap (q : X) (g : SL(2,Q2)) : X := ((1 : SL(2,ℝ)), g) • q

theorem realFactorOrbitMap_injective (q : X) : Injective (realFactorOrbitMap q) := by
  induction q using Quotient.inductionOn with
  | h M =>
    intro a b he
    have hg := (mk_eq_iff _ _).mp he
    have hh := gamma_eq_one_of_snd_eq_one hg (by simp)
    have hc := mul_right_cancel (inv_mul_eq_one.mp hh)
    exact congrArg Prod.fst hc

theorem padicFactorOrbitMap_injective (q : X) : Injective (padicFactorOrbitMap q) := by
  induction q using Quotient.inductionOn with
  | h M =>
    intro a b he
    have hg := (mk_eq_iff _ _).mp he
    have hh := gamma_eq_one_of_fst_eq_one hg (by simp)
    have hc := mul_right_cancel (inv_mul_eq_one.mp hh)
    exact congrArg Prod.snd hc

theorem realFactorOrbitMap_measurableEmbedding (q : X) :
    MeasurableEmbedding (realFactorOrbitMap q) :=
  ((continuous_id.prodMk continuous_const).smul continuous_const).measurableEmbedding
    (realFactorOrbitMap_injective q)

theorem padicFactorOrbitMap_measurableEmbedding (q : X) :
    MeasurableEmbedding (padicFactorOrbitMap q) :=
  ((continuous_const.prodMk continuous_id).smul continuous_const).measurableEmbedding
    (padicFactorOrbitMap_injective q)

/-- An actual injective orbit parameterization rules out a diagonal-invariant
probability concentrated on its image. No closed-orbit assumption is made. -/
theorem no_probability_on_sl2_image
    {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e : SL(2,F) → X) (he : MeasurableEmbedding e)
    {a : F} (ha : a ≠ 0) (hsmall : ‖a‖ < 1)
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (hcomm : ∀ g, T (e g) = e (diagonal a ha * g))
    (hmass : μ (range e) = 1) : False := by
  have hmem : ∀ᵐ q ∂μ, q ∈ range e := by
    rw [ae_iff]
    change μ (range e)ᶜ = 0
    rw [measure_compl he.measurableSet_range (measure_ne_top _ _),
      measure_univ,hmass,tsub_self]
  have hzero (j : Fin 2) : ∀ᵐ q ∂μ, ∀ g, e g = q → g 0 j = 0 := by
    have hcoordCont : Continuous (fun g : SL(2,F) => g 0 j) :=
      (continuous_apply j).comp ((continuous_apply 0).comp continuous_subtype_val)
    have hcoord : Measurable (fun g : SL(2,F) => g 0 j) := hcoordCont.measurable
    obtain ⟨f,hf,hfe⟩ := he.exists_measurable_extend hcoord (fun _ => inferInstance)
    have hcov : ∀ᵐ q ∂μ, f (T q) = a * f q := by
      filter_upwards [hmem] with q hq
      obtain ⟨g,rfl⟩ := hq
      rw [hcomm,show f (e (diagonal a ha * g)) = (diagonal a ha * g) 0 j from congrFun hfe _,
        show f (e g) = g 0 j from congrFun hfe _]
      simp [BBEKDynamics.diagonal,Matrix.mul_apply,Fin.sum_univ_two]
    filter_upwards [ae_eq_zero_of_scalar_covariance hT hf ha hsmall hcov] with q hq g hg
    rw [← hg,show f (e g) = g 0 j from congrFun hfe _] at hq
    exact hq
  obtain ⟨q,hq,h0,h1⟩ := (hmem.and ((hzero 0).and (hzero 1))).exists
  obtain ⟨g,hg⟩ := hq
  have hdet := g.property
  rw [Matrix.det_fin_two] at hdet
  simp only [h0 g hg,h1 g hg,zero_mul,sub_zero] at hdet
  exact zero_ne_one hdet

/-- No probability invariant under this real diagonal can concentrate on one
real-factor orbit, even if that orbit is not closed. -/
theorem no_real_factor_orbit_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X)
    (hT : MeasurePreserving (fun z : X =>
      (diagonal (1/2 : ℝ) (by norm_num), (1 : SL(2,Q2))) • z) μ μ)
    (hmass : μ (range (realFactorOrbitMap q)) = 1) : False := by
  apply no_probability_on_sl2_image μ (realFactorOrbitMap q)
    (realFactorOrbitMap_measurableEmbedding q) (by norm_num : (1/2 : ℝ) ≠ 0)
    (by norm_num : ‖(1/2 : ℝ)‖ < 1) _ hT _ hmass
  intro g
  simp only [realFactorOrbitMap,← MulAction.mul_smul,Prod.mk_mul_mk,one_mul]

/-- The corresponding actual 2-adic factor-orbit obstruction. -/
theorem no_padic_factor_orbit_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X)
    (hT : MeasurePreserving (fun z : X =>
      ((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) • z) μ μ)
    (hmass : μ (range (padicFactorOrbitMap q)) = 1) : False := by
  have hsmall : ‖(2 : Q2)‖ < 1 := by
    have he : ‖(2 : Q2)‖ = (2 : ℝ)⁻¹ := padicNormE.norm_p
    rw [he]
    norm_num
  apply no_probability_on_sl2_image μ (padicFactorOrbitMap q)
    (padicFactorOrbitMap_measurableEmbedding q) (by norm_num : (2 : Q2) ≠ 0)
    hsmall _ hT _ hmass
  intro g
  simp only [padicFactorOrbitMap,← MulAction.mul_smul,Prod.mk_mul_mk,one_mul]

end VV.BBEKExceptionalFactorOrbit




