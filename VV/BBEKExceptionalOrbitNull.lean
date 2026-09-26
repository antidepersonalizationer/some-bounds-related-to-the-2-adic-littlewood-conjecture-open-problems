import VV.BBEKExceptionalCentralizer
import Mathlib.Probability.ConditionalProbability

/-! Every common-centralizer orbit has measure zero under the relevant
kernel-of-root diagonal. Positive orbit mass would normalize to an invariant
probability, already ruled out by actual arithmetic-factor coordinates.
In particular, countably many such orbits cannot carry any positive mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal MatrixGroups
namespace VV.BBEKExceptionalOrbitNull
open BBEKDynamics BBEKQuotient BBEKExceptionalFactorOrbit BBEKExceptionalCentralizer
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Restriction and normalization preserve an invariant measurable set. -/
theorem invariant_cond_on_set {Z : Type*} [MeasurableSpace Z]
    {μ : Measure Z} {T : Z → Z} (hT : MeasurePreserving T μ μ)
    {S : Set Z} (hS : MeasurableSet S) (hpre : T ⁻¹' S = S) :
    MeasurePreserving T μ[|S] μ[|S] := by
  have hh := hT.restrict_preimage hS
  rw [hpre] at hh
  exact hh.smul_measure (μ S)⁻¹

theorem realFactorOrbit_preimage (q : X) (g : SL(2,ℝ)) :
    (fun z : X => (g,(1 : SL(2,Q2))) • z) ⁻¹' range (realFactorOrbitMap q) =
      range (realFactorOrbitMap q) := by
  ext z
  constructor
  · rintro ⟨h,he⟩
    refine ⟨g⁻¹*h,?_⟩
    have hh := congrArg (fun z : X => ((g,(1 : SL(2,Q2))) : G)⁻¹ • z) he
    have hone (z : X) : ((1 : SL(2,ℝ)),(1 : SL(2,Q2))) • z = z := one_smul G z
    simpa [realFactorOrbitMap,← MulAction.mul_smul,hone] using hh
  · rintro ⟨h,rfl⟩
    refine ⟨g*h,?_⟩
    simp [realFactorOrbitMap,← MulAction.mul_smul]

theorem padicFactorOrbit_preimage (q : X) (g : SL(2,Q2)) :
    (fun z : X => ((1 : SL(2,ℝ)),g) • z) ⁻¹' range (padicFactorOrbitMap q) =
      range (padicFactorOrbitMap q) := by
  ext z
  constructor
  · rintro ⟨h,he⟩
    refine ⟨g⁻¹*h,?_⟩
    have hh := congrArg (fun z : X => (((1 : SL(2,ℝ)),g) : G)⁻¹ • z) he
    have hone (z : X) : ((1 : SL(2,ℝ)),(1 : SL(2,Q2))) • z = z := one_smul G z
    simpa [padicFactorOrbitMap,← MulAction.mul_smul,hone] using hh
  · rintro ⟨h,rfl⟩
    refine ⟨g*h,?_⟩
    simp [padicFactorOrbitMap,← MulAction.mul_smul]

theorem real_factor_orbit_null (μ : Measure X) [IsFiniteMeasure μ]
    (q : X)
    (hT : MeasurePreserving (fun z : X =>
      (diagonal (1/2 : ℝ) (by norm_num),(1 : SL(2,Q2))) • z) μ μ) :
    μ (range (realFactorOrbitMap q)) = 0 := by
  by_contra hzero
  let S := range (realFactorOrbitMap q)
  letI : IsProbabilityMeasure μ[|S] := cond_isProbabilityMeasure hzero
  exact no_real_factor_orbit_probability μ[|S] q
    (invariant_cond_on_set hT (realFactorOrbitMap_measurableEmbedding q).measurableSet_range
      (realFactorOrbit_preimage q _))
    (cond_apply_self hzero (measure_ne_top μ S))

theorem padic_factor_orbit_null (μ : Measure X) [IsFiniteMeasure μ]
    (q : X)
    (hT : MeasurePreserving (fun z : X =>
      ((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) • z) μ μ) :
    μ (range (padicFactorOrbitMap q)) = 0 := by
  by_contra hzero
  let S := range (padicFactorOrbitMap q)
  letI : IsProbabilityMeasure μ[|S] := cond_isProbabilityMeasure hzero
  exact no_padic_factor_orbit_probability μ[|S] q
    (invariant_cond_on_set hT (padicFactorOrbitMap_measurableEmbedding q).measurableSet_range
      (padicFactorOrbit_preimage q _))
    (cond_apply_self hzero (measure_ne_top μ S))

theorem real_centralizer_orbit_null (μ : Measure X) [IsFiniteMeasure μ]
    (q : X)
    (hT : MeasurePreserving (fun z : X =>
      ((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) • z) μ μ) :
    μ (centralizerOrbit realCommonCentralizer q) = 0 := by
  rw [real_centralizerOrbit_eq_factorOrbit]
  exact padic_factor_orbit_null μ q hT

theorem padic_centralizer_orbit_null (μ : Measure X) [IsFiniteMeasure μ]
    (q : X)
    (hT : MeasurePreserving (fun z : X =>
      (diagonal (1/2 : ℝ) (by norm_num),(1 : SL(2,Q2))) • z) μ μ) :
    μ (centralizerOrbit padicCommonCentralizer q) = 0 := by
  rw [padic_centralizerOrbit_eq_factorOrbit]
  exact real_factor_orbit_null μ q hT

theorem countable_real_centralizer_orbits_null (μ : Measure X) [IsFiniteMeasure μ]
    {I : Type*} [Countable I] (q : I → X)
    (hT : MeasurePreserving (fun z : X =>
      ((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) • z) μ μ) :
    μ (⋃ i, centralizerOrbit realCommonCentralizer (q i)) = 0 :=
  measure_iUnion_null fun i => real_centralizer_orbit_null μ (q i) hT

theorem countable_padic_centralizer_orbits_null (μ : Measure X) [IsFiniteMeasure μ]
    {I : Type*} [Countable I] (q : I → X)
    (hT : MeasurePreserving (fun z : X =>
      (diagonal (1/2 : ℝ) (by norm_num),(1 : SL(2,Q2))) • z) μ μ) :
    μ (⋃ i, centralizerOrbit padicCommonCentralizer (q i)) = 0 :=
  measure_iUnion_null fun i => padic_centralizer_orbit_null μ (q i) hT

end VV.BBEKExceptionalOrbitNull

