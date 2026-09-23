import VV.BBEKLeafwiseStabilizer
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-! Actual Poincaré recurrence rules out nonunit multipliers for
quasi-invariant translations of normalized contracting leaf measures. -/

noncomputable section
open Set MeasureTheory Function Filter Metric
open scoped Topology ENNReal NNReal

namespace VV.BBEKLeafwiseStabilizer

variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

theorem eigen_pow_le_ball_two (η : Measure U)
    (hunit : η (ball (0 : U) 1) = 1) {u : U} {c : ℝ≥0}
    (heigen : translate u η = c • η) (k : ℕ) (hsmall : ‖k • u‖ < 1) :
    (c : ℝ≥0∞)^k ≤ η (ball (0 : U) 2) := by
  have hsub : (k • u + ·) ⁻¹' ball (0 : U) 1 ⊆ ball (0 : U) 2 := by
    intro x hx
    have hxnorm : ‖k • u + x‖ < 1 := by simpa only [mem_preimage,mem_ball,dist_zero_right] using hx
    have ht := norm_sub_le (k • u + x) (k • u)
    have he : k • u + x - k • u = x := by abel
    rw [he] at ht
    simpa only [mem_ball,dist_zero_right] using (show ‖x‖ < 2 by linarith)
  have he := congrArg (fun m : Measure U => m (ball (0 : U) 1))
    (translate_nsmul_of_eigen η heigen k)
  dsimp only at he
  rw [translate_apply _ _ isOpen_ball.measurableSet,Measure.smul_apply,hunit] at he
  simp only [ENNReal.smul_def,ENNReal.coe_pow,smul_eq_mul,mul_one] at he
  exact he.symm.le.trans (measure_mono hsub)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  {T : X → X}

/-- Measurable observables return to all neighborhoods of their original
value almost surely.  No continuity of the base transformation or of the
observable is required.  This applies to countable families of local
leaf-measure tests once they have been constructed measurably. -/
theorem ae_observable_recurrent
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (hT : MeasurePreserving T μ μ) {f : X → Y} (hf : Measurable f) :
    ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 (f x), ∃ᶠ n : ℕ in atTop, f ((T^[n]) x) ∈ s := by
  have hrec : ∀ s ∈ TopologicalSpace.countableBasis Y,
      ∀ᵐ x ∂μ, f x ∈ s → ∃ᶠ n : ℕ in atTop, f ((T^[n]) x) ∈ s := by
    intro s hs
    exact hT.conservative.ae_mem_imp_frequently_image_mem
      (((TopologicalSpace.isOpen_of_mem_countableBasis hs).measurableSet.preimage hf).nullMeasurableSet)
  refine ((ae_ball_iff (TopologicalSpace.countable_countableBasis Y)).mpr hrec).mono ?_
  intro x hx s hs
  obtain ⟨O,hO,hxO,hOs⟩ := (TopologicalSpace.isBasis_countableBasis Y).mem_nhds_iff.mp hs
  exact (hx O hO hxO).mono fun n hn => hOs hn

theorem ae_observable_recurrent_subseq
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [FirstCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (hT : MeasurePreserving T μ μ) {f : X → Y} (hf : Measurable f) :
    ∀ᵐ x ∂μ, ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun j => f ((T^[n j]) x)) atTop (𝓝 (f x)) := by
  filter_upwards [ae_observable_recurrent hT hf] with x hx
  exact TopologicalSpace.FirstCountableTopology.tendsto_subseq
    (mapClusterPt_iff_frequently.mpr hx)

/-- Poincaré recurrence is derived here from preservation of the finite base
measure. No recurrence or quasi-invariance multiplier conclusion is assumed.
The only leaf-family inputs are normalization, local finiteness, measurable
local masses, and the projective covariance under the contracting coordinate. -/
theorem ae_translation_multiplier_eq_one
    (hT : MeasurePreserving T μ μ) (η : X → Measure U)
    (hmass : Measurable (fun x => η x (ball (0 : U) 2)))
    (hnorm : ∀ᵐ x ∂μ, η x (ball (0 : U) 1) = 1)
    (hfinite : ∀ᵐ x ∂μ, η x (ball (0 : U) 2) ≠ ∞)
    (σ : U ≃+ U) (hσ : Measurable σ)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, ∀ (u : U) (c : ℝ≥0), c ≠ 0 → translate u (η x) = c • η x → c = 1 := by
  classical
  let S (M : ℕ) : Set X := {x | η x (ball (0 : U) 2) ≤ M}
  have hS (M : ℕ) : MeasurableSet (S M) := measurableSet_le hmass measurable_const
  have hreturn : ∀ᵐ x ∂μ, ∀ M : ℕ, x ∈ S M → ∃ᶠ n : ℕ in atTop, (T^[n]) x ∈ S M := by
    apply ae_all_iff.mpr
    intro M
    exact hT.conservative.ae_mem_imp_frequently_image_mem (hS M).nullMeasurableSet
  have hnormAll : ∀ᵐ x ∂μ, ∀ n : ℕ, η ((T^[n]) x) (ball (0 : U) 1) = 1 := by
    apply ae_all_iff.mpr
    intro n
    exact (hT.iterate n).quasiMeasurePreserving.ae hnorm
  have hcovAll : ∀ᵐ x ∂μ, ∀ n : ℕ,
      ∃ d : ℝ≥0, η (T ((T^[n]) x)) = d • Measure.map σ (η ((T^[n]) x)) := by
    apply ae_all_iff.mpr
    intro n
    exact (hT.iterate n).quasiMeasurePreserving.ae hcov
  filter_upwards [hreturn,hnormAll,hcovAll,hfinite] with x hxret hxnorm hxcov hxfin
  have hle (u : U) (c : ℝ≥0) (heigen : translate u (η x) = c • η x) : c ≤ 1 := by
    by_contra hc
    have hcpos : 1 < c := lt_of_not_ge hc
    obtain ⟨M,hM⟩ := ENNReal.exists_nat_gt hxfin
    have hreturns := hxret M hM.le
    have hiter (n : ℕ) : translate ((σ^[n]) u) (η ((T^[n]) x)) = c • η ((T^[n]) x) := by
      induction n with
      | zero => simpa using heigen
      | succ n ih =>
        obtain ⟨d,hd⟩ := hxcov n
        rw [Function.iterate_succ_apply',Function.iterate_succ_apply',hd]
        exact translate_eigen_projective_map σ hσ _ ih d
    have hcposR : (1 : ℝ) < c := by exact_mod_cast hcpos
    obtain ⟨k,hkR⟩ : ∃ k : ℕ, (M : ℝ) < (c : ℝ)^k :=
      ((tendsto_pow_atTop_atTop_of_one_lt hcposR).eventually (eventually_gt_atTop (M : ℝ))).exists
    have hk : (M : ℝ≥0) < c^k := by exact_mod_cast hkR
    have hsmall : ∀ᶠ n : ℕ in atTop, ‖k • (σ^[n]) u‖ < 1 := by
      have hc := (continuous_nsmul k).continuousAt.tendsto.comp (hcontract u)
      have hc' : Tendsto (fun n => ‖k • (σ^[n]) u‖) atTop (𝓝 (0 : ℝ)) := by
        simpa only [nsmul_zero,norm_zero] using hc.norm
      exact hc'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨n,hn,hsmalln⟩ := (hreturns.and_eventually hsmall).exists
    have hb := eigen_pow_le_ball_two (η ((T^[n]) x)) (hxnorm n) (hiter n) k hsmalln
    have hk' : (M : ℝ≥0∞) < (c : ℝ≥0∞)^k := by exact_mod_cast hk
    exact (not_le_of_gt hk') (hb.trans hn)
  intro u c hc heigen
  have hupper := hle u c heigen
  have hinv := hle (-u) c⁻¹ (translate_neg_of_eigen (η x) hc heigen)
  exact le_antisymm hupper ((inv_le_one₀ (pos_iff_ne_zero.mpr hc)).mp hinv)

theorem ae_projectiveTranslationStabilizer_eq
    (hT : MeasurePreserving T μ μ) (η : X → Measure U)
    (hmass : Measurable (fun x => η x (ball (0 : U) 2)))
    (hnorm : ∀ᵐ x ∂μ, η x (ball (0 : U) 1) = 1)
    (hfinite : ∀ᵐ x ∂μ, η x (ball (0 : U) 2) ≠ ∞)
    (σ : U ≃+ U) (hσ : Measurable σ)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, projectiveTranslationStabilizer (η x) = translationStabilizer (η x) := by
  filter_upwards [ae_translation_multiplier_eq_one hT η hmass hnorm hfinite σ hσ hcontract hcov]
    with x hx
  apply le_antisymm _ (translationStabilizer_le_projective (η x))
  rintro u ⟨c,hc,hu⟩
  rw [hx u c hc hu,one_smul] at hu
  exact hu

end VV.BBEKLeafwiseStabilizer

namespace VV.BBEKLeafwiseStabilizer
section Field
variable {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- The actual one-dimensional root dilation, as an additive equivalence. -/
def rootDilation (a : F) (ha : a ≠ 0) : F ≃+ F where
  toFun x := a*x
  invFun x := a⁻¹*x
  left_inv x := by simp [← mul_assoc,ha]
  right_inv x := by simp [← mul_assoc,ha]
  map_add' := mul_add a

omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem rootDilation_iterate (a : F) (ha : a ≠ 0) (u : F) (n : ℕ) :
    ((rootDilation a ha)^[n]) u = a^n*u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,pow_succ']
    exact (mul_assoc a (a^n) u).symm

omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem rootDilation_contracts {a : F} (ha : a ≠ 0) (hsmall : ‖a‖ < 1) (u : F) :
    Tendsto (fun n : ℕ => ((rootDilation a ha)^[n]) u) atTop (𝓝 0) := by
  simp only [rootDilation_iterate]
  simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hsmall).mul_const u

/-- The recurrence theorem specialized to scalar root groups over a normed
field (in particular R and Q₂); contraction is proved from the scalar norm. -/
theorem ae_translation_multiplier_eq_one_of_rootDilation
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (η : X → Measure F)
    (hmass : Measurable (fun x => η x (ball (0 : F) 2)))
    (hnorm : ∀ᵐ x ∂μ, η x (ball (0 : F) 1) = 1)
    (hfinite : ∀ᵐ x ∂μ, η x (ball (0 : F) 2) ≠ ∞)
    {a : F} (ha : a ≠ 0) (hsmall : ‖a‖ < 1)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0, η (T x) = d • Measure.map (a * ·) (η x)) :
    ∀ᵐ x ∂μ, ∀ (u : F) (c : ℝ≥0), c ≠ 0 → translate u (η x) = c • η x → c = 1 := by
  exact ae_translation_multiplier_eq_one hT η hmass hnorm hfinite (rootDilation a ha)
    (measurable_const.mul measurable_id) (rootDilation_contracts ha hsmall) hcov

end Field

end VV.BBEKLeafwiseStabilizer
