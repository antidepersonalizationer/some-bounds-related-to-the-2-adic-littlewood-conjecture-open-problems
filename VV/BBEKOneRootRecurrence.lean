import VV.BBEKOneRootAtoms

/-!
# Exact translation stabilizers of the four canonical root families

The actual globally glued one-root families are normalized on a radius
chosen by quotient geometry. Recurrence is proved for that radius, without
rescaling coordinates or replacing the family by an arbitrary measure.
The resulting scalar-one statement identifies projective and exact
translation stabilizers. It does not produce a nonzero stabilizer.
-/
noncomputable section
open Set MeasureTheory Function Filter Metric
open scoped Topology ENNReal NNReal
namespace VV.BBEKOneRootRecurrence
open BBEKLeafwiseStabilizer BBEKLeafAtomDichotomy BBEKOneRootAtoms

section Recurrence
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

theorem eigen_pow_le_ball_double_radius (η : Measure U) {r : ℝ}
    (hunit : η (ball (0 : U) r) = 1) {u : U} {c : ℝ≥0}
    (heigen : translate u η = c • η) (k : ℕ) (hsmall : ‖k • u‖ < r) :
    (c : ℝ≥0∞)^k ≤ η (ball (0 : U) (2*r)) := by
  have hsub : (k • u + ·) ⁻¹' ball (0 : U) r ⊆ ball (0 : U) (2*r) := by
    intro x hx
    have hxnorm : ‖k • u + x‖ < r := by simpa only [mem_preimage,mem_ball,dist_zero_right] using hx
    have ht := norm_sub_le (k • u + x) (k • u)
    have he : k • u + x - k • u = x := by abel
    rw [he] at ht
    simpa only [mem_ball,dist_zero_right] using (show ‖x‖ < 2*r by linarith)
  have he := congrArg (fun m : Measure U => m (ball (0 : U) r))
    (translate_nsmul_of_eigen η heigen k)
  dsimp only at he
  rw [translate_apply _ _ isOpen_ball.measurableSet,Measure.smul_apply,hunit] at he
  simp only [ENNReal.smul_def,ENNReal.coe_pow,smul_eq_mul,mul_one] at he
  exact he.symm.le.trans (measure_mono hsub)


variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  {T : X → X}

theorem ae_translation_multiplier_eq_one_radius
    (hT : MeasurePreserving T μ μ) (η : X → Measure U) {r : ℝ} (hr : 0 < r)
    (hmass : Measurable (fun x => η x (ball (0 : U) (2*r))))
    (hnorm : ∀ᵐ x ∂μ, η x (ball (0 : U) r) = 1)
    (hfinite : ∀ᵐ x ∂μ, η x (ball (0 : U) (2*r)) ≠ ∞)
    (σ : U ≃+ U) (hσ : Measurable σ)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, ∀ (u : U) (c : ℝ≥0), c ≠ 0 → translate u (η x) = c • η x → c = 1 := by
  classical
  let S (M : ℕ) : Set X := {x | η x (ball (0 : U) (2*r)) ≤ M}
  have hS (M : ℕ) : MeasurableSet (S M) := measurableSet_le hmass measurable_const
  have hreturn : ∀ᵐ x ∂μ, ∀ M : ℕ, x ∈ S M → ∃ᶠ n : ℕ in atTop, (T^[n]) x ∈ S M := by
    apply ae_all_iff.mpr
    intro M
    exact hT.conservative.ae_mem_imp_frequently_image_mem (hS M).nullMeasurableSet
  have hnormAll : ∀ᵐ x ∂μ, ∀ n : ℕ, η ((T^[n]) x) (ball (0 : U) r) = 1 := by
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
    have hsmall : ∀ᶠ n : ℕ in atTop, ‖k • (σ^[n]) u‖ < r := by
      have hc := (continuous_nsmul k).continuousAt.tendsto.comp (hcontract u)
      have hc' : Tendsto (fun n => ‖k • (σ^[n]) u‖) atTop (𝓝 (0 : ℝ)) := by
        simpa only [nsmul_zero,norm_zero] using hc.norm
      exact hc'.eventually (gt_mem_nhds hr)
    obtain ⟨n,hn,hsmalln⟩ := (hreturns.and_eventually hsmall).exists
    have hb := eigen_pow_le_ball_double_radius (η ((T^[n]) x)) (hxnorm n) (hiter n) k hsmalln
    have hk' : (M : ℝ≥0∞) < (c : ℝ≥0∞)^k := by exact_mod_cast hk
    exact (not_le_of_gt hk') (hb.trans hn)
  intro u c hc heigen
  have hupper := hle u c heigen
  have hinv := hle (-u) c⁻¹ (translate_neg_of_eigen (η x) hc heigen)
  exact le_antisymm hupper ((inv_le_one₀ (pos_iff_ne_zero.mpr hc)).mp hinv)


end Recurrence

open BBEKDynamics BBEKQuotient BBEKRootLeafKernel BBEKOneRootCovariance
open BBEKOneRootUpper
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

section Scalar
variable {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F] [ProperSpace F]

theorem scalar_projective_stabilizer_eq {μ : Measure X} [IsFiniteMeasure μ]
    (g : G) (hT : MeasurePreserving (fun q : X => g⁻¹ • q) μ μ)
    (η : X → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hfinite : ∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q))
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    {a : F} (ha : a ≠ 0) (hsmall : ‖a⁻¹‖ < 1)
    (hcov : ∀ᵐ q ∂μ,
      η (g • q) = ((η q).map (a * ·) (ball 0 r))⁻¹ • (η q).map (a * ·) ∧
      0 < (η q).map (a * ·) (ball 0 r) ∧ (η q).map (a * ·) (ball 0 r) ≠ ∞) :
    ∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = translationStabilizer (η q) := by
  let σ := rootDilation a ha
  have hs : Measurable σ := (continuous_const.mul continuous_id).measurable
  have hsi : Measurable σ.symm := (continuous_const.mul continuous_id).measurable
  have hnorm (u : F) : ‖σ.symm u‖ ≤ ‖u‖ := by
    change ‖a⁻¹ * u‖ ≤ ‖u‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg u) hsmall.le
  have hcontract (u : F) : Tendsto (fun n : ℕ => (σ.symm^[n]) u) atTop (𝓝 0) := by
    have he : σ.symm = rootDilation a⁻¹ (inv_ne_zero ha) := by
      apply AddEquiv.ext
      intro v
      rfl
    rw [he]
    exact rootDilation_contracts (inv_ne_zero ha) hsmall u
  have hcovNN : ∀ᵐ q ∂μ, ∃ d : ℝ≥0,
      η (g⁻¹ • q) = d • Measure.map σ.symm (η q) := by
    filter_upwards [inverse_covariance g hT η σ hs hsi hcov, hnormal,
      hT.quasiMeasurePreserving.ae hnormal] with q hq hn hnT
    obtain ⟨d, hd⟩ := hq
    have hdle := normalization_scalar_le_one (η q) (η (g⁻¹ • q)) hn hnT
      σ.symm hsi hnorm hd
    have hdne : d ≠ ∞ := ne_of_lt (hdle.trans_lt ENNReal.one_lt_top)
    refine ⟨d.toNNReal, ?_⟩
    simpa only [ENNReal.smul_def, ENNReal.coe_toNNReal hdne] using hd
  have hball : ∀ᵐ q ∂μ, η q (ball 0 (2*r)) ≠ ∞ := by
    filter_upwards [hfinite] with q hq
    letI := hq
    exact measure_ball_ne_top
  have hm := ae_translation_multiplier_eq_one_radius hT η hr
    ((Measure.measurable_coe isOpen_ball.measurableSet).comp hη)
    hnormal hball σ.symm hsi hcontract hcovNN
  filter_upwards [hm] with q hq
  apply le_antisymm _ (translationStabilizer_le_projective (η q))
  rintro u ⟨c, hc, hu⟩
  rw [hq u c hc hu, one_smul] at hu
  exact hu
end Scalar
/-- The canonical real_lower family has only exact projective translations.
Its actual chart construction and atom dichotomy are retained. -/
theorem exists_real_lower_exact_stabilizer_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) ∧
      (∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = translationStabilizer (η q)) := by
  obtain ⟨r, hr, η, hη, hgood, hcov, hcanonical⟩ :=
    exists_real_lower_covariant_data μ hK hμK ht hT
  refine ⟨r, hr, η, hη, hgood, hcanonical, ?_, ?_⟩
  · exact scalar_atom_dichotomy (psi t 1) hT η hη hr
      (hgood.mono fun _ hq => hq.2.2.1) (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  · exact scalar_projective_stabilizer_eq (psi t 1) hT η hη hr
      (hgood.mono fun _ hq => hq.1) (hgood.mono fun _ hq => hq.2.2.1)
      (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
/-- The canonical padic_lower family has only exact projective translations.
Its actual chart construction and atom dichotomy are retained. -/
theorem exists_padic_lower_exact_stabilizer_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) ∧
      (∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = translationStabilizer (η q)) := by
  obtain ⟨r, hr, η, hη, hgood, hcov, hcanonical⟩ :=
    exists_padic_lower_covariant_data μ hK hμK ht hT
  refine ⟨r, hr, η, hη, hgood, hcanonical, ?_, ?_⟩
  · exact scalar_atom_dichotomy (psi t 1) hT η hη hr
      (hgood.mono fun _ hq => hq.2.2.1) (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  · exact scalar_projective_stabilizer_eq (psi t 1) hT η hη hr
      (hgood.mono fun _ hq => hq.1) (hgood.mono fun _ hq => hq.2.2.1)
      (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
/-- The canonical real_upper family has only exact projective translations.
Its actual chart construction and atom dichotomy are retained. -/
theorem exists_real_upper_exact_stabilizer_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure ℝ, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily realSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) ∧
      (∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = translationStabilizer (η q)) := by
  obtain ⟨r, hr, η, hη, hgood, hcov, hcanonical⟩ :=
    exists_real_upper_covariant_data μ hK hμK ht hT
  have hTi : MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ := by
    simpa only [inv_inv] using hT
  refine ⟨r, hr, η, hη, hgood, hcanonical, ?_, ?_⟩
  · exact scalar_atom_dichotomy ((psi t 1)⁻¹) hTi η hη hr
      (hgood.mono fun _ hq => hq.2.2.1) (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
  · exact scalar_projective_stabilizer_eq ((psi t 1)⁻¹) hTi η hη hr
      (hgood.mono fun _ hq => hq.1) (hgood.mono fun _ hq => hq.2.2.1)
      (Real.exp_ne_zero _) (real_inverse_scaling_norm_lt_one ht) hcov
/-- The canonical padic_upper family has only exact projective translations.
Its actual chart construction and atom dichotomy are retained. -/
theorem exists_padic_upper_exact_stabilizer_data (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Q2, Measurable η ∧
      (∀ᵐ q ∂μ, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
        ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      IsConstructedUpperRootFamily padicSplit μ t r η ∧
      (∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) ∧
      (∀ᵐ q ∂μ, projectiveTranslationStabilizer (η q) = translationStabilizer (η q)) := by
  obtain ⟨r, hr, η, hη, hgood, hcov, hcanonical⟩ :=
    exists_padic_upper_covariant_data μ hK hμK ht hT
  have hTi : MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ := by
    simpa only [inv_inv] using hT
  refine ⟨r, hr, η, hη, hgood, hcanonical, ?_, ?_⟩
  · exact scalar_atom_dichotomy ((psi t 1)⁻¹) hTi η hη hr
      (hgood.mono fun _ hq => hq.2.2.1) (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov
  · exact scalar_projective_stabilizer_eq ((psi t 1)⁻¹) hTi η hη hr
      (hgood.mono fun _ hq => hq.1) (hgood.mono fun _ hq => hq.2.2.1)
      (zpow_ne_zero _ (by norm_num)) padic_inverse_scaling_norm_lt_one hcov

end VV.BBEKOneRootRecurrence

