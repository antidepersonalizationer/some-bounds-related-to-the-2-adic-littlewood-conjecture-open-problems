import VV.BBEKLeafAtomDichotomy
import VV.BBEKRealStabilizerField
import VV.BBEKPadicStabilizerField
import Mathlib.NumberTheory.Padics.ProperSpace

/-! Finite contracting canonical leaf measures are Dirac. Together with the
real and p-adic closed subgroup structures this establishes the full-root
support threshold. No positive entropy premise is converted to non-Dirac
here, and no leaf symmetry is presumed. -/
noncomputable section
open Set MeasureTheory Function Filter Metric
open scoped Topology ENNReal
namespace VV.BBEKLeafSupportGeneration
open BBEKLeafwiseStabilizer BBEKLeafAtomDichotomy
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X}
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]

theorem total_mass_invariant (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ}
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η (T x) univ = η x univ := by
  apply ae_eq_of_comp_le hT ((Measure.measurable_coe MeasurableSet.univ).comp hη)
  filter_upwards [hnormal,hT.quasiMeasurePreserving.ae hnormal,hcov] with x hx hTx hc
  obtain ⟨d,hd⟩ := hc
  have hdle := normalization_scalar_le_one (η x) (η (T x)) hx hTx σ hσ hnorm hd
  change η (T x) univ ≤ η x univ
  rw [hd,Measure.smul_apply,smul_eq_mul,Measure.map_apply hσ MeasurableSet.univ,preimage_univ]
  simpa only [one_mul] using mul_le_mul_right' hdle (η x univ)

theorem exact_covariance_on_finite (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x univ ≠ ∞ → η (T x) = Measure.map σ (η x) := by
  filter_upwards [hnormal,hcov,total_mass_invariant hT η hη hnormal σ hσ hnorm hcov]
    with x hx hc ha
  intro hfinite
  obtain ⟨d,hd⟩ := hc
  have hpositive : η x univ ≠ 0 := by
    have hh : 1 ≤ η x univ := hx ▸ measure_mono (subset_univ _)
    exact ne_of_gt (zero_lt_one.trans_le hh)
  rw [hd,Measure.smul_apply,smul_eq_mul,Measure.map_apply hσ MeasurableSet.univ,
    preimage_univ] at ha
  have hd1 : d = 1 := (ENNReal.mul_eq_right hpositive hfinite).mp ha
  simpa only [hd1,one_smul] using hd
theorem iterated_covariance_on_finite (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x univ ≠ ∞ → ∀ n : ℕ,
      η ((T^[n]) x) univ = η x univ ∧
      η ((T^[n]) x) = Measure.map (σ^[n]) (η x) ∧
      η ((T^[n]) x) (ball 0 r) = 1 := by
  have hi := total_mass_invariant hT η hη hnormal σ hσ hnorm hcov
  have he := exact_covariance_on_finite hT η hη hr hnormal σ hσ hnorm hcov
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      η (T ((T^[n]) x)) univ = η ((T^[n]) x) univ ∧
      (η ((T^[n]) x) univ ≠ ∞ →
        η (T ((T^[n]) x)) = Measure.map σ (η ((T^[n]) x))) ∧
      η ((T^[n]) x) (ball 0 r) = 1 := by
    apply ae_all_iff.mpr
    intro n
    exact (hT.iterate n).quasiMeasurePreserving.ae (hi.and (he.and hnormal))
  filter_upwards [hall] with x hx
  intro ha n
  induction n with
  | zero => exact ⟨rfl,by simp,(hx 0).2.2⟩
  | succ n ih =>
    refine ⟨?_,?_,(hx (n+1)).2.2⟩
    · simpa only [Function.iterate_succ_apply'] using (hx n).1.trans ih.1
    · rw [Function.iterate_succ_apply',(hx n).2.1 (ih.1 ▸ ha),ih.2.1,
        Measure.map_map hσ (hσ.iterate n)]
      congr 1
      funext u
      exact (Function.iterate_succ_apply' σ n u).symm

/-- Finite total mass forces total mass one. This conclusion
is derived from recurrence, exact projective covariance, and contraction. -/
theorem probability_on_finite (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x univ ≠ ∞ → η x univ = 1 := by
  filter_upwards [iterated_covariance_on_finite hT η hη hr hnormal σ hσ hnorm hcov]
    with x hx
  intro ha
  apply mass_univ_of_iterated_ball_mass (η x) σ hnorm hcontract hr
  intro n
  have hn := (hx ha n).2.2
  rw [(hx ha n).2.1,Measure.map_apply (hσ.iterate n) isOpen_ball.measurableSet] at hn
  exact hn

theorem ball_mass_one_on_finite (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ, η x univ ≠ ∞ → η x (ball 0 ε) = 1 := by
  classical
  let b : X → ℝ≥0∞ := fun x => if η x univ = ∞ then 0 else η x (ball 0 ε)
  have hb : Measurable b := by
    apply Measurable.ite _ measurable_const
      ((Measure.measurable_coe isOpen_ball.measurableSet).comp hη)
    exact ((Measure.measurable_coe MeasurableSet.univ).comp hη)
      (measurableSet_singleton ∞)
  have hatom := total_mass_invariant hT η hη hnormal σ hσ hnorm hcov
  have hexact := exact_covariance_on_finite hT η hη hr hnormal σ hσ hnorm hcov
  have hmono : ∀ᵐ x ∂μ, b x ≤ b (T x) := by
    filter_upwards [hatom,hexact] with x hx hc
    by_cases ha : η x univ = ∞
    · simp only [b,hx,ha,if_pos]
      exact le_rfl
    · simp only [b,hx,ha,if_false]
      rw [hc ha,Measure.map_apply hσ isOpen_ball.measurableSet]
      exact measure_mono (preimage_iterate_ball_monotone σ hnorm ε (show 0 ≤ 1 by omega))
  have hbInv := ae_eq_of_le_comp hT hb hmono
  have hbAll : ∀ᵐ x ∂μ, ∀ n : ℕ, b (T ((T^[n]) x)) = b ((T^[n]) x) :=
    ae_all_iff.mpr fun n => (hT.iterate n).quasiMeasurePreserving.ae hbInv
  filter_upwards [hbAll,iterated_covariance_on_finite hT η hη hr hnormal σ hσ hnorm hcov,
    probability_on_finite hT η hη hr hnormal σ hσ hnorm hcontract hcov] with x hx hiter hprob
  intro ha
  have hbIter (n : ℕ) : b ((T^[n]) x) = b x := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',hx n,ih]
  have hmass (n : ℕ) : η x ((σ^[n]) ⁻¹' ball 0 ε) = η x (ball 0 ε) := by
    have hh := hbIter n
    simp only [b,(hiter ha n).1,ha,if_false] at hh
    rwa [(hiter ha n).2.1,Measure.map_apply (hσ.iterate n) isOpen_ball.measurableSet] at hh
  exact (mass_univ_of_iterated_ball_mass (η x) σ hnorm hcontract hε hmass).symm.trans (hprob ha)

/-- The finite-total-mass event consists only of Dirac leaves. The event is
not assumed conull, and the conclusion concerns the original family. -/
theorem ae_finite_implies_dirac (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x univ ≠ ∞ → η x = Measure.dirac 0 := by
  have hb : ∀ᵐ x ∂μ, ∀ n : ℕ, η x univ ≠ ∞ → η x (ball 0 (1 / ((n : ℝ)+1))) = 1 :=
    ae_all_iff.mpr fun n =>
      ball_mass_one_on_finite hT η hη hr hnormal σ hσ hnorm hcontract hcov (by positivity)
  filter_upwards [hb,probability_on_finite hT η hη hr hnormal σ hσ hnorm hcontract hcov]
    with x hx hprob
  intro hfinite
  letI : IsProbabilityMeasure (η x) := ⟨hprob hfinite⟩
  have hballs : ∀ᵐ u ∂η x, ∀ n : ℕ, u ∈ ball (0 : U) (1 / ((n : ℝ)+1)) :=
    ae_all_iff.mpr fun n => (mem_ae_iff_prob_eq_one isOpen_ball.measurableSet).mpr (hx n hfinite)
  have hz : ∀ᵐ u ∂η x, u = 0 := by
    filter_upwards [hballs] with u hu
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
    exact .of_forall fun n => (show ‖u‖ < 1 / ((n : ℝ)+1) by simpa using hu n).le
  have he : Measure.map (id : U → U) (η x) = Measure.map (fun _ : U => 0) (η x) :=
    Measure.map_congr hz
  simpa only [Measure.map_id,Measure.map_const,measure_univ,one_smul] using he

/-- Positive mass in every centered ball and a zero central atom exclude
support in every proper closed real additive subgroup. -/
theorem real_supported_subgroup_eq_top (η : Measure ℝ)
    (hpos : ∀ ε : ℝ, 0 < ε → 0 < η (ball 0 ε)) (hzero : η {0} = 0)
    (S : AddSubgroup ℝ) (hclosed : IsClosed (S : Set ℝ))
    (hsupport : ∀ᵐ u ∂η, u ∈ S) : S = ⊤ := by
  by_contra htop
  have hnd : ¬ Dense (S : Set ℝ) := by
    intro hd
    exact htop (SetLike.coe_injective (hclosed.closure_eq ▸ hd.closure_eq))
  have hgap : ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ S, 0 < u → ε ≤ u := by
    by_contra hn
    push_neg at hn
    apply hnd
    exact S.dense_of_not_isolated_zero (fun ε hε => hn ε hε)
  obtain ⟨ε,hε,hgap⟩ := hgap
  have hle : η (ball 0 ε) ≤ η {0} := by
    apply measure_mono_ae
    filter_upwards [hsupport] with u hu hb
    have huabs : |u| ∈ S := by
      by_cases h : 0 ≤ u
      · simpa only [abs_of_nonneg h] using hu
      · simpa only [abs_of_neg (lt_of_not_ge h)] using S.neg_mem hu
    have huε : |u| < ε := by
      change dist u 0 < ε at hb
      simpa only [Real.dist_eq,sub_zero] using hb
    change u = 0
    by_cases hz : u = 0
    · exact hz
    · exact False.elim ((not_lt_of_ge (hgap |u| huabs (abs_pos.mpr hz))) huε)
  rw [hzero] at hle
  exact not_le_of_gt (hpos ε hε) hle

/-- A locally finite measure supported in a proper closed p-adic additive
subgroup has finite total mass: that subgroup is bounded and hence lies in
a compact ball. -/
theorem padic_finite_of_supported_proper {p : ℕ} [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (η : Measure ℚ_[p]) [IsLocallyFiniteMeasure η]
    (S : AddSubgroup ℚ_[p]) (hclosed : IsClosed (S : Set ℚ_[p])) (hproper : S ≠ ⊤)
    (hsupport : ∀ᵐ u ∂η, u ∈ S) : η univ ≠ ∞ := by
  have hb : BddAbove (subgroupNorms S) := by
    by_contra hn
    exact hproper (padic_closed_subgroup_eq_top_of_unbounded S hclosed hn)
  obtain ⟨R,hR⟩ := hb
  have hle : η univ ≤ η (closedBall 0 R) := by
    apply measure_mono_ae
    filter_upwards [hsupport] with u hu _
    exact (mem_closedBall_zero_iff).mpr (hR ⟨u,hu,rfl⟩)
  exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne hle

/-- Non-Dirac real leaves are not carried by any proper closed additive
root subgroup. The non-Dirac premise is not deduced from entropy here. -/
theorem ae_real_nonDirac_full_root_support (hT : MeasurePreserving T μ μ)
    (η : X → Measure ℝ) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (hpos : ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → 0 < η x (ball 0 ε))
    (σ : ℝ ≃+ ℝ) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x ≠ Measure.dirac 0 →
      ∀ S : AddSubgroup ℝ, IsClosed (S : Set ℝ) → (∀ᵐ u ∂η x, u ∈ S) → S = ⊤ := by
  filter_upwards [ae_zero_atom_or_dirac hT η hη hr hnormal σ hσ hnorm hcontract hcov,hpos]
    with x hx hp hn S hS hsupport
  exact real_supported_subgroup_eq_top (η x) hp (hx.resolve_right hn) S hS hsupport

/-- The corresponding p-adic support threshold follows from finite-mass
recurrence, without assuming a p-adic proper subgroup is discrete. -/
theorem ae_padic_nonDirac_full_root_support {p : ℕ} [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (hT : MeasurePreserving T μ μ)
    (η : X → Measure ℚ_[p]) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (hfinite : ∀ᵐ x ∂μ, IsLocallyFiniteMeasure (η x))
    (σ : ℚ_[p] ≃+ ℚ_[p]) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x ≠ Measure.dirac 0 →
      ∀ S : AddSubgroup ℚ_[p], IsClosed (S : Set ℚ_[p]) → (∀ᵐ u ∂η x, u ∈ S) → S = ⊤ := by
  filter_upwards [ae_finite_implies_dirac hT η hη hr hnormal σ hσ hnorm hcontract hcov,hfinite]
    with x hx hf hn S hS hsupport
  letI := hf
  by_contra hproper
  exact hn (hx (padic_finite_of_supported_proper (η x) S hS hproper hsupport))

end VV.BBEKLeafSupportGeneration


