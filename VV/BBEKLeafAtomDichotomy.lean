import VV.BBEKLeafwiseRecurrence
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Analysis.SpecificLimits.Basic

/-! Atoms in normalized contracting leaf families.  Recurrence is derived
from preservation of the finite base measure, not assumed separately. -/

noncomputable section
open Set MeasureTheory Function Filter Metric
open scoped Topology ENNReal

namespace VV.BBEKLeafAtomDichotomy
open BBEKLeafwiseStabilizer

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X}

theorem ae_eq_of_comp_le (hT : MeasurePreserving T μ μ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hle : ∀ᵐ x ∂μ, f (T x) ≤ f x) :
    ∀ᵐ x ∂μ, f (T x) = f x := by
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, f (T ((T^[n]) x)) ≤ f ((T^[n]) x) :=
    ae_all_iff.mpr fun n => (hT.iterate n).quasiMeasurePreserving.ae hle
  filter_upwards [ae_observable_recurrent_subseq hT hf,hall] with x hx hsteps
  obtain ⟨k,hk,hlim⟩ := hx
  have hanti : Antitone (fun n : ℕ => f ((T^[n]) x)) := by
    apply antitone_nat_of_succ_le
    intro n
    simpa only [Function.iterate_succ_apply'] using hsteps n
  apply le_antisymm (by simpa using hsteps 0)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with j hj
  simpa using hanti (show 1 ≤ k j from hj.trans (hk.id_le j))

theorem ae_eq_of_le_comp (hT : MeasurePreserving T μ μ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hle : ∀ᵐ x ∂μ, f x ≤ f (T x)) :
    ∀ᵐ x ∂μ, f (T x) = f x := by
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, f ((T^[n]) x) ≤ f (T ((T^[n]) x)) :=
    ae_all_iff.mpr fun n => (hT.iterate n).quasiMeasurePreserving.ae hle
  filter_upwards [ae_observable_recurrent_subseq hT hf,hall] with x hx hsteps
  obtain ⟨k,hk,hlim⟩ := hx
  have hmono : Monotone (fun n : ℕ => f ((T^[n]) x)) := by
    apply monotone_nat_of_le_succ
    intro n
    simpa only [Function.iterate_succ_apply'] using hsteps n
  apply le_antisymm _ (by simpa using hsteps 0)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with j hj
  simpa using hmono (show 1 ≤ k j from hj.trans (hk.id_le j))

variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]

theorem normalization_scalar_le_one (η ν : Measure U) {r : ℝ}
    (hη : η (ball 0 r) = 1) (hν : ν (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    {d : ℝ≥0∞} (hd : ν = d • Measure.map σ η) : d ≤ 1 := by
  have hsub : ball (0 : U) r ⊆ σ ⁻¹' ball 0 r := by
    intro u hu
    simpa only [mem_preimage,mem_ball,dist_zero_right] using
      (hnorm u).trans_lt (show ‖u‖ < r by simpa using hu)
  have hmass : 1 ≤ η (σ ⁻¹' ball 0 r) := hη ▸ measure_mono hsub
  have he : d * η (σ ⁻¹' ball 0 r) = 1 := by
    rw [hd,Measure.smul_apply,smul_eq_mul,Measure.map_apply hσ isOpen_ball.measurableSet] at hν
    exact hν
  calc d = d * 1 := (mul_one _).symm
    _ ≤ d * η (σ ⁻¹' ball 0 r) := mul_le_mul_left' hmass d
    _ = 1 := he

theorem map_singleton_zero (η : Measure U) (σ : U ≃+ U) (hσ : Measurable σ) :
    Measure.map σ η {0} = η {0} := by
  rw [Measure.map_apply hσ (measurableSet_singleton 0)]
  congr 1
  ext u
  change σ u = 0 ↔ u = 0
  constructor
  · intro h
    apply σ.injective
    simpa only [map_zero] using h
  · rintro rfl
    exact σ.map_zero

theorem atom_mass_invariant (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ}
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η (T x) {0} = η x {0} := by
  apply ae_eq_of_comp_le hT ((Measure.measurable_coe (measurableSet_singleton 0)).comp hη)
  filter_upwards [hnormal,hT.quasiMeasurePreserving.ae hnormal,hcov] with x hx hTx hc
  obtain ⟨d,hd⟩ := hc
  have hdle := normalization_scalar_le_one (η x) (η (T x)) hx hTx σ hσ hnorm hd
  change η (T x) {0} ≤ η x {0}
  rw [hd,Measure.smul_apply,smul_eq_mul,map_singleton_zero _ σ hσ]
  simpa only [one_mul] using mul_le_mul_right' hdle (η x {0})

theorem exact_covariance_on_atom (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x {0} ≠ 0 → η (T x) = Measure.map σ (η x) := by
  filter_upwards [hnormal,hcov,atom_mass_invariant hT η hη hnormal σ hσ hnorm hcov]
    with x hx hc ha
  intro hatom
  obtain ⟨d,hd⟩ := hc
  have hbound : η x {0} ≤ 1 := by
    rw [← hx]
    exact measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))
  have hfinite : η x {0} ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hbound
  rw [hd,Measure.smul_apply,smul_eq_mul,map_singleton_zero _ σ hσ] at ha
  have hd1 : d = 1 := (ENNReal.mul_eq_right hatom hfinite).mp ha
  simpa only [hd1,one_smul] using hd

omit [MeasurableSpace U] [BorelSpace U] in
theorem preimage_iterate_ball_monotone (σ : U ≃+ U)
    (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖) (r : ℝ) :
    Monotone (fun n : ℕ => (σ^[n]) ⁻¹' ball (0 : U) r) := by
  apply monotone_nat_of_le_succ
  intro n u hu
  simp only [mem_preimage,mem_ball,dist_zero_right] at hu ⊢
  rw [Function.iterate_succ_apply']
  exact (hnorm _).trans_lt hu

omit [MeasurableSpace U] [BorelSpace U] in
theorem iUnion_preimage_iterate_ball (σ : U ≃+ U)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) :
    (⋃ n : ℕ, (σ^[n]) ⁻¹' ball (0 : U) r) = univ := by
  apply Set.eq_univ_of_forall
  intro u
  obtain ⟨n,hn⟩ := ((hcontract u).eventually (ball_mem_nhds (0 : U) hr)).exists
  exact mem_iUnion.mpr ⟨n,hn⟩

omit [BorelSpace U] in
theorem mass_univ_of_iterated_ball_mass (η : Measure U) (σ : U ≃+ U)
    (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) {c : ℝ≥0∞}
    (hmass : ∀ n : ℕ, η ((σ^[n]) ⁻¹' ball (0 : U) r) = c) : η univ = c := by
  rw [← iUnion_preimage_iterate_ball σ hcontract hr,
    (preimage_iterate_ball_monotone σ hnorm r).measure_iUnion]
  simp only [hmass,iSup_const]

theorem iterated_covariance_on_atom (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x {0} ≠ 0 → ∀ n : ℕ,
      η ((T^[n]) x) {0} = η x {0} ∧
      η ((T^[n]) x) = Measure.map (σ^[n]) (η x) ∧
      η ((T^[n]) x) (ball 0 r) = 1 := by
  have hi := atom_mass_invariant hT η hη hnormal σ hσ hnorm hcov
  have he := exact_covariance_on_atom hT η hη hr hnormal σ hσ hnorm hcov
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      η (T ((T^[n]) x)) {0} = η ((T^[n]) x) {0} ∧
      (η ((T^[n]) x) {0} ≠ 0 →
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

/-- A nonzero central atom forces finite total mass one.  This conclusion
is derived from recurrence, exact projective covariance, and contraction. -/
theorem probability_on_atom (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x {0} ≠ 0 → η x univ = 1 := by
  filter_upwards [iterated_covariance_on_atom hT η hη hr hnormal σ hσ hnorm hcov]
    with x hx
  intro ha
  apply mass_univ_of_iterated_ball_mass (η x) σ hnorm hcontract hr
  intro n
  have hn := (hx ha n).2.2
  rw [(hx ha n).2.1,Measure.map_apply (hσ.iterate n) isOpen_ball.measurableSet] at hn
  exact hn

theorem ball_mass_one_on_atom (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ, η x {0} ≠ 0 → η x (ball 0 ε) = 1 := by
  classical
  let b : X → ℝ≥0∞ := fun x => if η x {0} = 0 then 0 else η x (ball 0 ε)
  have hb : Measurable b := by
    apply Measurable.ite _ measurable_const
      ((Measure.measurable_coe isOpen_ball.measurableSet).comp hη)
    exact ((Measure.measurable_coe (measurableSet_singleton 0)).comp hη)
      (measurableSet_singleton 0)
  have hatom := atom_mass_invariant hT η hη hnormal σ hσ hnorm hcov
  have hexact := exact_covariance_on_atom hT η hη hr hnormal σ hσ hnorm hcov
  have hmono : ∀ᵐ x ∂μ, b x ≤ b (T x) := by
    filter_upwards [hatom,hexact] with x hx hc
    by_cases ha : η x {0} = 0
    · simp only [b,hx,ha,if_pos]
      exact le_rfl
    · simp only [b,hx,ha,if_false]
      rw [hc ha,Measure.map_apply hσ isOpen_ball.measurableSet]
      exact measure_mono (preimage_iterate_ball_monotone σ hnorm ε (show 0 ≤ 1 by omega))
  have hbInv := ae_eq_of_le_comp hT hb hmono
  have hbAll : ∀ᵐ x ∂μ, ∀ n : ℕ, b (T ((T^[n]) x)) = b ((T^[n]) x) :=
    ae_all_iff.mpr fun n => (hT.iterate n).quasiMeasurePreserving.ae hbInv
  filter_upwards [hbAll,iterated_covariance_on_atom hT η hη hr hnormal σ hσ hnorm hcov,
    probability_on_atom hT η hη hr hnormal σ hσ hnorm hcontract hcov] with x hx hiter hprob
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

/-- The central-atom dichotomy for an actual measurable contracting leaf
family: either the central atom vanishes, or the entire measure is Dirac.
No total-finiteness or recurrence conclusion is included as an input. -/
theorem ae_zero_atom_or_dirac (hT : MeasurePreserving T μ μ)
    (η : X → Measure U) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnormal : ∀ᵐ x ∂μ, η x (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hnorm : ∀ u, ‖σ u‖ ≤ ‖u‖)
    (hcontract : ∀ u, Tendsto (fun n : ℕ => (σ^[n]) u) atTop (𝓝 0))
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0∞, η (T x) = d • Measure.map σ (η x)) :
    ∀ᵐ x ∂μ, η x {0} = 0 ∨ η x = Measure.dirac 0 := by
  have hb : ∀ᵐ x ∂μ, ∀ n : ℕ, η x {0} ≠ 0 → η x (ball 0 (1 / ((n : ℝ)+1))) = 1 :=
    ae_all_iff.mpr fun n =>
      ball_mass_one_on_atom hT η hη hr hnormal σ hσ hnorm hcontract hcov (by positivity)
  filter_upwards [hb,probability_on_atom hT η hη hr hnormal σ hσ hnorm hcontract hcov]
    with x hx hprob
  by_cases ha : η x {0} = 0
  · exact Or.inl ha
  right
  letI : IsProbabilityMeasure (η x) := ⟨hprob ha⟩
  have hballs : ∀ᵐ u ∂η x, ∀ n : ℕ, u ∈ ball (0 : U) (1 / ((n : ℝ)+1)) :=
    ae_all_iff.mpr fun n => (mem_ae_iff_prob_eq_one isOpen_ball.measurableSet).mpr (hx n ha)
  have hz : ∀ᵐ u ∂η x, u = 0 := by
    filter_upwards [hballs] with u hu
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
    exact .of_forall fun n => (show ‖u‖ < 1 / ((n : ℝ)+1) by simpa using hu n).le
  have he : Measure.map (id : U → U) (η x) = Measure.map (fun _ : U => 0) (η x) :=
    Measure.map_congr hz
  simpa only [Measure.map_id,Measure.map_const,measure_univ,one_smul] using he

end VV.BBEKLeafAtomDichotomy
