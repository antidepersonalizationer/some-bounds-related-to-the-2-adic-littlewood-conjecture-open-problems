import VV.BBEKShearNonconcentration
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! A measurable family version of quadratic nonconcentration. Countably
many dense coefficient tests produce measurable good sets; compactness at
each leaf and continuity from below then give one threshold on a large set. -/
noncomputable section
open Set MeasureTheory Filter Metric TopologicalSpace
open scoped Topology ENNReal
namespace VV.BBEKShearFamilyNonconcentration
open BBEKShearNonconcentration
variable {F Z : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
  [ProperSpace F] [SecondCountableTopology F] [MeasurableSpace Z]
  {μ : Measure Z} [IsProbabilityMeasure μ]

/-- A common sublevel threshold for a measurable family of finite nonatomic
root measures, outside a set of arbitrarily small base measure. -/
theorem exists_uniform_sublevel_good_set
    (ν : Z → Measure F) (hν : Measurable ν)
    (hgood : ∀ᵐ q ∂μ, IsFiniteMeasure (ν q) ∧ NoAtoms (ν q))
    {c R κ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 ≤ R) (hκ : 0 < κ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Q : Set Z, MeasurableSet Q ∧ 1-κ < μ.real Q ∧
      ∀ q ∈ Q, ∀ a b : F, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → c ≤ max ‖a‖ ‖b‖ →
        ν q {v | ‖v‖ ≤ R ∧ ‖a*v+b*v^2‖ ≤ δ} < ε := by
  classical
  let C := coefficientAnnulus F c
  have hC : IsCompact C := isCompact_coefficientAnnulus c
  have hC0 : ∀ p ∈ C, p ≠ 0 := by
    intro p hp h0
    have := hp.1
    rw [h0,norm_zero] at this
    exact (not_le_of_gt hc) this
  have hCne : Nonempty C := ⟨⟨(1,0),by
    constructor
    · simpa only [Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one] using hc1
    · simp only [Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one,le_refl]⟩⟩
  letI := hCne
  let d : ℕ → C := denseSeq C
  have hd : DenseRange d := denseRange_denseSeq C
  let τ : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
  have hτ : ∀ n, 0 < τ n := by intro n; dsimp [τ]; positivity
  have hτanti : Antitone τ := by
    intro n m hnm
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  let E : ℕ → ℕ → Set F := fun n j =>
    {v | ‖v‖ ≤ R ∧ ‖shearPolynomial (d j).val v‖ ≤ 2 * τ n}
  have hE : ∀ n j, MeasurableSet (E n j) := by
    intro n j
    exact (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le (continuous_shearPolynomial _).norm.measurable measurable_const)
  let Q : ℕ → Set Z := fun n => {q | ∀ j : ℕ, ν q (E n j) < ε}
  have hQ : ∀ n, MeasurableSet (Q n) := by
    intro n
    have he : Q n = ⋂ j : ℕ, {q | ν q (E n j) < ε} := by ext q; simp [Q]
    rw [he]
    exact MeasurableSet.iInter fun j => measurableSet_lt
      ((Measure.measurable_coe (hE n j)).comp hν) measurable_const
  have hQmono : Monotone Q := by
    intro n m hnm q hq j
    apply lt_of_le_of_lt (measure_mono ?_) (hq j)
    intro v hv
    exact ⟨hv.1,hv.2.trans (mul_le_mul_of_nonneg_left (hτanti hnm) (by norm_num))⟩
  have hcover : ∀ᵐ q ∂μ, q ∈ ⋃ n, Q n := by
    filter_upwards [hgood] with q hq
    letI : IsFiniteMeasure (ν q) := hq.1
    letI : NoAtoms (ν q) := hq.2
    obtain ⟨δ,hδ,hδbound⟩ := uniform_small_sublevels (ν q) hC hC0 hR hε
    have hlim : Tendsto (fun n => 2 * τ n) atTop (𝓝 0) := by
      simpa [τ] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2
    obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
    refine mem_iUnion.mpr ⟨n,?_⟩
    intro j
    apply lt_of_le_of_lt (measure_mono ?_) (hδbound (d j).val (d j).property)
    intro v hv
    exact ⟨hv.1,hv.2.trans hn.le⟩
  have hmass : μ (⋃ n, Q n) = 1 := by
    have heq : (⋃ n, Q n) =ᵐ[μ] univ := by
      filter_upwards [hcover] with q hq
      exact propext ⟨fun _ => mem_univ q,fun _ => hq⟩
    exact (measure_congr heq).trans measure_univ
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) hQmono
  rw [hmass] at hlim
  have hreal : Tendsto (fun n => μ.real (Q n)) atTop (𝓝 1) := by
    simpa only [ENNReal.toReal_one] using (ENNReal.tendsto_toReal (by simp : (1:ℝ≥0∞) ≠ ∞)).comp hlim
  obtain ⟨n,hn⟩ := (hreal.eventually (lt_mem_nhds (by linarith : 1-κ < 1))).exists
  refine ⟨τ n,hτ n,Q n,hQ n,hn,?_⟩
  intro q hq a b ha hb hab
  let p : C := ⟨(a,b),⟨hab,max_le ha hb⟩⟩
  let L := R+R^2+1
  have hL : 0 < L := by dsimp [L]; nlinarith
  obtain ⟨j,hj⟩ := hd.exists_dist_lt p (div_pos (hτ n) hL)
  have hdist : dist (d j).val p.val * L < τ n := by
    rw [dist_comm]
    exact (lt_div_iff₀ hL).mp hj
  apply lt_of_le_of_lt (measure_mono ?_) (hq j)
  intro v hv
  refine ⟨hv.1,?_⟩
  have hdiff := polynomial_difference_le (d j).val p.val hv.1
  have hnorm : ‖shearPolynomial (d j).val v‖ ≤
      ‖shearPolynomial (d j).val v - shearPolynomial p.val v‖ + ‖shearPolynomial p.val v‖ := by
    simpa only [sub_add_cancel] using (norm_add_le
      (shearPolynomial (d j).val v - shearPolynomial p.val v) (shearPolynomial p.val v))
  have hdnonneg : 0 ≤ dist (d j).val p.val := dist_nonneg
  have hsmall : ‖shearPolynomial p.val v‖ ≤ τ n := hv.2
  dsimp [L] at hdist
  change ‖shearPolynomial (d j).val v‖ ≤ 2 * τ n
  nlinarith




/-- The version directly suited to canonical global leaves, whose total mass
may be infinite. Only the actual radius-r normalization and nonatomicity are
needed; restriction to the normalizing ball is performed inside the proof. -/
theorem exists_uniform_leaf_sublevel_good_set
    (η : Z → Measure F) (hη : Measurable η) {r : ℝ} (hr : 0 < r)
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hnoatom : ∀ᵐ q ∂μ, NoAtoms (η q))
    {c κ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hκ : 0 < κ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Q : Set Z, MeasurableSet Q ∧ 1-κ < μ.real Q ∧
      ∀ q ∈ Q, ∀ a b : F, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → c ≤ max ‖a‖ ‖b‖ →
        η q {v | ‖v‖ < r ∧ ‖a*v+b*v^2‖ ≤ δ} < ε := by
  let ν : Z → Measure F := fun q => (η q).restrict (ball 0 r)
  have hν : Measurable ν := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [ν,Measure.restrict_apply hS]
    exact (Measure.measurable_coe (hS.inter measurableSet_ball)).comp hη
  have hgood : ∀ᵐ q ∂μ, IsFiniteMeasure (ν q) ∧ NoAtoms (ν q) := by
    filter_upwards [hnorm,hnoatom] with q hq hn
    letI : NoAtoms (η q) := hn
    refine ⟨⟨?_⟩,inferInstance⟩
    change (η q).restrict (ball 0 r) univ < ∞
    rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,hq]
    norm_num
  obtain ⟨δ,hδ,Q,hQ,hQmass,hbound⟩ := exists_uniform_sublevel_good_set ν hν hgood
    hc hc1 hr.le hκ hε
  refine ⟨δ,hδ,Q,hQ,hQmass,?_⟩
  intro q hq a b ha hb hab
  have h := hbound q hq a b ha hb hab
  have hS : MeasurableSet {v : F | ‖v‖ ≤ r ∧ ‖a*v+b*v^2‖ ≤ δ} :=
    (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le (continuous_shearPolynomial (a,b)).norm.measurable measurable_const)
  change (η q).restrict (ball 0 r) {v | ‖v‖ ≤ r ∧ ‖a*v+b*v^2‖ ≤ δ} < ε at h
  rw [Measure.restrict_apply hS] at h
  apply lt_of_le_of_lt (measure_mono ?_) h
  intro v hv
  exact ⟨⟨hv.1.le,hv.2⟩,by simpa only [mem_ball,dist_zero_right] using hv.1⟩

end VV.BBEKShearFamilyNonconcentration

