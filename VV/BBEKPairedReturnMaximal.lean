import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The uniform return-frequency estimate used in the low-entropy paired-return
argument.  This is proved directly by Hopf's finite maximal-sum argument; the
large set of points good at every time length is a conclusion, not a premise. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace VV.BBEKPairedReturnMaximal
variable {X : Type*} {T : X → X} {f : X → ℝ}

/-- Maximum of zero and the first `n` Birkhoff sums. -/
def maximalSum (T : X → X) (f : X → ℝ) : ℕ → X → ℝ
  | 0, _ => 0
  | n + 1, q => max 0 (f q + maximalSum T f n (T q))

theorem maximalSum_nonneg (n : ℕ) (q : X) : 0 ≤ maximalSum T f n q := by
  cases n <;> simp [maximalSum]

theorem maximalSum_mono (q : X) : Monotone (fun n => maximalSum T f n q) := by
  have hstep : ∀ n q, maximalSum T f n q ≤ maximalSum T f (n + 1) q := by
    intro n
    induction n with
    | zero => intro q; exact maximalSum_nonneg _ _
    | succ n ih =>
      intro q
      exact max_le_max le_rfl (add_le_add_left (ih (T q)) _)
  exact monotone_nat_of_le_succ (fun n => hstep n q)

theorem birkhoffSum_le_maximalSum (n : ℕ) (q : X) :
    birkhoffSum T f n q ≤ maximalSum T f n q := by
  induction n generalizing q with
  | zero => simp [maximalSum]
  | succ n ih =>
    rw [birkhoffSum_succ']
    exact (add_le_add_left (ih (T q)) _).trans (le_max_right _ _)

theorem exists_maximalSum_eq (n : ℕ) (q : X) :
    ∃ k ≤ n, maximalSum T f n q = birkhoffSum T f k q := by
  induction n generalizing q with
  | zero => exact ⟨0, le_rfl, by simp [maximalSum]⟩
  | succ n ih =>
    rcases ih (T q) with ⟨k, hk, he⟩
    by_cases h : 0 ≤ f q + maximalSum T f n (T q)
    · exact ⟨k+1, Nat.succ_le_succ hk, by rw [maximalSum, max_eq_right h,
        he, birkhoffSum_succ']⟩
    · exact ⟨0, Nat.zero_le _, by simp [maximalSum, max_eq_left (le_of_not_ge h)]⟩

theorem maximalSum_pos_iff (n : ℕ) (q : X) :
    0 < maximalSum T f n q ↔ ∃ k ≤ n, 0 < birkhoffSum T f k q := by
  constructor
  · intro h
    rcases exists_maximalSum_eq n q with ⟨k, hk, he⟩
    exact ⟨k, hk, by rwa [← he]⟩
  · rintro ⟨k, hk, h⟩
    exact h.trans_le ((birkhoffSum_le_maximalSum k q).trans (maximalSum_mono q hk))

variable [MeasurableSpace X] {μ : Measure X}

theorem measurable_maximalSum (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (maximalSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

theorem integrable_maximalSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (n : ℕ) : Integrable (maximalSum T f n) μ := by
  induction n with
  | zero => simp [maximalSum]
  | succ n ih =>
    have hi := hf.add ((hT.integrable_comp ih.aestronglyMeasurable).2 ih)
    simpa only [maximalSum, max_comm] using hi.pos_part

/-- Hopf's finite maximal inequality in its signed integral form. -/
theorem integral_nonneg_on_maximalSum_pos (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (hfm : Measurable f) (n : ℕ) :
    0 ≤ ∫ q in {q | 0 < maximalSum T f n q}, f q ∂μ := by
  let E : Set X := {q | 0 < maximalSum T f n q}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_maximalSum hT.measurable hfm n)
  have hM := integrable_maximalSum hT hf n
  have hMT := (hT.integrable_comp hM.aestronglyMeasurable).2 hM
  have hp : ∀ q, maximalSum T f n q - maximalSum T f n (T q) ≤ E.indicator f q := by
    intro q
    by_cases hq : q ∈ E
    · rw [Set.indicator_of_mem hq]
      cases n with
      | zero => exact False.elim (lt_irrefl (0 : ℝ) hq)
      | succ n =>
        have ht : 0 < f q + maximalSum T f n (T q) := by
          simpa only [E, mem_setOf_eq, maximalSum, lt_max_iff,
            lt_self_iff_false, false_or] using hq
        have hm := maximalSum_mono (T := T) (f := f) (T q) (Nat.le_succ n)
        rw [maximalSum, max_eq_right ht.le]
        linarith
    · rw [Set.indicator_of_notMem hq]
      have hz : maximalSum T f n q = 0 :=
        le_antisymm (le_of_not_gt hq) (maximalSum_nonneg _ _)
      rw [hz]
      exact sub_nonpos.mpr (maximalSum_nonneg _ _)
  have hc : ∫ q, maximalSum T f n (T q) ∂μ = ∫ q, maximalSum T f n q ∂μ := by
    rw [← integral_map hT.measurable.aemeasurable
      (hM.aestronglyMeasurable.mono_ac (by rw [hT.map_eq]))]
    rw [hT.map_eq]
  have hi := integral_mono (hM.sub hMT) (hf.indicator hE) hp
  change (∫ q, maximalSum T f n q - maximalSum T f n (T q) ∂μ) ≤ _ at hi
  change Integrable (fun q => maximalSum T f n (T q)) μ at hMT
  rw [integral_sub hM hMT, hc, sub_self, integral_indicator hE] at hi
  exact hi





/-- Number of visits to `B` among times `0,...,n-1`. -/
def badVisits (T : X → X) (B : Set X) (n : ℕ) (q : X) : ℕ := by
  classical
  exact ((Finset.range n).filter fun k => T^[k] q ∈ B).card

omit [MeasurableSpace X] in
theorem birkhoffSum_centered_indicator (B : Set X) (ε : ℝ) (n : ℕ) (q : X) :
    birkhoffSum T (fun q => B.indicator (fun _ => (1 : ℝ)) q - ε) n q =
      (badVisits T B n q : ℝ) - ε * n := by
  classical
  simp [birkhoffSum, badVisits, Finset.sum_sub_distrib, Set.indicator_apply,
    Finset.sum_boole, mul_comm]

/-- Finite Hopf inequality for the indicator of a measurable bad set. -/
theorem measure_finite_maximal_bad_le [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {B : Set X} (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    μ {q | 0 < maximalSum T (fun q => B.indicator (fun _ => (1 : ℝ)) q - ε) n q}
      ≤ ENNReal.ofReal (μ.real B / ε) := by
  let g : X → ℝ := fun q => B.indicator (fun _ => (1 : ℝ)) q - ε
  let E : Set X := {q | 0 < maximalSum T g n q}
  have hI : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hgm : Measurable g := (measurable_const.indicator hB).sub measurable_const
  have hi := integral_nonneg_on_maximalSum_pos hT
    (hI.sub (integrable_const ε)) hgm n
  change 0 ≤ ∫ q in E, B.indicator (fun _ => (1 : ℝ)) q - ε ∂μ at hi
  rw [integral_sub hI.integrableOn (integrable_const ε),
    setIntegral_indicator hB, setIntegral_const, setIntegral_const] at hi
  simp only [smul_eq_mul, mul_one] at hi
  have hEB : μ.real (E ∩ B) ≤ μ.real B := measureReal_mono inter_subset_right
  have hbound : μ.real E ≤ μ.real B / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ E)
    (div_nonneg (measureReal_nonneg) hε.le)).2 hbound

/-- A point has excessive bad visits if some finite time interval has bad
frequency strictly larger than `ε`. -/
def excessiveVisits (T : X → X) (B : Set X) (ε : ℝ) : Set X :=
  {q | ∃ n : ℕ, ε * n < (badVisits T B n q : ℝ)}

omit [MeasurableSpace X] in
theorem excessiveVisits_eq_iUnion (B : Set X) (ε : ℝ) :
    excessiveVisits T B ε = ⋃ n : ℕ,
      {q | 0 < maximalSum T (fun q => B.indicator (fun _ => (1 : ℝ)) q - ε) n q} := by
  ext q
  simp only [excessiveVisits, mem_setOf_eq, mem_iUnion, maximalSum_pos_iff,
    birkhoffSum_centered_indicator, sub_pos]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, n, le_rfl, hn⟩
  · rintro ⟨n, k, _, hk⟩
    exact ⟨k, hk⟩

theorem measurableSet_excessiveVisits (hT : Measurable T)
    {B : Set X} (hB : MeasurableSet B) (ε : ℝ) :
    MeasurableSet (excessiveVisits T B ε) := by
  rw [excessiveVisits_eq_iUnion]
  exact MeasurableSet.iUnion fun n => measurableSet_lt measurable_const
    (measurable_maximalSum hT ((measurable_const.indicator hB).sub measurable_const) n)

/-- The weak `(1,1)` maximal bound is uniform over all finite time lengths. -/
theorem measure_excessiveVisits_le [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {B : Set X} (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) :
    μ (excessiveVisits T B ε) ≤ ENNReal.ofReal (μ.real B / ε) := by
  rw [excessiveVisits_eq_iUnion]
  have hm : Monotone (fun n : ℕ =>
      {q | 0 < maximalSum T (fun q => B.indicator (fun _ => (1 : ℝ)) q - ε) n q}) := by
    intro n m hnm q hq
    exact hq.trans_le (maximalSum_mono q hnm)
  rw [hm.measure_iUnion]
  exact iSup_le (measure_finite_maximal_bad_le hT hB hε)

/-- The actual large good set used to choose paired-return times: every point
in it has the required frequency bound at every finite time length. -/
theorem exists_all_lengths_good_set [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {B : Set X} (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Set X, MeasurableSet G ∧
      1 - μ.real B / ε ≤ μ.real G ∧
      ∀ q ∈ G, ∀ n : ℕ, (badVisits T B n q : ℝ) ≤ ε * n := by
  let G := (excessiveVisits T B ε)ᶜ
  have hE := measurableSet_excessiveVisits hT.measurable hB ε
  refine ⟨G, hE.compl, ?_, ?_⟩
  · have h := (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top μ (excessiveVisits T B ε))
      (div_nonneg measureReal_nonneg hε.le)).1 (measure_excessiveVisits_le hT hB hε)
    rw [show G = (excessiveVisits T B ε)ᶜ from rfl, measureReal_compl hE]
    simp only [measureReal_univ_eq_one]
    change μ.real (excessiveVisits T B ε) ≤ μ.real B / ε at h
    linarith
  · intro q hq n
    exact le_of_not_gt (fun hn => hq ⟨n, hn⟩)




/-- The form used for `X₃` in the low-entropy proof: a bad set of mass less
than `ε²` leaves a set of mass greater than `1-ε` good at every length. -/
theorem exists_all_lengths_good_set_of_small_bad [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {B : Set X} (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) (hsmall : μ.real B < ε ^ 2) :
    ∃ G : Set X, MeasurableSet G ∧ 1 - ε < μ.real G ∧
      ∀ q ∈ G, ∀ n : ℕ, (badVisits T B n q : ℝ) ≤ ε * n := by
  obtain ⟨G, hG, hmass, hgood⟩ := exists_all_lengths_good_set hT hB hε
  refine ⟨G, hG, ?_, hgood⟩
  have hquot : μ.real B / ε < ε := (div_lt_iff₀ hε).2 (by nlinarith)
  linarith

end VV.BBEKPairedReturnMaximal
