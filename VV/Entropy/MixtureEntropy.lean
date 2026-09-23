import VV.Entropy.FixedRefinement
import VV.Entropy.FiniteEntropy

/-! Finite invariant probability mixtures preserve KS entropy lower bounds. -/
noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology ENNReal NNReal
namespace ErgodicTheory.Entropy
variable {X I J : Type*} [MeasurableSpace X]

/-- The actual finite convex combination measure. -/
def mixtureMeasure [Fintype J] (w : J → ℝ≥0) (ν : J → ProbabilityMeasure X) : Measure X :=
  ∑ j, (w j : ℝ≥0∞) • (ν j : Measure X)

theorem mixtureMeasure_apply [Fintype J] (w : J → ℝ≥0) (ν : J → ProbabilityMeasure X)
    (s : Set X) : mixtureMeasure w ν s = ∑ j, (w j : ℝ≥0∞) * (ν j : Measure X) s := by
  simp [mixtureMeasure, Measure.finset_sum_apply, Measure.smul_apply]

def probabilityMixture [Fintype J] (w : J → ℝ≥0) (hw : ∑ j, w j = 1)
    (ν : J → ProbabilityMeasure X) : ProbabilityMeasure X :=
  ⟨mixtureMeasure w ν, ⟨by
    rw [mixtureMeasure_apply]
    simpa only [measure_univ, mul_one, ← ENNReal.coe_finset_sum, hw, ENNReal.coe_one]⟩⟩

@[simp] theorem probabilityMixture_coe [Fintype J] (w : J → ℝ≥0) (hw : ∑ j, w j = 1)
    (ν : J → ProbabilityMeasure X) : (probabilityMixture w hw ν : Measure X) = mixtureMeasure w ν := rfl

theorem probabilityMixture_apply_toReal [Fintype J] (w : J → ℝ≥0) (hw : ∑ j, w j = 1)
    (ν : J → ProbabilityMeasure X) (s : Set X) :
    ((probabilityMixture w hw ν : Measure X) s).toReal =
      ∑ j, (w j : ℝ) * ((ν j : Measure X) s).toReal := by
  rw [probabilityMixture_coe, mixtureMeasure_apply, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
  · intro j hj
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)

theorem probabilityMixture_measurePreserving [Fintype J]
    (w : J → ℝ≥0) (hw : ∑ j, w j = 1) (ν : J → ProbabilityMeasure X)
    {T : X → X} (hT : Measurable T)
    (hν : ∀ j, MeasurePreserving T (ν j : Measure X) (ν j : Measure X)) :
    MeasurePreserving T (probabilityMixture w hw ν : Measure X)
      (probabilityMixture w hw ν : Measure X) := by
  refine ⟨hT, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hT hs]
  simp only [probabilityMixture_coe, mixtureMeasure_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(hν j).measure_preimage hs.nullMeasurableSet]

/-- Concavity survives the Fekete limit for a genuinely common fixed partition. -/
theorem ksEntropyPartition_mixture_ge [Fintype I] [Fintype J]
    (w : J → ℝ≥0) (hw : ∑ j, w j = 1) (ν : J → ProbabilityMeasure X)
    {T : X → X} (hT : Measurable T)
    (hν : ∀ j, MeasurePreserving T (ν j : Measure X) (ν j : Measure X))
    (P : FixedPartition X I) :
    (∑ j, (w j : ℝ) * ksEntropyPartition (hν j) (P.toMeasurePartition (ν j : Measure X))) ≤
      ksEntropyPartition (probabilityMixture_measurePreserving w hw ν hT hν)
        (P.toMeasurePartition (probabilityMixture w hw ν : Measure X)) := by
  let hmix := probabilityMixture_measurePreserving w hw ν hT hν
  have hseq (n : ℕ) :
      (∑ j, (w j : ℝ) * ksEntropySeq (hν j) (P.toMeasurePartition (ν j : Measure X)) n) ≤
        ksEntropySeq hmix (P.toMeasurePartition (probabilityMixture w hw ν : Measure X)) n := by
    exact entropy_concave_of_apply (probabilityMixture w hw ν : Measure X)
      (fun j => (ν j : Measure X)) (ksJoinCells P.cells T n) (fun j => (w j : ℝ))
      (fun j => (w j).coe_nonneg) (by simpa only [← NNReal.coe_sum, hw, NNReal.coe_one])
      (fun i => probabilityMixture_apply_toReal w hw ν (ksJoinCells P.cells T n i))
  have hleft := tendsto_finset_sum Finset.univ (fun j hj =>
    (tendsto_ksEntropySeq (hν j) (P.toMeasurePartition (ν j : Measure X))).const_mul (w j : ℝ))
  apply le_of_tendsto_of_tendsto' hleft
    (tendsto_ksEntropySeq hmix (P.toMeasurePartition (probabilityMixture w hw ν : Measure X)))
  intro n
  have h := div_le_div_of_nonneg_right (hseq n) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [Finset.sum_div, mul_div_assoc] using h

/-- A strict real bound below system entropy is attained by a finite exact partition. -/
theorem exists_fixedPartition_entropy_gt {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) {b : ℝ}
    (hb : (b : EReal) < ksEntropy hT) :
    ∃ n : ℕ, ∃ P : FixedPartition X (Fin n), b < ksEntropyPartition hT (P.toMeasurePartition μ) := by
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hb
  obtain ⟨P, hP⟩ := lt_iSup_iff.mp hn
  refine ⟨n, P.exactify, ?_⟩
  rw [P.ksEntropy_exactify hT]
  exact EReal.coe_lt_coe_iff.mp hP

/-- Finite invariant convex combinations retain any common real KS entropy lower bound.
The simultaneous approximating partition is constructed by exactification and common refinement. -/
theorem ksEntropy_mixture_ge [Fintype J]
    (w : J → ℝ≥0) (hw : ∑ j, w j = 1) (ν : J → ProbabilityMeasure X)
    {T : X → X} (hT : Measurable T)
    (hν : ∀ j, MeasurePreserving T (ν j : Measure X) (ν j : Measure X))
    {c : ℝ} (hc : ∀ j, (c : EReal) ≤ ksEntropy (hν j)) :
    (c : EReal) ≤ ksEntropy (probabilityMixture_measurePreserving w hw ν hT hν) := by
  classical
  by_contra hnot
  obtain ⟨b, hb, hbc⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
  have he (j : J) : ∃ n : ℕ, ∃ P : FixedPartition X (Fin n),
      b < ksEntropyPartition (hν j) (P.toMeasurePartition (ν j : Measure X)) :=
    exists_fixedPartition_entropy_gt (hν j) (hbc.trans_le (hc j))
  choose n P hP using he
  let R := FixedPartition.iJoin P
  have hR (j : J) : b ≤ ksEntropyPartition (hν j) (R.toMeasurePartition (ν j : Measure X)) :=
    (hP j).le.trans (ksEntropyPartition_le_iJoin (hν j) P j)
  have hweight : ∑ j, (w j : ℝ) = 1 := by
    simpa only [← NNReal.coe_sum, hw, NNReal.coe_one]
  have havg : b ≤ ksEntropyPartition (probabilityMixture_measurePreserving w hw ν hT hν)
      (R.toMeasurePartition (probabilityMixture w hw ν : Measure X)) := by
    calc
      b = ∑ j, (w j : ℝ) * b := by rw [← Finset.sum_mul, hweight, one_mul]
      _ ≤ ∑ j, (w j : ℝ) * ksEntropyPartition (hν j)
          (R.toMeasurePartition (ν j : Measure X)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hR j) (w j).coe_nonneg)
      _ ≤ _ := ksEntropyPartition_mixture_ge w hw ν hT hν R
  exact (not_le_of_gt hb) ((EReal.coe_le_coe_iff.mpr havg).trans
    (ksEntropyPartition_le_ksEntropy _ _))

/-- The entropy excess of a finite mixture is bounded by the entropy of its weights. -/
theorem entropy_mixture_le [Fintype I] [Fintype J]
    (w : J → ℝ≥0) (hw : ∑ j, w j = 1) (ν : J → ProbabilityMeasure X)
    (P : FixedPartition X I) :
    entropy (probabilityMixture w hw ν : Measure X) P.cells ≤
      (∑ j, (w j : ℝ) * entropy (ν j : Measure X) P.cells) +
        ∑ j, Real.negMulLog (w j : ℝ) := by
  classical
  have hsum (j : J) : ∑ i, ((ν j : Measure X) (P.cells i)).toReal = 1 :=
    (P.toMeasurePartition (ν j : Measure X)).sum_toReal_measure_eq_one
  calc
    entropy (probabilityMixture w hw ν : Measure X) P.cells
      = ∑ i, Real.negMulLog (∑ j, (w j : ℝ) * ((ν j : Measure X) (P.cells i)).toReal) := by
        simp only [entropy, probabilityMixture_apply_toReal]
    _ ≤ ∑ i, ∑ j, Real.negMulLog ((w j : ℝ) * ((ν j : Measure X) (P.cells i)).toReal) :=
      Finset.sum_le_sum fun i _ => negMulLog_sum_le_sum_negMulLog _
        (fun j => mul_nonneg (w j).coe_nonneg ENNReal.toReal_nonneg)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, hsum,
        one_mul, entropy]
      ring

/-- Fixed-partition KS entropy is affine on finite invariant probability mixtures. -/
theorem ksEntropyPartition_mixture_eq [Fintype I] [Fintype J]
    (w : J → ℝ≥0) (hw : ∑ j, w j = 1) (ν : J → ProbabilityMeasure X)
    {T : X → X} (hT : Measurable T)
    (hν : ∀ j, MeasurePreserving T (ν j : Measure X) (ν j : Measure X))
    (P : FixedPartition X I) :
    ksEntropyPartition (probabilityMixture_measurePreserving w hw ν hT hν)
        (P.toMeasurePartition (probabilityMixture w hw ν : Measure X)) =
      ∑ j, (w j : ℝ) * ksEntropyPartition (hν j) (P.toMeasurePartition (ν j : Measure X)) := by
  apply le_antisymm _ (ksEntropyPartition_mixture_ge w hw ν hT hν P)
  let hmix := probabilityMixture_measurePreserving w hw ν hT hν
  have hright := tendsto_finset_sum Finset.univ (fun j hj =>
    (tendsto_ksEntropySeq (hν j) (P.toMeasurePartition (ν j : Measure X))).const_mul (w j : ℝ))
  have herr := (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop
    (∑ j, Real.negMulLog (w j : ℝ))
  have hlim := hright.add herr
  rw [add_zero] at hlim
  apply le_of_tendsto_of_tendsto'
    (tendsto_ksEntropySeq hmix (P.toMeasurePartition (probabilityMixture w hw ν : Measure X))) hlim
  intro n
  have hh := div_le_div_of_nonneg_right (entropy_mixture_le w hw ν (P.dynJoin hT n))
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [add_div, Finset.sum_div, mul_div_assoc] using hh

/-- Arbitrary real lower bounds may be approximated simultaneously by one finite partition. -/
theorem ksEntropy_mixture_ge_weighted [Fintype J]
    (w : J → ℝ≥0) (hw : ∑ j, w j = 1) (ν : J → ProbabilityMeasure X)
    {T : X → X} (hT : Measurable T)
    (hν : ∀ j, MeasurePreserving T (ν j : Measure X) (ν j : Measure X))
    (a : J → ℝ) (ha : ∀ j, (a j : EReal) ≤ ksEntropy (hν j)) :
    ((∑ j, (w j : ℝ) * a j : ℝ) : EReal) ≤
      ksEntropy (probabilityMixture_measurePreserving w hw ν hT hν) := by
  classical
  by_contra hnot
  obtain ⟨b, hb, hba⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
  let ε : ℝ := (∑ j, (w j : ℝ) * a j) - b
  have hε : 0 < ε := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hba)
  have he (j : J) : ∃ n : ℕ, ∃ P : FixedPartition X (Fin n),
      a j - ε < ksEntropyPartition (hν j) (P.toMeasurePartition (ν j : Measure X)) :=
    exists_fixedPartition_entropy_gt (hν j)
      ((EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hε)).trans_le (ha j))
  choose n P hP using he
  let R := FixedPartition.iJoin P
  have hR (j : J) : a j - ε ≤ ksEntropyPartition (hν j)
      (R.toMeasurePartition (ν j : Measure X)) :=
    (hP j).le.trans (ksEntropyPartition_le_iJoin (hν j) P j)
  have hweight : ∑ j, (w j : ℝ) = 1 := by
    simp only [← NNReal.coe_sum, hw, NNReal.coe_one]
  have havg : b ≤ ksEntropyPartition (probabilityMixture_measurePreserving w hw ν hT hν)
      (R.toMeasurePartition (probabilityMixture w hw ν : Measure X)) := by
    calc
      b = ∑ j, (w j : ℝ) * (a j - ε) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hweight, one_mul, ε]
        ring
      _ ≤ ∑ j, (w j : ℝ) * ksEntropyPartition (hν j)
          (R.toMeasurePartition (ν j : Measure X)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hR j) (w j).coe_nonneg)
      _ ≤ _ := ksEntropyPartition_mixture_ge w hw ν hT hν R
  exact (not_le_of_gt hb) ((EReal.coe_le_coe_iff.mpr havg).trans
    (ksEntropyPartition_le_ksEntropy _ _))

/-- Finite real upper bounds on the component system entropies bound the mixture. -/
theorem ksEntropy_mixture_le_weighted [Fintype J]
    (w : J → ℝ≥0) (hw : ∑ j, w j = 1) (ν : J → ProbabilityMeasure X)
    {T : X → X} (hT : Measurable T)
    (hν : ∀ j, MeasurePreserving T (ν j : Measure X) (ν j : Measure X))
    (a : J → ℝ) (ha : ∀ j, ksEntropy (hν j) ≤ (a j : EReal)) :
    ksEntropy (probabilityMixture_measurePreserving w hw ν hT hν) ≤
      ((∑ j, (w j : ℝ) * a j : ℝ) : EReal) := by
  classical
  apply iSup_le
  intro n
  apply iSup_le
  intro P
  rw [← P.ksEntropy_exactify (probabilityMixture_measurePreserving w hw ν hT hν),
    ksEntropyPartition_mixture_eq w hw ν hT hν P.exactify]
  apply EReal.coe_le_coe_iff.mpr
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (w j).coe_nonneg
  exact EReal.coe_le_coe_iff.mp ((ksEntropyPartition_le_ksEntropy (hν j)
    (P.exactify.toMeasurePartition (ν j : Measure X))).trans (ha j))

/-- Full affinity whenever the component entropies are finite real numbers.
This includes the compact maximal-entropy face used in the BBEK argument. -/
theorem ksEntropy_mixture_eq_weighted [Fintype J]
    (w : J → ℝ≥0) (hw : ∑ j, w j = 1) (ν : J → ProbabilityMeasure X)
    {T : X → X} (hT : Measurable T)
    (hν : ∀ j, MeasurePreserving T (ν j : Measure X) (ν j : Measure X))
    (a : J → ℝ) (ha : ∀ j, ksEntropy (hν j) = (a j : EReal)) :
    ksEntropy (probabilityMixture_measurePreserving w hw ν hT hν) =
      ((∑ j, (w j : ℝ) * a j : ℝ) : EReal) :=
  le_antisymm (ksEntropy_mixture_le_weighted w hw ν hT hν a (fun j => (ha j).le))
    (ksEntropy_mixture_ge_weighted w hw ν hT hν a (fun j => (ha j).ge))

end ErgodicTheory.Entropy
