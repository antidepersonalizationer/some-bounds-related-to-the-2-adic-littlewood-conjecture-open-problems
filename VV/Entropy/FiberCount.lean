import VV.Entropy.FiniteEntropy
import VV.Entropy.KSEntropyMono

/-! Finite conditional-support bounds, proved directly from Gibbs' inequality. -/

noncomputable section
open MeasureTheory Function
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]

/-- Cellwise conditional-support bounds give a measure-weighted logarithmic
bound on the entropy increase. -/
theorem entropy_join_le_of_fiber_counts {μ : Measure X} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ I) (Q : MeasurePartition μ J) (M : I → ℕ) (hM : ∀ i, 0 < M i)
    (hcount : ∀ i, (Finset.univ.filter
      (fun j => μ (P.cells i ∩ Q.cells j) ≠ 0)).card ≤ M i) :
    entropy μ (joinCells P.cells Q.cells) ≤ entropy μ P.cells +
      ∑ i, (μ (P.cells i)).toReal * Real.log (M i) := by
  classical
  let a : I → ℝ := fun i => (μ (P.cells i)).toReal
  let p : I × J → ℝ := fun z => (μ (P.cells z.1 ∩ Q.cells z.2)).toReal
  let b : I × J → ℝ := fun z => if p z = 0 then 0 else a z.1 / M z.1
  have hMpos : ∀ i, (0 : ℝ) < M i := fun i => by exact_mod_cast hM i
  have hrow : ∀ i, ∑ j, p (i,j) = a i := by
    intro i
    dsimp [p, a]
    rw [Q.measure_eq_sum_inter (P.measurable i),
      ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]
  have hasum : ∑ i, a i = 1 := P.sum_toReal_measure_eq_one
  have hpsum : ∑ z, p z = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hrow]
    exact hasum
  have hap : ∀ z, p z ≠ 0 → 0 < a z.1 := by
    intro z hz
    have hmeasure : 0 < μ (P.cells z.1 ∩ Q.cells z.2) :=
      pos_iff_ne_zero.mpr (ENNReal.toReal_ne_zero.mp hz).1
    exact ENNReal.toReal_pos
      (ne_of_gt (hmeasure.trans_le (measure_mono Set.inter_subset_left))) (measure_ne_top μ _)
  have hbrow : ∀ i, ∑ j, b (i,j) ≤ a i := by
    intro i
    have hsupport : (Finset.univ.filter (fun j => p (i,j) ≠ 0)).card ≤ M i := by
      convert hcount i using 1
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p,
        ENNReal.toReal_ne_zero]
      exact and_iff_left (measure_ne_top μ _)
    have heq : (∑ j, b (i,j)) =
        ((Finset.univ.filter (fun j => p (i,j) ≠ 0)).card : ℝ) * (a i / M i) := by
      have hb : ∀ j, b (i,j) = if p (i,j) ≠ 0 then a i / M i else 0 := by
        intro j
        by_cases hz : p (i,j) = 0 <;> simp [b, hz]
      simp_rw [hb]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [heq]
    calc
      _ ≤ (M i : ℝ) * (a i / M i) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hsupport) (div_nonneg ENNReal.toReal_nonneg (hMpos i).le)
      _ = a i := by field_simp [(hMpos i).ne']
  have hbsum : ∑ z, b z ≤ 1 := by
    rw [Fintype.sum_prod_type, ← hasum]
    exact Finset.sum_le_sum fun i _ => hbrow i
  have hbnonneg : ∀ z, 0 ≤ b z := by
    intro z
    dsimp [b]
    split_ifs
    · exact le_rfl
    · exact div_nonneg ENNReal.toReal_nonneg (hMpos z.1).le
  have hac : ∀ z, p z ≠ 0 → b z ≠ 0 := by
    intro z hz
    simp only [b, if_neg hz]
    exact (div_pos (hap z hz) (hMpos z.1)).ne'
  have hg := sum_negMulLog_le p b (fun _ => ENNReal.toReal_nonneg)
    hbnonneg hpsum hbsum hac
  have hterm : ∀ z, p z * Real.log (b z) =
      p z * Real.log (a z.1) - p z * Real.log (M z.1) := by
    intro z
    by_cases hz : p z = 0
    · simp [hz]
    · dsimp only [b]
      rw [if_neg hz, Real.log_div (hap z hz).ne' (hMpos z.1).ne']
      ring
  have hA : ∑ z, p z * Real.log (a z.1) = - entropy μ P.cells := by
    rw [Fintype.sum_prod_type, entropy, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    change (∑ j, p (i,j) * Real.log (a i)) = _
    rw [← Finset.sum_mul, hrow]
    dsimp [a, Real.negMulLog]
    ring
  have hB : ∑ z, p z * Real.log (M z.1) = ∑ i, a i * Real.log (M i) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    change (∑ j, p (i,j) * Real.log (M i)) = _
    rw [← Finset.sum_mul, hrow]
  have hR : -(∑ z, p z * Real.log (b z)) =
      entropy μ P.cells + ∑ i, a i * Real.log (M i) := by
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, hA, hB]
    ring
  rw [hR] at hg
  exact hg

/-- A uniform conditional-support bound is the constant special case. -/
theorem entropy_join_le_of_fiber_count {μ : Measure X} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ I) (Q : MeasurePartition μ J) (M : ℕ) (hM : 0 < M)
    (hcount : ∀ i, (Finset.univ.filter
      (fun j => μ (P.cells i ∩ Q.cells j) ≠ 0)).card ≤ M) :
    entropy μ (joinCells P.cells Q.cells) ≤ entropy μ P.cells + Real.log M := by
  have h := entropy_join_le_of_fiber_counts P Q (fun _ => M) (fun _ => hM) hcount
  simpa only [← Finset.sum_mul, P.sum_toReal_measure_eq_one, one_mul] using h

/-- A conditional support bound controls the entropy of the second partition. -/
theorem entropy_le_add_sum_log_of_fiber_counts {μ : Measure X} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ I) (Q : MeasurePartition μ J) (M : I → ℕ) (hM : ∀ i, 0 < M i)
    (hcount : ∀ i, (Finset.univ.filter
      (fun j => μ (P.cells i ∩ Q.cells j) ≠ 0)).card ≤ M i) :
    entropy μ Q.cells ≤ entropy μ P.cells +
      ∑ i, (μ (P.cells i)).toReal * Real.log (M i) := by
  have hlow := entropy_le_entropy_join Q P
  have hcomm : entropy μ (joinCells Q.cells P.cells) =
      entropy μ (joinCells P.cells Q.cells) := by
    rw [← entropy_reindex μ (Equiv.prodComm I J)]
    congr 1
    funext z
    exact Set.inter_comm _ _
  rw [hcomm] at hlow
  exact hlow.trans (entropy_join_le_of_fiber_counts P Q M hM hcount)

/-- Uniform form of the preceding comparison. -/
theorem entropy_le_add_log_of_fiber_count {μ : Measure X} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ I) (Q : MeasurePartition μ J) (M : ℕ) (hM : 0 < M)
    (hcount : ∀ i, (Finset.univ.filter
      (fun j => μ (P.cells i ∩ Q.cells j) ≠ 0)).card ≤ M) :
    entropy μ Q.cells ≤ entropy μ P.cells + Real.log M := by
  have hlow := entropy_le_entropy_join Q P
  have hcomm : entropy μ (joinCells Q.cells P.cells) =
      entropy μ (joinCells P.cells Q.cells) := by
    rw [← entropy_reindex μ (Equiv.prodComm I J)]
    congr 1
    funext z
    exact Set.inter_comm _ _
  rw [hcomm] at hlow
  exact hlow.trans (entropy_join_le_of_fiber_count P Q M hM hcount)

/-- Subexponential conditional name counts imply the desired entropy
comparison.  This is the finite combinatorial implication; geometric
estimates of those counts are a separate theorem. -/
theorem ksEntropyPartition_le_of_subexponential_fibers
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) (Q : MeasurePartition μ J)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n)
    (hcount : ∀ n a, (Finset.univ.filter (fun b =>
      μ ((ksJoin hT P n).cells a ∩ (ksJoin hT Q n).cells b) ≠ 0)).card ≤ M n)
    (hrate : Filter.Tendsto (fun n => Real.log (M n) / n) Filter.atTop (nhds 0)) :
    ksEntropyPartition hT Q ≤ ksEntropyPartition hT P := by
  have hh : ∀ n : ℕ, ksEntropySeq hT Q n / n ≤
      ksEntropySeq hT P n / n + Real.log (M n) / n := by
    intro n
    rw [← add_div]
    exact div_le_div_of_nonneg_right
      (entropy_le_add_log_of_fiber_count (ksJoin hT P n) (ksJoin hT Q n)
        (M n) (hM n) (hcount n)) (Nat.cast_nonneg n)
  have hlim := le_of_tendsto_of_tendsto' (tendsto_ksEntropySeq hT Q)
    ((tendsto_ksEntropySeq hT P).add hrate) hh
  simpa only [add_zero] using hlim

end ErgodicTheory.Entropy

