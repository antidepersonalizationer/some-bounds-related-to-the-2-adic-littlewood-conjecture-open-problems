import VV.Entropy.FiniteEntropy

/-! The finite blocking estimate behind the variational principle. -/

noncomputable section
open scoped BigOperators

namespace ErgodicTheory.Entropy

/-- Subadditivity of intervals iterates over consecutive equal-size blocks. -/
theorem interval_le_blocks (H : ℕ → ℕ → ℝ)
    (hzero : ∀ s, H s 0 = 0)
    (hadd : ∀ s n m, H s (n + m) ≤ H s n + H (s + n) m)
    (s q k : ℕ) :
    H s (k * q) ≤ ∑ i ∈ Finset.range k, H (s + i * q) q := by
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_succ]
    exact (hadd s (k * q) q).trans (add_le_add_right ih _)

/-- Summing all residue classes modulo the block length counts each starting
time at most once.  This form only needs nonnegative summands. -/
theorem residue_block_sum_le (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    {q d n : ℕ} (hq : 0 < q) (hfit : d * q + q ≤ n) :
    (∑ j ∈ Finset.range q, ∑ k ∈ Finset.range d, f (j + k * q)) ≤
      ∑ i ∈ Finset.range n, f i := by
  classical
  let S := Finset.range q ×ˢ Finset.range d
  let a : ℕ × ℕ → ℕ := fun p => p.1 + p.2 * q
  have hinj : Set.InjOn a S := by
    intro p hp r hr heq
    simp only [S, Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hr
    have hfirst : p.1 = r.1 := by
      have hmod := congrArg (fun i => i % q) heq
      simpa only [a, Nat.add_mod, Nat.mul_mod_left, add_zero,
        Nat.mod_eq_of_lt hp.1, Nat.mod_eq_of_lt hr.1] using hmod
    have hsecond : p.2 = r.2 := by
      dsimp [a] at heq
      rw [hfirst] at heq
      exact Nat.eq_of_mul_eq_mul_right hq (Nat.add_left_cancel heq)
    exact Prod.ext hfirst hsecond
  have hsub : S.image a ⊆ Finset.range n := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    simp only [S, Finset.mem_product, Finset.mem_range] at hp
    apply Finset.mem_range.mpr
    dsimp [a]
    nlinarith
  calc
    _ = ∑ p ∈ S, f (a p) := by rw [Finset.sum_product]
    _ = ∑ i ∈ S.image a, f i := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf i)

/-- The elementary blocking inequality, before concavity is applied to a
Cesàro average.  The harmless boundary term is explicit. -/
theorem interval_blocking_estimate (H : ℕ → ℕ → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hzero : ∀ s, H s 0 = 0)
    (hnonneg : ∀ s n, 0 ≤ H s n)
    (hadd : ∀ s n m, H s (n + m) ≤ H s n + H (s + n) m)
    (hbound : ∀ s n, H s n ≤ n * D)
    {q d n : ℕ} (hq : 0 < q) (hfit : d * q + q ≤ n)
    (hend : n ≤ d * q + 2 * q) :
    (q : ℝ) * H 0 n ≤
      (∑ i ∈ Finset.range n, H i q) + 3 * (q : ℝ) ^ 2 * D := by
  have hone : ∀ j ∈ Finset.range q,
      H 0 n ≤ (∑ k ∈ Finset.range d, H (j + k * q) q) + 3 * q * D := by
    intro j hj
    have hjq : j < q := Finset.mem_range.mp hj
    have hstart : j + d * q ≤ n := by omega
    have htail : n - (j + d * q) ≤ 2 * q := by omega
    have hsplit : n = j + (d * q + (n - (j + d * q))) := by omega
    have h1 := hadd 0 j (d * q + (n - (j + d * q)))
    have h2 := hadd j (d * q) (n - (j + d * q))
    have h3 := interval_le_blocks H hzero hadd j q d
    have hb0 := hbound 0 j
    have hb1 := hbound (j + d * q) (n - (j + d * q))
    have hjR : (j : ℝ) ≤ q := by exact_mod_cast hjq.le
    have htR : ((n - (j + d * q) : ℕ) : ℝ) ≤ 2 * q := by exact_mod_cast htail
    rw [← hsplit, zero_add] at h1
    nlinarith [mul_le_mul_of_nonneg_right hjR hD, mul_le_mul_of_nonneg_right htR hD]
  have hsum := Finset.sum_le_sum hone
  have hres := residue_block_sum_le (fun i => H i q) (fun i => hnonneg i q) hq hfit
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_add_distrib] at hsum
  nlinarith

/-- The same estimate with its block count chosen internally by division. -/
theorem interval_blocking_estimate_of_le (H : ℕ → ℕ → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hzero : ∀ s, H s 0 = 0)
    (hnonneg : ∀ s n, 0 ≤ H s n)
    (hadd : ∀ s n m, H s (n + m) ≤ H s n + H (s + n) m)
    (hbound : ∀ s n, H s n ≤ n * D)
    {q n : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    (q : ℝ) * H 0 n ≤
      (∑ i ∈ Finset.range n, H i q) + 3 * (q : ℝ) ^ 2 * D := by
  have hk : 1 ≤ n / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa using hqn)
  have heq : (n / q - 1) * q + q = n / q * q := by
    calc
      _ = (n / q - 1 + 1) * q := by ring
      _ = _ := by rw [Nat.sub_add_cancel hk]
  apply interval_blocking_estimate H D hD hzero hnonneg hadd hbound hq
    (d := n / q - 1)
  · rw [heq]
    exact Nat.div_mul_le_self n q
  · have hm := Nat.mod_lt n hq
    have hn := Nat.mod_add_div n q
    nlinarith

open MeasureTheory in
/-- Actual orbit-partition entropy satisfies the non-invariant blocking
estimate.  Its right side will next be bounded by mixture concavity. -/
theorem blockEntropy_mul_le_sum [MeasurableSpace X] [Fintype I] [Nonempty I]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : FixedPartition X I)
    {T : X → X} (hT : Measurable T) {q n : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    (q : ℝ) * blockEntropy μ P T n ≤
      (∑ i ∈ Finset.range n, intervalEntropy μ P T i q) +
        3 * (q : ℝ) ^ 2 * Real.log (Fintype.card I) := by
  have hD : 0 ≤ Real.log (Fintype.card I) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := I))
  simpa only [intervalEntropy_start_zero] using interval_blocking_estimate_of_le
    (intervalEntropy μ P T) (Real.log (Fintype.card I)) hD
    (intervalEntropy_zero μ P T) (intervalEntropy_nonneg μ P T)
    (intervalEntropy_add_le μ P hT) (intervalEntropy_le_length_log μ P hT) hq hqn

end ErgodicTheory.Entropy

