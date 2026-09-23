import VV.Entropy.BlockEstimate
import VV.Entropy.OrbitAverage

/-! Entropy concavity for actual orbit averages and the finite-time
inequality used in the variational principle. -/

noncomputable section
open MeasureTheory Function Set
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

theorem entropy_orbitAverage_ge {T : X → X} (hT : Measurable T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X)
    (cells : I → Set X) (hmeas : ∀ i, MeasurableSet (cells i)) :
    (n : ℝ)⁻¹ * (∑ j ∈ Finset.range n,
      entropy (ν : Measure X) (fun i => (T^[j]) ⁻¹' cells i)) ≤
        entropy (orbitAverage hT n hn ν : Measure X) cells := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmass : ∀ i, ((orbitAverage hT n hn ν : Measure X) (cells i)).toReal =
      ∑ j ∈ Finset.range n, (n : ℝ)⁻¹ *
        ((ν : Measure X) ((T^[j]) ⁻¹' cells i)).toReal := by
    intro i
    rw [orbitAverage_apply hT n hn ν (hmeas i), ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun j _ => measure_ne_top _ _), Finset.mul_sum]
  have hcell : ∀ i,
      (∑ j ∈ Finset.range n, (n : ℝ)⁻¹ *
        Real.negMulLog ((ν : Measure X) ((T^[j]) ⁻¹' cells i)).toReal) ≤
      Real.negMulLog ((orbitAverage hT n hn ν : Measure X) (cells i)).toReal := by
    intro i
    rw [hmass]
    simpa only [smul_eq_mul] using
      Real.concaveOn_negMulLog.le_map_sum (t := Finset.range n)
        (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg n))
        (by simp [hnR])
        (fun j _ => Set.mem_Ici.mpr (ENNReal.toReal_nonneg :
          0 ≤ ((ν : Measure X) ((T^[j]) ⁻¹' cells i)).toReal))
  simp only [entropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun i _ => hcell i

theorem sum_intervalEntropy_le_average {T : X → X} (hT : Measurable T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X)
    (P : FixedPartition X I) (q : ℕ) :
    (∑ i ∈ Finset.range n, intervalEntropy (ν : Measure X) P T i q) ≤
      (n : ℝ) * blockEntropy (orbitAverage hT n hn ν : Measure X) P T q := by
  have h := entropy_orbitAverage_ge hT n hn ν (ksJoinCells P.cells T q)
    (P.dynJoin hT q).measurable
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left h hnR.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul] using hm

/-- Long-block entropy of the seed is controlled by any fixed block of its
actual Cesàro orbit average, up to an explicit vanishing boundary error. -/
theorem blockEntropy_le_average [Nonempty I] {T : X → X} (hT : Measurable T)
    (n : ℕ) (hn : 0 < n) (ν : ProbabilityMeasure X) (P : FixedPartition X I)
    {q : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    (q : ℝ) * blockEntropy (ν : Measure X) P T n ≤
      (n : ℝ) * blockEntropy (orbitAverage hT n hn ν : Measure X) P T q +
        3 * (q : ℝ)^2 * Real.log (Fintype.card I) := by
  exact (blockEntropy_mul_le_sum (ν : Measure X) P hT hq hqn).trans
    (add_le_add_right (sum_intervalEntropy_le_average hT n hn ν P q) _)

end ErgodicTheory.Entropy
