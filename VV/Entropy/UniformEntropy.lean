import VV.Entropy.FiniteEntropy
import Mathlib.Probability.Distributions.Uniform

/-! Entropy of uniform probabilities on finite separated sets. -/

noncomputable section
open MeasureTheory Function Set
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {X I : Type*} [MeasurableSpace X]

/-- If every partition cell contains at most one selected point, the actual
uniform probability on those points has entropy exactly log of their number. -/
theorem entropy_uniform_eq_log_card [Fintype I] (P : FixedPartition X I)
    (s : Finset X) (hs : s.Nonempty)
    (hsep : ∀ i, ∀ x ∈ s, ∀ y ∈ s, x ∈ P.cells i → y ∈ P.cells i → x = y) :
    entropy (PMF.uniformOfFinset s hs).toMeasure P.cells = Real.log s.card := by
  classical
  let μ := (PMF.uniformOfFinset s hs).toMeasure
  have hm : ∀ i, μ (P.cells i) =
      ((s.filter (fun x => x ∈ P.cells i)).card : ℝ≥0∞) / s.card := by
    intro i
    exact PMF.toMeasure_uniformOfFinset_apply hs (P.cells i) (P.measurable i)
  have hterm : ∀ i, Real.negMulLog (μ (P.cells i)).toReal =
      (μ (P.cells i)).toReal * Real.log s.card := by
    intro i
    have hc : (s.filter (fun x => x ∈ P.cells i)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      exact hsep i x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
        (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    have hc' : (s.filter (fun x => x ∈ P.cells i)).card = 0 ∨
        (s.filter (fun x => x ∈ P.cells i)).card = 1 := by omega
    rcases hc' with hc' | hc'
    · simp [hm, hc']
    · rw [hm, hc']
      simp only [Nat.cast_one, one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        Real.negMulLog, Real.log_inv]
      ring
  change entropy μ P.cells = _
  rw [entropy]
  simp_rw [hterm]
  have hsum : ∑ i, (μ (P.cells i)).toReal = 1 := (P.toMeasurePartition μ).sum_toReal_measure_eq_one
  rw [← Finset.sum_mul, hsum, one_mul]

/-- An orbit-separated set meets each sufficiently fine dynamical cell in
at most one point. -/
theorem blockEntropy_uniform_eq_log_card [PseudoMetricSpace X] [Fintype I]
    (P : FixedPartition X I) {T : X → X} (hT : Measurable T)
    (s : Finset X) (hs : s.Nonempty) (n : ℕ) {ε : ℝ}
    (hmesh : ∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < ε)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ∃ k < n, ε ≤ dist ((T^[k]) x) ((T^[k]) y)) :
    blockEntropy (PMF.uniformOfFinset s hs).toMeasure P T n = Real.log s.card := by
  apply entropy_uniform_eq_log_card (P.dynJoin hT n) s hs
  intro a x hx y hy hxa hya
  by_contra hne
  obtain ⟨k, hk, hdist⟩ := hsep x hx y hy hne
  have hxk := Set.mem_iInter.mp hxa (⟨k, hk⟩ : Fin n)
  have hyk := Set.mem_iInter.mp hya (⟨k, hk⟩ : Fin n)
  exact (not_lt_of_ge hdist) (hmesh (a ⟨k, hk⟩) _ hxk _ hyk)

end ErgodicTheory.Entropy

