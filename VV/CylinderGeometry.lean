import VV.Semantics
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Concrete continued-fraction cylinder geometry

Two inverse branches contract by at least a factor of four.  The following
proof works directly with the complete-quotient recursion and does not need
an unformalized continued-fraction cylinder theorem.
-/

namespace VV.CylinderGeometry

noncomputable def branch (a t : ℝ) : ℝ := (a + t)⁻¹

theorem branch_pair (a b t : ℝ) (hb : 0 < b + t) :
    branch a (branch b t) = (b + t) / (a * (b + t) + 1) := by
  simp only [branch]
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp

theorem pair_difference (a b u v : ℝ)
    (hu : a * (b + u) + 1 ≠ 0) (hv : a * (b + v) + 1 ≠ 0) :
    (b + u) / (a * (b + u) + 1) - (b + v) / (a * (b + v) + 1) =
      (u - v) / ((a * (b + u) + 1) * (a * (b + v) + 1)) := by
  field_simp
  ring

theorem branch_pair_contract (a b u v : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |branch a (branch b u) - branch a (branch b v)| ≤ |u - v| / 4 := by
  have hbu : 0 < b + u := by linarith
  have hbv : 0 < b + v := by linarith
  have hdu : 2 ≤ a * (b + u) + 1 := by nlinarith
  have hdv : 2 ≤ a * (b + v) + 1 := by nlinarith
  have hdu0 : 0 < a * (b + u) + 1 := by linarith
  have hdv0 : 0 < a * (b + v) + 1 := by linarith
  have hprod : 4 ≤ (a * (b + u) + 1) * (a * (b + v) + 1) := by nlinarith
  rw [branch_pair a b u hbu, branch_pair a b v hbv,
    pair_difference a b u v hdu0.ne' hdv0.ne', abs_div,
    abs_of_pos (mul_pos hdu0 hdv0)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hprod

noncomputable def tail (x : ℝ) (n : ℕ) : ℝ := Int.fract (VV.completeQuotient x n)

theorem tail_nonneg (x : ℝ) (n : ℕ) : 0 ≤ tail x n := Int.fract_nonneg _

theorem tail_lt_one (x : ℝ) (n : ℕ) : tail x n < 1 := Int.fract_lt_one _

theorem tail_rec (x : ℝ) (n : ℕ) :
    tail x n = branch (VV.partialQuotient x (n + 1)) (tail x (n + 1)) := by
  simp only [branch, VV.partialQuotient, tail]
  rw [Int.floor_add_fract]
  simp only [VV.completeQuotient, inv_inv]

theorem tail_pair (x : ℝ) (n : ℕ) :
    tail x n = branch (VV.partialQuotient x (n + 1))
      (branch (VV.partialQuotient x (n + 2)) (tail x (n + 2))) := by
  rw [tail_rec x n, tail_rec x (n + 1)]

/-- The two tails use the same next `2*m` digits. -/
theorem tail_distance_le (x y : ℝ) (hx : Irrational x) (_hy : Irrational y)
    (n m : ℕ)
    (hdigits : ∀ k : ℕ, k < 2 * m →
      VV.partialQuotient x (n + k + 1) = VV.partialQuotient y (n + k + 1)) :
    |tail x n - tail y n| ≤ (1 / 4 : ℝ) ^ m := by
  induction m generalizing n with
  | zero =>
    have hx0 := tail_nonneg x n
    have hy0 := tail_nonneg y n
    have hx1 := tail_lt_one x n
    have hy1 := tail_lt_one y n
    rw [pow_zero, abs_le]
    constructor <;> linarith
  | succ m ih =>
    have hfirst := hdigits 0 (by omega)
    have hsecond := hdigits 1 (by omega)
    simp only [Nat.add_zero] at hfirst
    have hrest : ∀ k : ℕ, k < 2 * m →
        VV.partialQuotient x (n + 2 + k + 1) =
          VV.partialQuotient y (n + 2 + k + 1) := by
      intro k hk
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hdigits (k + 2) (by omega)
    have hdist := ih (n + 2) hrest
    have hstep := branch_pair_contract
      (VV.partialQuotient x (n + 1)) (VV.partialQuotient x (n + 2))
      (tail x (n + 2)) (tail y (n + 2))
      (by exact_mod_cast VV.one_le_partialQuotient_succ hx n)
      (by exact_mod_cast VV.one_le_partialQuotient_succ hx (n + 1))
      (tail_nonneg x _) (tail_nonneg y _)
    rw [tail_pair x n, tail_pair y n, ← hfirst]
    have hsecond' : VV.partialQuotient x (n + 2) = VV.partialQuotient y (n + 2) := by
      simpa only [Nat.add_assoc] using hsecond
    rw [← hsecond']
    calc
      _ ≤ |tail x (n + 2) - tail y (n + 2)| / 4 := hstep
      _ ≤ (1 / 4 : ℝ) ^ m / 4 := div_le_div_of_nonneg_right hdist (by norm_num)
      _ = (1 / 4 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring

/-- Equality of the integer part and first `2*m` partial quotients gives an
explicit exponentially small bound on the distance between the real numbers. -/
theorem same_prefix_distance (x y : ℝ) (hx : Irrational x) (hy : Irrational y)
    (m : ℕ) (hzero : VV.partialQuotient x 0 = VV.partialQuotient y 0)
    (hdigits : ∀ k : ℕ, k < 2 * m →
      VV.partialQuotient x (k + 1) = VV.partialQuotient y (k + 1)) :
    dist x y ≤ (1 / 4 : ℝ) ^ m := by
  have ht := tail_distance_le x y hx hy 0 m (by simpa using hdigits)
  have hfloor : ⌊x⌋ = ⌊y⌋ := hzero
  have heq : x - y = tail x 0 - tail y 0 := by
    simp only [tail, VV.completeQuotient, Int.fract]
    rw [hfloor]
    ring
  simpa only [Real.dist_eq, heq] using ht

/-- Uniqueness of a real irrational number from its entire simple continued
fraction, including the integer part. -/
theorem eq_of_all_partialQuotients_eq {x y : ℝ}
    (hx : Irrational x) (hy : Irrational y)
    (h : ∀ n : ℕ, VV.partialQuotient x n = VV.partialQuotient y n) : x = y := by
  have hdist : ∀ m : ℕ, dist x y ≤ (1 / 4 : ℝ) ^ m :=
    fun m => same_prefix_distance x y hx hy m (h 0) (fun k _ => h (k + 1))
  have hzero : dist x y ≤ 0 := ge_of_tendsto'
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
      (by norm_num : (1 / 4 : ℝ) < 1)) hdist
  exact dist_eq_zero.mp (le_antisymm hzero dist_nonneg)

end VV.CylinderGeometry
