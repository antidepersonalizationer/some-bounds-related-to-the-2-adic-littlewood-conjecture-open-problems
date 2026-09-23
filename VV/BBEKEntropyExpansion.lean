import VV.BBEKEntropyGeometry

/-! Quantitative unstable expansion and a first-exit argument. -/

noncomputable section
open Set Metric Topology
open scoped Topology

namespace VV.BBEKEntropyExpansion
open BBEKDynamics BBEKQuotient BBEKEntropyGeometry

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def expand (t : ℝ) (z : ℝ × Q2) : ℝ × Q2 :=
  (Real.exp (2*t) * z.1, (2 : Q2) ^ (-2 : ℤ) * z.2)

theorem expand_conjugate (t : ℝ) (z : ℝ × Q2) :
    psi t 1 * x z.1 z.2 * (psi t 1)⁻¹ = x (expand t z).1 (expand t z).2 := by
  simpa only [expand,mul_one] using psi_conjugate t 1 z.1 z.2

theorem expand_sub (t : ℝ) (z w : ℝ × Q2) :
    expand t (z-w) = expand t z - expand t w := by
  apply Prod.ext <;> simp [expand,mul_sub]

theorem expand_norm (t : ℝ) (z : ℝ × Q2) :
    ‖expand t z‖ = max (Real.exp (2*t) * ‖z.1‖) (4 * ‖z.2‖) := by
  have h2 : ‖(2 : Q2) ^ (-2 : ℤ)‖ = (4 : ℝ) := by
    convert padicNormE.norm_p_zpow (p := 2) (-2) using 1 <;> norm_num
  simp only [expand,Prod.norm_mk,norm_mul,h2,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem four_le_exp_twice {t : ℝ} (ht : Real.log 2 ≤ t) : 4 ≤ Real.exp (2*t) := by
  have hh : 2 ≤ Real.exp t := by
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr ht
  have he : Real.exp (2*t) = (Real.exp t)^2 := by
    rw [show 2*t=t+t by ring,Real.exp_add,pow_two]
  rw [he]
  nlinarith

theorem expand_norm_lower {t : ℝ} (ht : Real.log 2 ≤ t) (z : ℝ × Q2) :
    4 * ‖z‖ ≤ ‖expand t z‖ := by
  rw [expand_norm,Prod.norm_def,mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
  exact max_le_max (mul_le_mul_of_nonneg_right (four_le_exp_twice ht) (norm_nonneg _)) le_rfl

theorem expand_norm_upper {t : ℝ} (ht : Real.log 2 ≤ t) (z : ℝ × Q2) :
    ‖expand t z‖ ≤ Real.exp (2*t) * ‖z‖ := by
  rw [expand_norm,Prod.norm_def,mul_max_of_nonneg _ _ (Real.exp_pos _).le]
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (four_le_exp_twice ht) (norm_nonneg _))

theorem expand_iterate_norm_lower {t : ℝ} (ht : Real.log 2 ≤ t) (z : ℝ × Q2) (n : ℕ) :
    (4 : ℝ)^n * ‖z‖ ≤ ‖(expand t)^[n] z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply',pow_succ']
      calc
        4 * 4^n * ‖z‖ = 4 * (4^n * ‖z‖) := by ring
        _ ≤ 4 * ‖(expand t)^[n] z‖ := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ _ := expand_norm_lower ht _

theorem expand_iterate_norm_upper {t : ℝ} (ht : Real.log 2 ≤ t) (z : ℝ × Q2) (n : ℕ) :
    ‖(expand t)^[n] z‖ ≤ (Real.exp (2*t))^n * ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply',pow_succ']
      calc
        _ ≤ Real.exp (2*t) * ‖(expand t)^[n] z‖ := expand_norm_upper ht _
        _ ≤ Real.exp (2*t) * ((Real.exp (2*t))^n * ‖z‖) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = _ := by ring

/-- The first iterate reaching the inner radius stays below the outer
radius. The upper expansion bound, rather than an arbitrary late iterate,
is what prevents wrapping around the quotient from spoiling separation. -/
theorem first_exit {t : ℝ} (ht : Real.log 2 ≤ t) {ε R : ℝ}
    (hεR : Real.exp (2*t) * ε ≤ R) (z : ℝ × Q2) (hzR : ‖z‖ ≤ R)
    (n : ℕ) (hreach : ε ≤ (4 : ℝ)^n * ‖z‖) :
    ∃ j ≤ n, ε ≤ ‖(expand t)^[j] z‖ ∧ ‖(expand t)^[j] z‖ ≤ R := by
  have hn : ε ≤ ‖(expand t)^[n] z‖ := hreach.trans (expand_iterate_norm_lower ht z n)
  have hex : ∃ j : ℕ, ε ≤ ‖(expand t)^[j] z‖ := ⟨n,hn⟩
  let j := Nat.find hex
  have hj : ε ≤ ‖(expand t)^[j] z‖ := Nat.find_spec hex
  have hjn : j ≤ n := Nat.find_min' hex hn
  refine ⟨j,hjn,hj,?_⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · simpa [hj0] using hzR
  · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj0)
    have hklt : k < j := by omega
    have hkε : ‖(expand t)^[k] z‖ < ε := lt_of_not_ge (Nat.find_min hex hklt)
    rw [hk,Function.iterate_succ_apply']
    exact (expand_norm_upper ht _).trans
      ((mul_le_mul_of_nonneg_left hkε.le (Real.exp_pos _).le).trans hεR)

def timeMap (t : ℝ) (q : X) : X := psi t 1 • q

theorem timeMap_continuous (t : ℝ) : Continuous (timeMap t) :=
  continuous_const.smul continuous_id

theorem timeMap_parameter (t : ℝ) (z : ℝ × Q2) (q : X) :
    timeMap t (x z.1 z.2 • q) = x (expand t z).1 (expand t z).2 • timeMap t q := by
  have hm : psi t 1 * x z.1 z.2 = x (expand t z).1 (expand t z).2 * psi t 1 := by
    calc
      _ = (psi t 1 * x z.1 z.2 * (psi t 1)⁻¹) * psi t 1 := by group
      _ = _ := by rw [expand_conjugate]
  simp only [timeMap,← mul_smul,hm]

theorem timeMap_iterate_parameter (t : ℝ) (z : ℝ × Q2) (q : X) (n : ℕ) :
    (timeMap t)^[n] (x z.1 z.2 • q) =
      x ((expand t)^[n] z).1 ((expand t)^[n] z).2 • (timeMap t)^[n] q := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply',ih,timeMap_parameter,
        Function.iterate_succ_apply',Function.iterate_succ_apply']

theorem parameter_difference (z w : ℝ × Q2) (q : X) :
    x z.1 z.2 • q = x (z-w).1 (z-w).2 • (x w.1 w.2 • q) := by
  rw [← mul_smul,← x_add]
  simp

theorem timeMap_iterate_difference (t : ℝ) (z w : ℝ × Q2) (q : X) (n : ℕ) :
    (timeMap t)^[n] (x z.1 z.2 • q) =
      x ((expand t)^[n] (z-w)).1 ((expand t)^[n] (z-w)).2 •
        (timeMap t)^[n] (x w.1 w.2 • q) := by
  rw [parameter_difference z w q,timeMap_iterate_parameter]

/-- The precise first-exit separation statement on the actual quotient.
Both constants and the open diagonal neighborhood are obtained from the
compact set and expansion; none are assumed as a geometric input. -/
theorem compact_first_exit_separation {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ R : ℝ, 0 < R ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ E : Set (X × X),
      IsOpen E ∧ (∀ q : X, (q,q) ∈ E) ∧
      ∀ (q : X) (z w : ℝ × Q2) (n : ℕ), dist z w ≤ R →
        (∀ k ≤ n, (timeMap t)^[k] (x w.1 w.2 • q) ∈ Y) →
        ε ≤ (4 : ℝ)^n * dist z w →
        ∃ j ≤ n, ((timeMap t)^[j] (x w.1 w.2 • q),
          (timeMap t)^[j] (x z.1 z.2 • q)) ∉ E := by
  obtain ⟨R,hR,hsep⟩ := compact_parameter_annulus_separation hY
  let ε : ℝ := R / Real.exp (2*t)
  have hε : 0 < ε := div_pos hR (Real.exp_pos _)
  have hεR : Real.exp (2*t) * ε ≤ R := by
    dsimp [ε]
    rw [mul_div_cancel₀ _ (Real.exp_ne_zero _)]
  obtain ⟨E,hE,hdiag,hann⟩ := hsep ε hε
  refine ⟨R,hR,ε,hε,E,hE,hdiag,?_⟩
  intro q z w n hzw htrapped hreach
  rw [dist_eq_norm] at hzw hreach
  obtain ⟨j,hjn,hlo,hhi⟩ := first_exit ht hεR (z-w) hzw n hreach
  refine ⟨j,hjn,?_⟩
  rw [timeMap_iterate_difference t z w q j]
  exact hann _ (htrapped j hjn) _ hlo hhi

end VV.BBEKEntropyExpansion
