import VV.BBEKGaussChart
import VV.BBEKBowenLift

/-! The concrete expanding and contracting matrix directions of forward
Bowen displacements. No entropy-expansiveness assertion is assumed. -/

noncomputable section
open Matrix Filter Metric
open scoped MatrixGroups Topology

namespace VV.BBEKEntropyExpansive
open BBEKDynamics BBEKGaussChart BBEKBowenLift
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def diagConjugate {F : Type*} [Field F] (b : F) (hb : b ≠ 0) (M : SL(2,F)) : SL(2,F) :=
  BBEKDynamics.diagonal b hb * M * (BBEKDynamics.diagonal b hb)⁻¹

theorem diagConjugate_entries {F : Type*} [Field F] (b : F) (hb : b ≠ 0) (M : SL(2,F)) :
    diagConjugate b hb M 0 0 = M 0 0 ∧
    diagConjugate b hb M 0 1 = b^2*M 0 1 ∧
    diagConjugate b hb M 1 0 = b⁻¹^2*M 1 0 ∧
    diagConjugate b hb M 1 1 = M 1 1 := by
  unfold diagConjugate
  rw [diagonal_inv]
  simp [BBEKDynamics.diagonal,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hb]
  constructor
  · field_simp
  · constructor
    · ring
    · constructor
      · ring
      · field_simp

theorem diagonal_pow {F : Type*} [Field F] (b : F) (hb : b ≠ 0) (n : ℕ) :
    (BBEKDynamics.diagonal b hb)^n = BBEKDynamics.diagonal (b^n) (pow_ne_zero n hb) := by
  induction n with
  | zero => simp [BBEKDynamics.diagonal_one]
  | succ n ih =>
    rw [pow_succ,ih]
    simpa only [pow_succ] using (diagonal_mul (b^n) b (pow_ne_zero n hb) hb).symm

theorem power_diagConjugate {F : Type*} [Field F] (b : F) (hb : b ≠ 0)
    (M : SL(2,F)) (n : ℕ) :
    (BBEKDynamics.diagonal b hb)^n * M * ((BBEKDynamics.diagonal b hb)⁻¹)^n =
      diagConjugate (b^n) (pow_ne_zero n hb) M := by
  rw [inv_pow,diagonal_pow]
  rfl

/-- A bounded forward conjugacy orbit has zero expanding entry.
This single normed-field argument applies to both R and Q₂. -/
theorem lower_zero_of_bounded_conjugates {F : Type*} [NormedField F]
    (b : F) (hb : b ≠ 0) (hbn : ‖b‖ < 1) (M : SL(2,F)) (R : ℝ)
    (hbound : ∀ n : ℕ, ‖diagConjugate (b^n) (pow_ne_zero n hb) M 1 0‖ ≤ R) :
    M 1 0 = 0 := by
  have hle (n : ℕ) : ‖M 1 0‖ ≤ (‖b‖^2)^n * R := by
    have he : (b^n)^2 * diagConjugate (b^n) (pow_ne_zero n hb) M 1 0 = M 1 0 := by
      rw [(diagConjugate_entries _ _ M).2.2.1]
      field_simp
    rw [← he,norm_mul,norm_pow,norm_pow]
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    exact mul_le_mul_of_nonneg_left (hbound n) (by positivity)
  have hp : ‖b‖^2 < 1 := by nlinarith [norm_nonneg b]
  have ht : Tendsto (fun n : ℕ => (‖b‖^2)^n * R) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hp).mul_const R
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto' ht hle) (norm_nonneg _))

theorem entry_dist_le {F : Type*} [NormedField F] (M N : SL(2,F)) (i j : Fin 2) :
    dist (M i j) (N i j) ≤ dist M N :=
  (dist_le_pi_dist (M.val i) (N.val i) j).trans (dist_le_pi_dist M.val N.val i)

theorem lower_norm_le_dist_one {F : Type*} [NormedField F] (M : SL(2,F)) :
    ‖M 1 0‖ ≤ dist M 1 := by
  simpa using entry_dist_le M 1 1 0

def forwardConjugate (t : ℝ) (n : ℕ) (g : G) : G :=
  (psi t 1)^n*g*((psi t 1)⁻¹)^n

/-- Bounded forward displacements have no expanding component in either
the real or the 2-adic factor of the literal group. -/
theorem lower_zero_of_forward_bounded {t : ℝ} (ht : 0 < t) (g : G) (R : ℝ)
    (hbnd : ∀ n : ℕ, dist (forwardConjugate t n g) 1 ≤ R) :
    g.1 1 0 = 0 ∧ g.2 1 0 = 0 := by
  constructor
  · refine lower_zero_of_bounded_conjugates (Real.exp (-t)) (Real.exp_ne_zero _) ?_ g.1 R ?_
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_lt_one_iff]
      linarith
    · intro n
      have h := (lower_norm_le_dist_one (forwardConjugate t n g).1).trans
        ((show dist (forwardConjugate t n g).1 (1 : G).1 ≤
          dist (forwardConjugate t n g) 1 by rw [Prod.dist_eq]; exact le_max_left _ _).trans (hbnd n))
      change ‖((BBEKDynamics.diagonal (Real.exp (-t)) (Real.exp_ne_zero _))^n * g.1 *
        ((BBEKDynamics.diagonal (Real.exp (-t)) (Real.exp_ne_zero _))⁻¹)^n) 1 0‖ ≤ R at h
      rwa [power_diagConjugate] at h
  · refine lower_zero_of_bounded_conjugates ((2:Q2)^(1:ℤ))
      (zpow_ne_zero _ (by norm_num)) ?_ g.2 R ?_
    · rw [show ‖(2:Q2)^(1:ℤ)‖ = (2:ℝ)^(-(1:ℤ)) from padicNormE.norm_p_zpow (p:=2) 1]
      norm_num
    · intro n
      have h := (lower_norm_le_dist_one (forwardConjugate t n g).2).trans
        ((show dist (forwardConjugate t n g).2 (1 : G).2 ≤
          dist (forwardConjugate t n g) 1 by rw [Prod.dist_eq]; exact le_max_right _ _).trans (hbnd n))
      change ‖((BBEKDynamics.diagonal ((2:Q2)^(1:ℤ)) (zpow_ne_zero _ (by norm_num)))^n * g.2 *
        ((BBEKDynamics.diagonal ((2:Q2)^(1:ℤ)) (zpow_ne_zero _ (by norm_num)))⁻¹)^n) 1 0‖ ≤ R at h
      rwa [power_diagConjugate] at h

theorem diagConjugate_dist_le {F : Type*} [NormedField F] (b : F) (hb : b ≠ 0)
    (hbn : ‖b‖ ≤ 1) (M N : SL(2,F)) (hM : M 1 0 = 0) (hN : N 1 0 = 0) :
    dist (diagConjugate b hb M) (diagConjugate b hb N) ≤ dist M N := by
  change dist (diagConjugate b hb M).val (diagConjugate b hb N).val ≤ dist M N
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro j
  have hMe := diagConjugate_entries b hb M
  have hNe := diagConjugate_entries b hb N
  fin_cases i <;> fin_cases j
  · change dist (diagConjugate b hb M 0 0) (diagConjugate b hb N 0 0) ≤ dist M N
    rw [hMe.1,hNe.1]
    exact entry_dist_le M N 0 0
  · change dist (diagConjugate b hb M 0 1) (diagConjugate b hb N 0 1) ≤ dist M N
    rw [hMe.2.1,hNe.2.1,dist_eq_norm,← mul_sub,norm_mul]
    calc
      ‖b^2‖ * ‖M 0 1-N 0 1‖ ≤ ‖M 0 1-N 0 1‖ := by
        apply mul_le_of_le_one_left (norm_nonneg _)
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hbn
      _ ≤ dist M N := by simpa only [dist_eq_norm] using entry_dist_le M N 0 1
  · change dist (diagConjugate b hb M 1 0) (diagConjugate b hb N 1 0) ≤ dist M N
    simp only [hMe.2.2.1,hNe.2.2.1,hM,hN,mul_zero,dist_self]
    exact dist_nonneg
  · change dist (diagConjugate b hb M 1 1) (diagConjugate b hb N 1 1) ≤ dist M N
    rw [hMe.2.2.2,hNe.2.2.2]
    exact entry_dist_le M N 1 1

/-- Forward conjugation is nonexpanding on the remaining upper-triangular
directions, in the actual entrywise product maximum metric. -/
theorem forwardConjugate_dist_le {t : ℝ} (ht : 0 < t) (g h : G)
    (hg : g.1 1 0 = 0 ∧ g.2 1 0 = 0) (hh : h.1 1 0 = 0 ∧ h.2 1 0 = 0)
    (n : ℕ) : dist (forwardConjugate t n g) (forwardConjugate t n h) ≤ dist g h := by
  rw [Prod.dist_eq,Prod.dist_eq]
  apply max_le_max
  · change dist
      ((BBEKDynamics.diagonal (Real.exp (-t)) (Real.exp_ne_zero _))^n*g.1*
        ((BBEKDynamics.diagonal (Real.exp (-t)) (Real.exp_ne_zero _))⁻¹)^n)
      ((BBEKDynamics.diagonal (Real.exp (-t)) (Real.exp_ne_zero _))^n*h.1*
        ((BBEKDynamics.diagonal (Real.exp (-t)) (Real.exp_ne_zero _))⁻¹)^n) ≤ _
    rw [power_diagConjugate,power_diagConjugate]
    apply diagConjugate_dist_le _ _ _ _ _ hg.1 hh.1
    rw [norm_pow]
    apply pow_le_one₀ (norm_nonneg _)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_one_iff]
    linarith
  · change dist
      ((BBEKDynamics.diagonal ((2:Q2)^(1:ℤ)) (zpow_ne_zero _ (by norm_num)))^n*g.2*
        ((BBEKDynamics.diagonal ((2:Q2)^(1:ℤ)) (zpow_ne_zero _ (by norm_num)))⁻¹)^n)
      ((BBEKDynamics.diagonal ((2:Q2)^(1:ℤ)) (zpow_ne_zero _ (by norm_num)))^n*h.2*
        ((BBEKDynamics.diagonal ((2:Q2)^(1:ℤ)) (zpow_ne_zero _ (by norm_num)))⁻¹)^n) ≤ _
    rw [power_diagConjugate,power_diagConjugate]
    apply diagConjugate_dist_le _ _ _ _ _ hg.2 hh.2
    rw [norm_pow]
    apply pow_le_one₀ (norm_nonneg _)
    rw [show ‖(2:Q2)^(1:ℤ)‖ = (2:ℝ)^(-(1:ℤ)) from padicNormE.norm_p_zpow (p:=2) 1]
    norm_num

end VV.BBEKEntropyExpansive
