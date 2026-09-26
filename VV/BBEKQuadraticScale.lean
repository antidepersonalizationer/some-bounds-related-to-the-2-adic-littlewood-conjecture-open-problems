import VV.BBEKPairedReturnTimes
import VV.BBEKSl2Shear
import VV.BBEKEntropyExpansive

/-! Quantitative normalization of the two nonconstant coefficients of an
SL₂ shear. The scale parameters are obtained from the actual coefficient
sizes, including the cases where either coefficient vanishes. -/
noncomputable section
namespace VV.BBEKQuadraticScale
open BBEKPairedReturnTimes

/-- Additional time needed to normalize the linear and quadratic terms. -/
def extraTime (s t k : ℕ) := min s ((t - k) / 2)

theorem exists_four_scale {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ s : ℕ, (4 : ℝ) ^ s * x ≤ 1 ∧ 1 < (4 : ℝ) ^ (s + 1) * x := by
  obtain ⟨s, hs, hnext⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ 1 / x by exact (le_div_iff₀ hx).2 (by linarith))
    (by norm_num : (1 : ℝ) < 4)
  exact ⟨s, (le_div_iff₀ hx).mp hs, (div_lt_iff₀ hx).mp hnext⟩

theorem linear_lower {d : ℝ} {s : ℕ}
    (hd : 1 < (4 : ℝ) ^ (s + 1) * d) :
    (1 / 16 : ℝ) < (4 : ℝ) ^ s * d := by
  rw [pow_succ] at hd
  nlinarith

theorem quadratic_lower {b : ℝ} (hb : 0 ≤ b) {t k : ℕ} (hk : k ≤ t)
    (hbsat : 1 < (4 : ℝ) ^ (t + 1) * b) :
    (1 / 16 : ℝ) < (4 : ℝ) ^ (k + 2 * ((t - k) / 2)) * b := by
  have hpow : (4 : ℝ) ^ (t + 1) ≤ (4 : ℝ) ^ (k + 2 * ((t - k) / 2) + 2) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have h := hbsat.trans_le (mul_le_mul_of_nonneg_right hpow hb)
  rw [pow_add] at h
  norm_num at h
  nlinarith

theorem normalized_upper {d b : ℝ} (hd : 0 ≤ d) (hb : 0 ≤ b)
    {s t k : ℕ} (hk : k ≤ t)
    (hds : (4 : ℝ) ^ s * d ≤ 1) (hbt : (4 : ℝ) ^ t * b ≤ 1) :
    (4 : ℝ) ^ extraTime s t k * d ≤ 1 ∧
      (4 : ℝ) ^ (k + 2 * extraTime s t k) * b ≤ 1 := by
  constructor
  · apply le_trans _ hds
    apply mul_le_mul_of_nonneg_right _ hd
    exact pow_le_pow_right₀ (by norm_num) (Nat.min_le_left _ _)
  · apply le_trans _ hbt
    apply mul_le_mul_of_nonneg_right _ hb
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [extraTime]
    omega

theorem normalized_lower {d b : ℝ} (hb : 0 ≤ b) {s t k : ℕ} (hk : k ≤ t)
    (hds : 1 < (4 : ℝ) ^ (s + 1) * d)
    (hbt : 1 < (4 : ℝ) ^ (t + 1) * b) :
    (1 / 16 : ℝ) < max ((4 : ℝ) ^ extraTime s t k * d)
      ((4 : ℝ) ^ (k + 2 * extraTime s t k) * b) := by
  rcases le_total s ((t - k) / 2) with h | h
  · exact (linear_lower hds).trans_le (by simp [extraTime, min_eq_left h])
  · exact (quadratic_lower hb hk hbt).trans_le (by simp [extraTime, min_eq_right h])

/-- Every noncentral quadratic shear has genuine integer normalization
scales: throughout the short search interval both nonconstant coefficients
are at most one, and at least one has size greater than `1/16`. -/
theorem exists_normalizing_scales (d b : ℝ)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (hd1 : d ≤ 1) (hb1 : b ≤ 1)
    (hnonzero : d ≠ 0 ∨ b ≠ 0) :
    ∃ s t : ℕ, ∀ k < min s (t / 2) / 4 + 1,
      k ≤ t ∧ (4 : ℝ) ^ extraTime s t k * d ≤ 1 ∧
      (4 : ℝ) ^ (k + 2 * extraTime s t k) * b ≤ 1 ∧
      (1 / 16 : ℝ) < max ((4 : ℝ) ^ extraTime s t k * d)
        ((4 : ℝ) ^ (k + 2 * extraTime s t k) * b) := by
  by_cases hd0 : d = 0
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm (hnonzero.resolve_left (not_not.mpr hd0)))
    obtain ⟨t, ht, ht'⟩ := exists_four_scale hbpos hb1
    refine ⟨t+1, t, ?_⟩
    intro k hk
    have hkt : k ≤ t := by omega
    have he : extraTime (t+1) t k = (t-k)/2 := by dsimp [extraTime]; omega
    have hup := normalized_upper hd hb hkt
      (s := t+1) (by simp [hd0]) ht
    refine ⟨hkt, hup.1, hup.2, ?_⟩
    exact (quadratic_lower hb hkt ht').trans_le (by rw [he]; exact le_max_right _ _)
  · obtain ⟨s, hs, hs'⟩ := exists_four_scale (lt_of_le_of_ne hd (Ne.symm hd0)) hd1
    by_cases hb0 : b = 0
    · refine ⟨s, 4*s+2, ?_⟩
      intro k hk
      have hkt : k ≤ 4*s+2 := by omega
      have he : extraTime s (4*s+2) k = s := by dsimp [extraTime]; omega
      refine ⟨hkt, ?_, by simp [hb0], ?_⟩
      · rwa [he]
      · exact (linear_lower hs').trans_le (by rw [he]; exact le_max_left _ _)
    · obtain ⟨t, ht, ht'⟩ := exists_four_scale (lt_of_le_of_ne hb (Ne.symm hb0)) hb1
      refine ⟨s, t, ?_⟩
      intro k hk
      have hkt : k ≤ t := by omega
      have hup := normalized_upper hd hb hkt hs ht
      exact ⟨hkt, hup.1, hup.2, normalized_lower hb hkt hs' ht'⟩



open scoped MatrixGroups
open BBEKSl2Shear BBEKEntropyExpansive
variable {F : Type*} [NormedField F]

/-- The genuine linear coefficient after diagonal time `k` and root scale `n`. -/
def linearCoefficient (a : F) (g : SL(2,F)) (n : ℕ) : F :=
  a ^ (2*n) * (g 0 0 - g 1 1)

/-- The genuine quadratic coefficient after diagonal time `k` and root scale `n`. -/
def quadraticCoefficient (a : F) (g : SL(2,F)) (k n : ℕ) : F :=
  -(a ^ (2*(k+2*n)) * g 0 1)

/-- These coefficients occur in the actual SL₂ matrix product. -/
theorem actual_lower_shear (a : F) (ha : a ≠ 0) (g : SL(2,F))
    (k n : ℕ) (v : F) :
    lowerShear (a^(2*n)*v) (diagConjugate (a^k) (pow_ne_zero k ha) g) 1 0 =
      (a^k)⁻¹^2 * g 1 0 + linearCoefficient a g n * v +
        quadraticCoefficient a g k n * v^2 := by
  rcases diagConjugate_entries (a^k) (pow_ne_zero k ha) g with ⟨h00,h01,h10,h11⟩
  rw [lowerShear_10,h00,h01,h10,h11]
  have hpow : (a^k)^2 * (a^(2*n))^2 = a^(2*(k+2*n)) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  dsimp [linearCoefficient,quadraticCoefficient]
  rw [← hpow]
  ring

theorem norm_even_pow {a : F} (ha : ‖a‖ = 2) (n : ℕ) :
    ‖a^(2*n)‖ = (4 : ℝ)^n := by
  rw [norm_pow,ha,pow_mul]
  norm_num

theorem norm_linearCoefficient {a : F} (ha : ‖a‖ = 2) (g : SL(2,F)) (n : ℕ) :
    ‖linearCoefficient a g n‖ = (4 : ℝ)^n * ‖g 0 0 - g 1 1‖ := by
  rw [linearCoefficient,norm_mul,norm_even_pow ha]

theorem norm_quadraticCoefficient {a : F} (ha : ‖a‖ = 2) (g : SL(2,F)) (k n : ℕ) :
    ‖quadraticCoefficient a g k n‖ = (4 : ℝ)^(k+2*n) * ‖g 0 1‖ := by
  rw [quadraticCoefficient,norm_neg,norm_mul,norm_even_pow ha]

/-- For an actual noncentral SL₂ displacement, normalization scales exist
and work at every admissible time, over either normed ground field. -/
theorem exists_actual_shear_scales {a : F} (ha : ‖a‖ = 2) (g : SL(2,F))
    (hd : ‖g 0 0 - g 1 1‖ ≤ 1) (hb : ‖g 0 1‖ ≤ 1)
    (hnoncentral : ¬ (∀ u : F, BBEKFiniteQuotients.lower u * g =
      g * BBEKFiniteQuotients.lower u)) :
    ∃ s t : ℕ, ∀ k < min s (t / 2) / 4 + 1,
      k ≤ t ∧ ‖linearCoefficient a g (extraTime s t k)‖ ≤ 1 ∧
      ‖quadraticCoefficient a g k (extraTime s t k)‖ ≤ 1 ∧
      (1 / 16 : ℝ) < max ‖linearCoefficient a g (extraTime s t k)‖
        ‖quadraticCoefficient a g k (extraTime s t k)‖ := by
  have hn : ‖g 0 0 - g 1 1‖ ≠ 0 ∨ ‖g 0 1‖ ≠ 0 := by
    by_contra h
    push_neg at h
    apply hnoncentral
    exact (commutes_lower_iff g).2 ⟨norm_eq_zero.mp h.2,
      sub_eq_zero.mp (norm_eq_zero.mp h.1)⟩
  obtain ⟨s,t,hst⟩ := exists_normalizing_scales _ _
    (norm_nonneg _) (norm_nonneg _) hd hb hn
  refine ⟨s,t,?_⟩
  intro k hk
  simpa only [norm_linearCoefficient ha,norm_quadraticCoefficient ha] using hst k hk

end VV.BBEKQuadraticScale
