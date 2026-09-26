import VV.BBEKShearFamilyNonconcentration
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Sequences


/-! Quantitative vanishing of the non-root entries in the actual quadratic shear. -/

noncomputable section
open Filter Topology
open scoped MatrixGroups
namespace VV.BBEKShearLimit
open BBEKQuadraticScale BBEKSl2Shear BBEKEntropyExpansive

lemma admissible_time_le_extra {s t k : ℕ}
    (hk : k < min s (t / 2) / 4 + 1) : k ≤ extraTime s t k := by
  dsimp [extraTime]
  omega

lemma upper_square_le {b : ℝ} (hb : 0 ≤ b) {k n : ℕ}
    (hkn : k ≤ n) (hquad : (4 : ℝ)^(k+2*n)*b ≤ 1) :
    ((4 : ℝ)^k*b)^2 ≤ b := by
  have hp : (4 : ℝ)^(2*k) ≤ (4 : ℝ)^(k+2*n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hsmall : (4 : ℝ)^(2*k)*b ≤ 1 :=
    (mul_le_mul_of_nonneg_right hp hb).trans hquad
  calc
    ((4 : ℝ)^k*b)^2 = ((4 : ℝ)^(2*k)*b)*b := by
      rw [show 2*k = k*2 by omega, pow_mul, mul_pow]
      ring
    _ ≤ 1*b := mul_le_mul_of_nonneg_right hsmall hb
    _ = b := one_mul _

lemma diagonal_square_le {b : ℝ} (hb : 0 ≤ b) {k n : ℕ}
    (hquad : (4 : ℝ)^(k+2*n)*b ≤ 1) :
    ((4 : ℝ)^(k+n)*b)^2 ≤ (4 : ℝ)^k*b := by
  calc
    ((4 : ℝ)^(k+n)*b)^2 =
        ((4 : ℝ)^k*b)*((4 : ℝ)^(k+2*n)*b) := by
      have hp : ((4 : ℝ)^(k+n))^2 = (4 : ℝ)^k * (4 : ℝ)^(k+2*n) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [mul_pow, hp]
      ring
    _ ≤ ((4 : ℝ)^k*b)*1 :=
      mul_le_mul_of_nonneg_left hquad (mul_nonneg (by positivity) hb)
    _ = (4 : ℝ)^k*b := mul_one _

lemma upper_le_sqrt {b : ℝ} (hb : 0 ≤ b) {k n : ℕ}
    (hkn : k ≤ n) (hquad : (4 : ℝ)^(k+2*n)*b ≤ 1) :
    (4 : ℝ)^k*b ≤ Real.sqrt b :=
  Real.le_sqrt_of_sq_le (upper_square_le hb hkn hquad)

lemma diagonal_le_sqrt_sqrt {b : ℝ} (hb : 0 ≤ b) {k n : ℕ}
    (hkn : k ≤ n) (hquad : (4 : ℝ)^(k+2*n)*b ≤ 1) :
    (4 : ℝ)^(k+n)*b ≤ Real.sqrt (Real.sqrt b) :=
  (Real.le_sqrt_of_sq_le (diagonal_square_le hb hquad)).trans
    (Real.sqrt_le_sqrt (upper_le_sqrt hb hkn hquad))

variable {F : Type*} [NormedField F]

lemma norm_square_pow {a : F} (ha : ‖a‖ = 2) (k : ℕ) :
    ‖(a^k)^2‖ = (4 : ℝ)^k := by
  rw [← pow_mul, Nat.mul_comm k 2, norm_even_pow ha]

lemma norm_inverse_square_pow_le_one {a : F} (ha : ‖a‖ = 2) (k : ℕ) :
    ‖(a^k)⁻¹^2‖ ≤ 1 := by
  rw [inv_pow, norm_inv, norm_square_pow ha]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- All three entries outside the expanding root converge uniformly to their
identity values as the original displacement converges to the identity.
The root parameter only needs a bounded norm. -/
theorem nonroot_entry_bounds {a : F} (ha : ‖a‖ = 2) (ha0 : a ≠ 0)
    (g : SL(2,F)) {k n : ℕ} (hkn : k ≤ n)
    (hquad : ‖quadraticCoefficient a g k n‖ ≤ 1)
    {R : ℝ} {v : F} (hv : ‖v‖ ≤ R) :
    let h := lowerShear (a^(2*n)*v) (diagConjugate (a^k) (pow_ne_zero k ha0) g)
    ‖h 0 1‖ ≤ Real.sqrt ‖g 0 1‖ ∧
    ‖h 0 0 - g 0 0‖ ≤ Real.sqrt (Real.sqrt ‖g 0 1‖)*R ∧
    ‖h 1 1 - g 1 1‖ ≤ Real.sqrt (Real.sqrt ‖g 0 1‖)*R := by
  dsimp only
  rw [norm_quadraticCoefficient ha] at hquad
  rcases diagConjugate_entries (a^k) (pow_ne_zero k ha0) g with ⟨h00,h01,h10,h11⟩
  have hnorm : ‖(a^k)^2 * g 0 1 * (a^(2*n)*v)‖ =
      (4 : ℝ)^(k+n)*‖g 0 1‖*‖v‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_square_pow ha, norm_even_pow ha, pow_add]
    ring
  have hdiag : ‖(a^k)^2 * g 0 1 * (a^(2*n)*v)‖ ≤
      Real.sqrt (Real.sqrt ‖g 0 1‖)*R := by
    rw [hnorm]
    exact mul_le_mul (diagonal_le_sqrt_sqrt (norm_nonneg _) hkn hquad) hv
      (norm_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · rw [lowerShear_01,h01,norm_mul,norm_square_pow ha]
    exact upper_le_sqrt (norm_nonneg _) hkn hquad
  · rw [lowerShear_00,h00,h01,sub_sub_cancel_left,norm_neg]
    exact hdiag
  · rw [lowerShear_11,h11,h01,add_sub_cancel_left]
    exact hdiag

/-- The constant term left over after diagonal contraction is bounded by
its original lower-root entry. -/
theorem lower_constant_le {a : F} (ha : ‖a‖ = 2) (g : SL(2,F)) (k : ℕ) :
    ‖(a^k)⁻¹^2 * g 1 0‖ ≤ ‖g 1 0‖ := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_inverse_square_pow_le_one ha k)
    (norm_nonneg _)).trans_eq (one_mul _)

/-- The actual lower entry is bounded and stays away from zero whenever
its nonconstant polynomial does, up to the vanishing original error. -/
theorem lower_entry_bounds {a : F} (ha : ‖a‖ = 2) (ha0 : a ≠ 0)
    (g : SL(2,F)) (k n : ℕ)
    (hlin : ‖linearCoefficient a g n‖ ≤ 1)
    (hquad : ‖quadraticCoefficient a g k n‖ ≤ 1)
    {R δ : ℝ} {v : F} (hv : ‖v‖ ≤ R)
    (haway : δ ≤ ‖linearCoefficient a g n*v + quadraticCoefficient a g k n*v^2‖) :
    let h := lowerShear (a^(2*n)*v) (diagConjugate (a^k) (pow_ne_zero k ha0) g)
    ‖h 1 0‖ ≤ ‖g 1 0‖ + R + R^2 ∧ δ-‖g 1 0‖ ≤ ‖h 1 0‖ := by
  dsimp only
  rw [actual_lower_shear a ha0]
  have hR : 0 ≤ R := (norm_nonneg _).trans hv
  have hl : ‖linearCoefficient a g n*v‖ ≤ R := by
    rw [norm_mul]
    exact (mul_le_mul hlin hv (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hq : ‖quadraticCoefficient a g k n*v^2‖ ≤ R^2 := by
    rw [norm_mul,norm_pow]
    exact (mul_le_mul hquad (pow_le_pow_left₀ (norm_nonneg _) hv 2)
      (sq_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hc := lower_constant_le ha g k
  constructor
  · exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add hc hl)) hq)
  · have ht := norm_add_le
      ((a^k)⁻¹^2*g 1 0 + linearCoefficient a g n*v + quadraticCoefficient a g k n*v^2)
      (-((a^k)⁻¹^2*g 1 0))
    have he : (a^k)⁻¹^2*g 1 0 + linearCoefficient a g n*v +
        quadraticCoefficient a g k n*v^2 + -((a^k)⁻¹^2*g 1 0) =
        linearCoefficient a g n*v + quadraticCoefficient a g k n*v^2 := by ring
    rw [he,norm_neg] at ht
    linarith





/-- Normalized genuine SL₂ shears of displacements tending to the identity
have a subsequence converging to a nonidentity element of the lower root.
The nonzero bound is furnished by the polynomial sublevel estimate, rather
than by an assumed nonzero limit. -/
theorem exists_nonzero_lower_limit [ProperSpace F]
    {a : F} (ha : ‖a‖ = 2) (ha0 : a ≠ 0)
    (g : ℕ → SL(2,F)) (hg : Tendsto g atTop (𝓝 1))
    (k n : ℕ → ℕ) (v : ℕ → F) {R δ : ℝ} (hδ : 0 < δ)
    (hkn : ∀ i, k i ≤ n i) (hv : ∀ i, ‖v i‖ ≤ R)
    (hlin : ∀ i, ‖linearCoefficient a (g i) (n i)‖ ≤ 1)
    (hquad : ∀ i, ‖quadraticCoefficient a (g i) (k i) (n i)‖ ≤ 1)
    (haway : ∀ i, δ ≤ ‖linearCoefficient a (g i) (n i)*v i +
      quadraticCoefficient a (g i) (k i) (n i)*(v i)^2‖) :
    let h := fun i => lowerShear (a^(2*n i)*v i)
      (diagConjugate (a^k i) (pow_ne_zero (k i) ha0) (g i))
    ∃ u : F, u ≠ 0 ∧ δ ≤ ‖u‖ ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (h ∘ φ) atTop (𝓝 (BBEKFiniteQuotients.lower u)) := by
  let h := fun i => lowerShear (a^(2*n i)*v i)
    (diagConjugate (a^k i) (pow_ne_zero (k i) ha0) (g i))
  change ∃ u : F, u ≠ 0 ∧ δ ≤ ‖u‖ ∧ ∃ φ : ℕ → ℕ,
    StrictMono φ ∧ Tendsto (h ∘ φ) atTop (𝓝 (BBEKFiniteQuotients.lower u))
  have hgij (i j : Fin 2) : Tendsto (fun l => g l i j) atTop (𝓝 ((1 : SL(2,F)) i j)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hg) i) j
  have hg00 : Tendsto (fun l => g l 0 0) atTop (𝓝 1) := by simpa using hgij 0 0
  have hg01 : Tendsto (fun l => g l 0 1) atTop (𝓝 0) := by simpa using hgij 0 1
  have hg10 : Tendsto (fun l => g l 1 0) atTop (𝓝 0) := by simpa using hgij 1 0
  have hg11 : Tendsto (fun l => g l 1 1) atTop (𝓝 1) := by simpa using hgij 1 1
  have hnr (i : ℕ) := nonroot_entry_bounds ha ha0 (g i) (hkn i) (hquad i) (hv i)
  have hlr (i : ℕ) := lower_entry_bounds ha ha0 (g i) (k i) (n i)
    (hlin i) (hquad i) (hv i) (haway i)
  have hgsqrt : Tendsto (fun i => Real.sqrt ‖g i 0 1‖) atTop (𝓝 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hg01.norm
  have hgsqrt2 : Tendsto (fun i => Real.sqrt (Real.sqrt ‖g i 0 1‖)*R) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hgsqrt).mul_const R
  have hh01 : Tendsto (fun i => h i 0 1) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun i => norm_nonneg _) (fun i => (hnr i).1) hgsqrt)
  have hh00diff : Tendsto (fun i => h i 0 0 - g i 0 0) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun i => norm_nonneg _) (fun i => (hnr i).2.1) hgsqrt2)
  have hh11diff : Tendsto (fun i => h i 1 1 - g i 1 1) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun i => norm_nonneg _) (fun i => (hnr i).2.2) hgsqrt2)
  have hh00 : Tendsto (fun i => h i 0 0) atTop (𝓝 1) := by
    simpa only [sub_add_cancel,zero_add] using hh00diff.add hg00
  have hh11 : Tendsto (fun i => h i 1 1) atTop (𝓝 1) := by
    simpa only [sub_add_cancel,zero_add] using hh11diff.add hg11
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto _ hg10).exists_norm_le
  have hmem (i : ℕ) : h i 1 0 ∈ Metric.closedBall (0 : F) (C+R+R^2) := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (hlr i).1.trans (by linarith [hC (g i 1 0) (Set.mem_range_self i)])
  obtain ⟨u,_,φ,hφ,hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  have hud : δ ≤ ‖u‖ := by
    have hglim := (hg10.comp hφ.tendsto_atTop).norm
    have hsum := hlim.norm.add hglim
    have hineq : ∀ᶠ i in atTop, δ ≤ ‖h (φ i) 1 0‖ + ‖g (φ i) 1 0‖ :=
      Eventually.of_forall fun i => by linarith [(hlr (φ i)).2]
    simpa only [norm_zero,add_zero] using ge_of_tendsto hsum hineq
  refine ⟨u, ?_, hud, φ, hφ, ?_⟩
  · intro hu
    rw [hu,norm_zero] at hud
    exact (not_le_of_gt hδ) hud
  · apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i <;> fin_cases j
    · simpa [BBEKFiniteQuotients.lower] using hh00.comp hφ.tendsto_atTop
    · simpa [BBEKFiniteQuotients.lower] using hh01.comp hφ.tendsto_atTop
    · simpa [BBEKFiniteQuotients.lower] using hlim
    · simpa [BBEKFiniteQuotients.lower] using hh11.comp hφ.tendsto_atTop

end VV.BBEKShearLimit
