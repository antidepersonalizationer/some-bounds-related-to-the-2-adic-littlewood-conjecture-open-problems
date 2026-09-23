import VV.BBEKRigidityEscape

/-!
# Escape from a Mahler compact using one root and the split diagonal

For the specialized `SL₂(ℝ) × SL₂(ℚ₂)` quotient, one complete root group
together with the full split diagonal already moves every point out of every
positive Mahler compact.  Thus the low-entropy argument only has to produce
one nonzero ambient root invariance; an opposite root is not needed for the
final compact-support contradiction.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped MatrixGroups Topology

namespace VV.BBEKRootEscape
open BBEKDynamics BBEKQuotient BBEKOrbit BBEKDiagonal BBEKFactorEscape
  BBEKMeasureStabilizer BBEKMautner BBEKLattice BBEKDyadic

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem norm_pair_zero_right {E : Type*} [SeminormedAddCommGroup E] (a : E) :
    ‖![a, 0]‖ = ‖a‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
    intro i
    fin_cases i <;> simp
  · simpa using norm_le_pi_norm (![a, 0]) 0

private theorem norm_pair_zero_left {E : Type*} [SeminormedAddCommGroup E] (a : E) :
    ‖![0, a]‖ = ‖a‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
    intro i
    fin_cases i <;> simp
  · simpa using norm_le_pi_norm (![0, a]) 1

/-- A lower triangular element of `SL₂(ℝ)` can shrink any nonzero vector.
The element is returned with its literal diagonal/lower factorization. -/
theorem exists_real_lower_diagonal_shrink (w : Fin 2 → ℝ) (hw : w ≠ 0)
    { δ : ℝ } (hδ : 0 < δ) :
    ∃ a : ℝ, ∃ ha : a ≠ 0, ∃ u : ℝ,
      ‖((diagonal a ha) * lower u).val *ᵥ w‖ < δ := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      funext i
      fin_cases i <;> assumption
    let a : ℝ := 2 * |w 1| / δ
    have ha : a ≠ 0 := by
      dsimp [a]
      positivity
    refine ⟨a, ha, 0, ?_⟩
    have hv : ((diagonal a ha) * lower (0 : ℝ)).val *ᵥ w = ![0, a⁻¹ * w 1] := by
      funext i
      fin_cases i <;>
        simp [BBEKDynamics.diagonal, lower, Matrix.mulVec, dotProduct, Matrix.mul_apply,
          Fin.sum_univ_two, h0]
    rw [hv, norm_pair_zero_left, Real.norm_eq_abs, abs_mul, abs_inv]
    have hw1 : 0 < |w 1| := abs_pos.mpr h1
    have ha_pos : 0 < a := by dsimp [a]; positivity
    rw [abs_of_pos ha_pos]
    have heq : a⁻¹ * |w 1| = δ / 2 := by
      dsimp [a]
      field_simp [ne_of_gt hw1, ne_of_gt hδ]
      <;> ring
    rw [heq]
    linarith
  · let a : ℝ := δ / (2 * |w 0|)
    have ha : a ≠ 0 := by
      dsimp [a]
      positivity
    let u : ℝ := -(w 1 / w 0)
    refine ⟨a, ha, u, ?_⟩
    have hv : ((diagonal a ha) * lower u).val *ᵥ w = ![a * w 0, 0] := by
      funext i
      fin_cases i <;>
        simp [BBEKDynamics.diagonal, lower, u, Matrix.mulVec, dotProduct, Matrix.mul_apply,
          Fin.sum_univ_two, h0] <;> field_simp <;> ring
    rw [hv, norm_pair_zero_right, Real.norm_eq_abs, abs_mul]
    have hw0 : 0 < |w 0| := abs_pos.mpr h0
    have ha_pos : 0 < a := by dsimp [a]; positivity
    rw [abs_of_pos ha_pos]
    have heq : a * |w 0| = δ / 2 := by
      dsimp [a]
      field_simp [ne_of_gt hw0]
      <;> ring
    rw [heq]
    linarith

/-- An upper triangular element of `SL₂(ℝ)` can shrink any nonzero vector. -/
theorem exists_real_upper_diagonal_shrink (w : Fin 2 → ℝ) (hw : w ≠ 0)
    { δ : ℝ } (hδ : 0 < δ) :
    ∃ a : ℝ, ∃ ha : a ≠ 0, ∃ u : ℝ,
      ‖((diagonal a ha) * BBEKFiniteQuotients.upper u).val *ᵥ w‖ < δ := by
  by_cases h1 : w 1 = 0
  · have h0 : w 0 ≠ 0 := by
      intro h0
      apply hw
      funext i
      fin_cases i <;> assumption
    let a : ℝ := δ / (2 * |w 0|)
    have ha : a ≠ 0 := by dsimp [a]; positivity
    refine ⟨a, ha, 0, ?_⟩
    have hv : ((diagonal a ha) * BBEKFiniteQuotients.upper (0 : ℝ)).val *ᵥ w =
        ![a * w 0, 0] := by
      funext i
      fin_cases i <;>
        simp [BBEKDynamics.diagonal, BBEKFiniteQuotients.upper, Matrix.mulVec, dotProduct,
          Matrix.mul_apply, Fin.sum_univ_two, h1]
    rw [hv, norm_pair_zero_right, Real.norm_eq_abs, abs_mul]
    have hw0 : 0 < |w 0| := abs_pos.mpr h0
    have ha_pos : 0 < a := by dsimp [a]; positivity
    rw [abs_of_pos ha_pos]
    have heq : a * |w 0| = δ / 2 := by
      dsimp [a]
      field_simp [ne_of_gt hw0]
      <;> ring
    rw [heq]
    linarith
  · let a : ℝ := 2 * |w 1| / δ
    have ha : a ≠ 0 := by dsimp [a]; positivity
    let u : ℝ := -(w 0 / w 1)
    refine ⟨a, ha, u, ?_⟩
    have hv : ((diagonal a ha) * BBEKFiniteQuotients.upper u).val *ᵥ w =
        ![0, a⁻¹ * w 1] := by
      funext i
      fin_cases i <;>
        simp [BBEKDynamics.diagonal, BBEKFiniteQuotients.upper, u, Matrix.mulVec, dotProduct,
          Matrix.mul_apply, Fin.sum_univ_two, h1] <;> field_simp <;> ring
    rw [hv, norm_pair_zero_left, Real.norm_eq_abs, abs_mul, abs_inv]
    have hw1 : 0 < |w 1| := abs_pos.mpr h1
    have ha_pos : 0 < a := by dsimp [a]; positivity
    rw [abs_of_pos ha_pos]
    have heq : a⁻¹ * |w 1| = δ / 2 := by
      dsimp [a]
      field_simp [ne_of_gt hw1, ne_of_gt hδ]
      <;> ring
    rw [heq]
    linarith

private theorem padic_two_norm_lt_one : ‖(2 : Q2)‖ < 1 := by
  have he : ‖(2 : Q2)‖ = (2 : ℝ)⁻¹ := padicNormE.norm_p
  rw [he]
  norm_num

/-- A lower triangular element of `SL₂(ℚ₂)` can shrink any nonzero vector. -/
theorem exists_padic_lower_diagonal_shrink (w : Fin 2 → Q2) (hw : w ≠ 0)
    { δ : ℝ } (hδ : 0 < δ) :
    ∃ a : Q2, ∃ ha : a ≠ 0, ∃ u : Q2,
      ‖((diagonal a ha) * lower u).val *ᵥ w‖ < δ := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      funext i
      fin_cases i <;> assumption
    have ht : Tendsto (fun k : ℕ => (2 : Q2)^k * w 1) atTop (nhds 0) := by
      simpa only [smul_eq_mul, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one padic_two_norm_lt_one).smul_const (w 1)
    obtain ⟨k, hk⟩ := (ht.eventually (Metric.ball_mem_nhds 0 hδ)).exists
    let a : Q2 := ((2 : Q2)^k)⁻¹
    have ha : a ≠ 0 := inv_ne_zero (pow_ne_zero k (by norm_num))
    refine ⟨a, ha, 0, ?_⟩
    have hv : ((diagonal a ha) * lower (0 : Q2)).val *ᵥ w =
        ![0, (2 : Q2)^k * w 1] := by
      funext i
      fin_cases i <;>
        simp [BBEKDynamics.diagonal, lower, a, Matrix.mulVec, dotProduct,
          Matrix.mul_apply, Fin.sum_univ_two, h0]
    rw [hv, norm_pair_zero_left]
    simpa only [dist_zero_right] using hk
  · let u : Q2 := -(w 1 / w 0)
    have ht : Tendsto (fun k : ℕ => (2 : Q2)^k * w 0) atTop (nhds 0) := by
      simpa only [smul_eq_mul, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one padic_two_norm_lt_one).smul_const (w 0)
    obtain ⟨k, hk⟩ := (ht.eventually (Metric.ball_mem_nhds 0 hδ)).exists
    have ha : (2 : Q2)^k ≠ 0 := pow_ne_zero k (by norm_num)
    refine ⟨(2 : Q2)^k, ha, u, ?_⟩
    have hv : ((diagonal ((2 : Q2)^k) ha) * lower u).val *ᵥ w =
        ![(2 : Q2)^k * w 0, 0] := by
      funext i
      fin_cases i <;>
        simp [BBEKDynamics.diagonal, lower, u, Matrix.mulVec, dotProduct,
          Matrix.mul_apply, Fin.sum_univ_two, h0] <;> field_simp <;> ring
    rw [hv, norm_pair_zero_right]
    simpa only [dist_zero_right] using hk

/-- An upper triangular element of `SL₂(ℚ₂)` can shrink any nonzero vector. -/
theorem exists_padic_upper_diagonal_shrink (w : Fin 2 → Q2) (hw : w ≠ 0)
    { δ : ℝ } (hδ : 0 < δ) :
    ∃ a : Q2, ∃ ha : a ≠ 0, ∃ u : Q2,
      ‖((diagonal a ha) * BBEKFiniteQuotients.upper u).val *ᵥ w‖ < δ := by
  by_cases h1 : w 1 = 0
  · have h0 : w 0 ≠ 0 := by
      intro h0
      apply hw
      funext i
      fin_cases i <;> assumption
    have ht : Tendsto (fun k : ℕ => (2 : Q2)^k * w 0) atTop (nhds 0) := by
      simpa only [smul_eq_mul, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one padic_two_norm_lt_one).smul_const (w 0)
    obtain ⟨k, hk⟩ := (ht.eventually (Metric.ball_mem_nhds 0 hδ)).exists
    have ha : (2 : Q2)^k ≠ 0 := pow_ne_zero k (by norm_num)
    refine ⟨(2 : Q2)^k, ha, 0, ?_⟩
    have hv : ((diagonal ((2 : Q2)^k) ha) *
        BBEKFiniteQuotients.upper (0 : Q2)).val *ᵥ w =
          ![(2 : Q2)^k * w 0, 0] := by
      funext i
      fin_cases i <;>
        simp [BBEKDynamics.diagonal, BBEKFiniteQuotients.upper, Matrix.mulVec,
          dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h1]
    rw [hv, norm_pair_zero_right]
    simpa only [dist_zero_right] using hk
  · let u : Q2 := -(w 0 / w 1)
    have ht : Tendsto (fun k : ℕ => (2 : Q2)^k * w 1) atTop (nhds 0) := by
      simpa only [smul_eq_mul, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one padic_two_norm_lt_one).smul_const (w 1)
    obtain ⟨k, hk⟩ := (ht.eventually (Metric.ball_mem_nhds 0 hδ)).exists
    let a : Q2 := ((2 : Q2)^k)⁻¹
    have ha : a ≠ 0 := inv_ne_zero (pow_ne_zero k (by norm_num))
    refine ⟨a, ha, u, ?_⟩
    have hv : ((diagonal a ha) * BBEKFiniteQuotients.upper u).val *ᵥ w =
        ![0, (2 : Q2)^k * w 1] := by
      funext i
      fin_cases i <;>
        simp [BBEKDynamics.diagonal, BBEKFiniteQuotients.upper, u, a,
          Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h1] <;>
          field_simp <;> ring
    rw [hv, norm_pair_zero_left]
    simpa only [dist_zero_right] using hk

/-- Any specified family of real matrices which can shrink every nonzero
vector can move every quotient point out of `K δ`. -/
theorem exists_real_not_mem_K_of_shrink (P : SL(2, ℝ) → Prop)
    (hshrink : ∀ (w : Fin 2 → ℝ), w ≠ 0 → ∀ { δ : ℝ }, 0 < δ →
      ∃ g : SL(2, ℝ), P g ∧ ‖g.val *ᵥ w‖ < δ)
    (q : X) { δ : ℝ } (hδ : 0 < δ) :
    ∃ g : SL(2, ℝ), P g ∧ (g, (1 : SL(2, Q2))) • q ∉ K δ := by
  induction q using Quotient.inductionOn with
  | h M =>
      have hevent : ∀ᶠ k : ℕ in atTop,
          dist ((2 : Q2) ^ k • (M.2.val *ᵥ fun i => (intFirst i : Q2))) 0 < δ :=
        (padic_scaled_first_tendsto_zero M).eventually (Metric.ball_mem_nhds 0 hδ)
      obtain ⟨k, hk⟩ := hevent.exists
      have hk' :
          ‖(2 : Q2) ^ k • (M.2.val *ᵥ fun i => (intFirst i : Q2))‖ < δ := by
        simpa only [dist_zero_right] using hk
      let w : Fin 2 → ℝ :=
        (2 : ℝ) ^ k • (M.1.val *ᵥ fun i => (intFirst i : ℝ))
      have hw : w ≠ 0 := by
        exact smul_ne_zero (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0))
          (mulVec_intFirst_ne_zero M.1)
      obtain ⟨g, hgP, hg⟩ := hshrink w hw hδ
      refine ⟨g, hgP, ?_⟩
      intro hK
      have hs := (mem_K_mk_iff δ ((g, (1 : SL(2, Q2))) * M)).mp hK
        (scaledFirst k) (scaledFirst_ne_zero k)
      rw [scaledFirst_vectorImage] at hs
      have hreal :
          (2 : ℝ) ^ k •
              ((((g, (1 : SL(2, Q2))) * M).1).val *ᵥ
                fun i => (intFirst i : ℝ)) =
            g.val *ᵥ w := by
        funext i
        simp [w, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
        ring
      have hpadic :
          (2 : Q2) ^ k •
              ((((g, (1 : SL(2, Q2))) * M).2).val *ᵥ
                fun i => (intFirst i : Q2)) =
            (2 : Q2) ^ k • (M.2.val *ᵥ fun i => (intFirst i : Q2)) := by
        simp
      rw [hreal, hpadic] at hs
      change δ ≤ ‖(g.val *ᵥ w,
        (2 : Q2) ^ k • (M.2.val *ᵥ fun i => (intFirst i : Q2)))‖ at hs
      rw [Prod.norm_def] at hs
      exact (not_le_of_gt (max_lt hg hk')) hs

/-- The analogous lifting lemma for a specified family of 2-adic matrices. -/
theorem exists_padic_not_mem_K_of_shrink (P : SL(2, Q2) → Prop)
    (hshrink : ∀ (w : Fin 2 → Q2), w ≠ 0 → ∀ { δ : ℝ }, 0 < δ →
      ∃ g : SL(2, Q2), P g ∧ ‖g.val *ᵥ w‖ < δ)
    (q : X) { δ : ℝ } (hδ : 0 < δ) :
    ∃ g : SL(2, Q2), P g ∧ ((1 : SL(2, ℝ)), g) • q ∉ K δ := by
  induction q using Quotient.inductionOn with
  | h M =>
      have hevent : ∀ᶠ k : ℕ in atTop,
          dist (((2 : ℝ)⁻¹) ^ k •
            (M.1.val *ᵥ fun i => (intFirst i : ℝ))) 0 < δ :=
        (real_inverse_scaled_first_tendsto_zero M).eventually
          (Metric.ball_mem_nhds 0 hδ)
      obtain ⟨k, hk⟩ := hevent.exists
      have hk' :
          ‖((2 : ℝ)⁻¹) ^ k •
            (M.1.val *ᵥ fun i => (intFirst i : ℝ))‖ < δ := by
        simpa only [dist_zero_right] using hk
      let w : Fin 2 → Q2 :=
        ((2 : Q2)⁻¹) ^ k • (M.2.val *ᵥ fun i => (intFirst i : Q2))
      have hw : w ≠ 0 := by
        exact smul_ne_zero (pow_ne_zero k (inv_ne_zero (by norm_num : (2 : Q2) ≠ 0)))
          (mulVec_intFirst_ne_zero M.2)
      obtain ⟨g, hgP, hg⟩ := hshrink w hw hδ
      refine ⟨g, hgP, ?_⟩
      intro hK
      have hs := (mem_K_mk_iff δ (((1 : SL(2, ℝ)), g) * M)).mp hK
        (inverseScaledFirst k) (inverseScaledFirst_ne_zero k)
      rw [inverseScaledFirst_vectorImage] at hs
      have hreal :
          ((2 : ℝ)⁻¹) ^ k •
              (((((1 : SL(2, ℝ)), g) * M).1).val *ᵥ
                fun i => (intFirst i : ℝ)) =
            ((2 : ℝ)⁻¹) ^ k •
              (M.1.val *ᵥ fun i => (intFirst i : ℝ)) := by
        simp
      have hpadic :
          ((2 : Q2)⁻¹) ^ k •
              (((((1 : SL(2, ℝ)), g) * M).2).val *ᵥ
                fun i => (intFirst i : Q2)) =
            g.val *ᵥ w := by
        funext i
        simp [w, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
        ring
      rw [hreal, hpadic] at hs
      rw [Prod.norm_def] at hs
      exact (not_le_of_gt (max_lt hk' hg)) hs

theorem exists_real_lower_diagonal_not_mem_K (q : X) { δ : ℝ } (hδ : 0 < δ) :
    ∃ a : ℝ, ∃ ha : a ≠ 0, ∃ u : ℝ,
      ((diagonal a ha * lower u), (1 : SL(2, Q2))) • q ∉ K δ := by
  obtain ⟨g, ⟨a, ha, u, rfl⟩, hg⟩ := exists_real_not_mem_K_of_shrink
    (fun g => ∃ a : ℝ, ∃ ha : a ≠ 0, ∃ u : ℝ, g = diagonal a ha * lower u)
    (fun w hw {δ} hδ => by
      obtain ⟨a, ha, u, h⟩ := exists_real_lower_diagonal_shrink w hw hδ
      exact ⟨diagonal a ha * lower u, ⟨a, ha, u, rfl⟩, h⟩) q hδ
  exact ⟨a, ha, u, hg⟩

theorem exists_real_upper_diagonal_not_mem_K (q : X) { δ : ℝ } (hδ : 0 < δ) :
    ∃ a : ℝ, ∃ ha : a ≠ 0, ∃ u : ℝ,
      ((diagonal a ha * BBEKFiniteQuotients.upper u), (1 : SL(2, Q2))) • q ∉ K δ := by
  obtain ⟨g, ⟨a, ha, u, rfl⟩, hg⟩ := exists_real_not_mem_K_of_shrink
    (fun g => ∃ a : ℝ, ∃ ha : a ≠ 0, ∃ u : ℝ,
      g = diagonal a ha * BBEKFiniteQuotients.upper u)
    (fun w hw {δ} hδ => by
      obtain ⟨a, ha, u, h⟩ := exists_real_upper_diagonal_shrink w hw hδ
      exact ⟨diagonal a ha * BBEKFiniteQuotients.upper u, ⟨a, ha, u, rfl⟩, h⟩) q hδ
  exact ⟨a, ha, u, hg⟩

theorem exists_padic_lower_diagonal_not_mem_K (q : X) { δ : ℝ } (hδ : 0 < δ) :
    ∃ a : Q2, ∃ ha : a ≠ 0, ∃ u : Q2,
      ((1 : SL(2, ℝ)), (diagonal a ha * lower u)) • q ∉ K δ := by
  obtain ⟨g, ⟨a, ha, u, rfl⟩, hg⟩ := exists_padic_not_mem_K_of_shrink
    (fun g => ∃ a : Q2, ∃ ha : a ≠ 0, ∃ u : Q2, g = diagonal a ha * lower u)
    (fun w hw {δ} hδ => by
      obtain ⟨a, ha, u, h⟩ := exists_padic_lower_diagonal_shrink w hw hδ
      exact ⟨diagonal a ha * lower u, ⟨a, ha, u, rfl⟩, h⟩) q hδ
  exact ⟨a, ha, u, hg⟩

theorem exists_padic_upper_diagonal_not_mem_K (q : X) { δ : ℝ } (hδ : 0 < δ) :
    ∃ a : Q2, ∃ ha : a ≠ 0, ∃ u : Q2,
      ((1 : SL(2, ℝ)), (diagonal a ha * BBEKFiniteQuotients.upper u)) • q ∉ K δ := by
  obtain ⟨g, ⟨a, ha, u, rfl⟩, hg⟩ := exists_padic_not_mem_K_of_shrink
    (fun g => ∃ a : Q2, ∃ ha : a ≠ 0, ∃ u : Q2,
      g = diagonal a ha * BBEKFiniteQuotients.upper u)
    (fun w hw {δ} hδ => by
      obtain ⟨a, ha, u, h⟩ := exists_padic_upper_diagonal_shrink w hw hδ
      exact ⟨diagonal a ha * BBEKFiniteQuotients.upper u, ⟨a, ha, u, rfl⟩, h⟩) q hδ
  exact ⟨a, ha, u, hg⟩

/-- Full invariance under just the real lower root, together with the already
available full diagonal invariance, contradicts compact Mahler support. -/
theorem no_supported_of_real_lower_root
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (hlower : ∀ u : ℝ, x u 0 ∈ measureStabilizer μ)
    { δ : ℝ } (hδ : 0 < δ) (hmass : μ (K δ) = 1) : False := by
  apply no_invariant_probability_of_compact_escape
    (H := measureStabilizer μ) μ (BBEKMahler.compact_K hδ) hmass
  intro q hq
  obtain ⟨a, ha, u, hu⟩ := exists_real_lower_diagonal_not_mem_K q hδ
  have hdA : (diagonal a ha, (1 : SL(2, Q2))) ∈ A :=
    ⟨⟨a, ha, rfl⟩, (diagonalGroup Q2).one_mem⟩
  have hd := A_le_measureStabilizer μ hdA
  have hr := hlower u
  have hm := (measureStabilizer μ).mul_mem hd hr
  refine ⟨⟨(diagonal a ha * lower u, (1 : SL(2, Q2))), ?_⟩, hu⟩
  simpa only [x, Prod.mk_mul_mk, mul_one, BBEKDynamics.lower_zero] using hm

theorem no_supported_of_real_upper_root
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (hupper : ∀ u : ℝ, upperPoint u 0 ∈ measureStabilizer μ)
    { δ : ℝ } (hδ : 0 < δ) (hmass : μ (K δ) = 1) : False := by
  apply no_invariant_probability_of_compact_escape
    (H := measureStabilizer μ) μ (BBEKMahler.compact_K hδ) hmass
  intro q hq
  obtain ⟨a, ha, u, hu⟩ := exists_real_upper_diagonal_not_mem_K q hδ
  have hdA : (diagonal a ha, (1 : SL(2, Q2))) ∈ A :=
    ⟨⟨a, ha, rfl⟩, (diagonalGroup Q2).one_mem⟩
  have hd := A_le_measureStabilizer μ hdA
  have hr := hupper u
  have hm := (measureStabilizer μ).mul_mem hd hr
  refine ⟨⟨(diagonal a ha * BBEKFiniteQuotients.upper u,
    (1 : SL(2, Q2))), ?_⟩, hu⟩
  simpa only [upperPoint, Prod.mk_mul_mk, BBEKFiniteQuotients.upper_zero,
    mul_one] using hm

theorem no_supported_of_padic_lower_root
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (hlower : ∀ u : Q2, x 0 u ∈ measureStabilizer μ)
    { δ : ℝ } (hδ : 0 < δ) (hmass : μ (K δ) = 1) : False := by
  apply no_invariant_probability_of_compact_escape
    (H := measureStabilizer μ) μ (BBEKMahler.compact_K hδ) hmass
  intro q hq
  obtain ⟨a, ha, u, hu⟩ := exists_padic_lower_diagonal_not_mem_K q hδ
  have hdA : ((1 : SL(2, ℝ)), diagonal a ha) ∈ A :=
    ⟨(diagonalGroup ℝ).one_mem, ⟨a, ha, rfl⟩⟩
  have hd := A_le_measureStabilizer μ hdA
  have hr := hlower u
  have hm := (measureStabilizer μ).mul_mem hd hr
  refine ⟨⟨((1 : SL(2, ℝ)), diagonal a ha * lower u), ?_⟩, hu⟩
  simpa only [x, Prod.mk_mul_mk, mul_one, BBEKDynamics.lower_zero] using hm

theorem no_supported_of_padic_upper_root
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (hupper : ∀ u : Q2, upperPoint 0 u ∈ measureStabilizer μ)
    { δ : ℝ } (hδ : 0 < δ) (hmass : μ (K δ) = 1) : False := by
  apply no_invariant_probability_of_compact_escape
    (H := measureStabilizer μ) μ (BBEKMahler.compact_K hδ) hmass
  intro q hq
  obtain ⟨a, ha, u, hu⟩ := exists_padic_upper_diagonal_not_mem_K q hδ
  have hdA : ((1 : SL(2, ℝ)), diagonal a ha) ∈ A :=
    ⟨(diagonalGroup ℝ).one_mem, ⟨a, ha, rfl⟩⟩
  have hd := A_le_measureStabilizer μ hdA
  have hr := hupper u
  have hm := (measureStabilizer μ).mul_mem hd hr
  refine ⟨⟨((1 : SL(2, ℝ)),
    diagonal a ha * BBEKFiniteQuotients.upper u), ?_⟩, hu⟩
  simpa only [upperPoint, Prod.mk_mul_mk, BBEKFiniteQuotients.upper_zero,
    mul_one] using hm

/-- A single nonzero stabilizing root element suffices, since full diagonal
normalization fills its entire one-dimensional root group. -/
theorem no_supported_of_any_nonzero_root
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    { δ : ℝ } (hδ : 0 < δ) (hmass : μ (K δ) = 1)
    (hroot :
      (∃ u : ℝ, u ≠ 0 ∧ x u 0 ∈ measureStabilizer μ) ∨
      (∃ u : ℝ, u ≠ 0 ∧ upperPoint u 0 ∈ measureStabilizer μ) ∨
      (∃ u : Q2, u ≠ 0 ∧ x 0 u ∈ measureStabilizer μ) ∨
      (∃ u : Q2, u ≠ 0 ∧ upperPoint 0 u ∈ measureStabilizer μ)) : False := by
  rcases hroot with ⟨u, hu0, hu⟩ | ⟨u, hu0, hu⟩ | ⟨u, hu0, hu⟩ | ⟨u, hu0, hu⟩
  · exact no_supported_of_real_lower_root μ
      (all_real_lower_mem_of_nonzero μ hu0 hu) hδ hmass
  · exact no_supported_of_real_upper_root μ
      (all_real_upper_mem_of_nonzero μ hu0 hu) hδ hmass
  · exact no_supported_of_padic_lower_root μ
      (all_padic_lower_mem_of_nonzero μ hu0 hu) hδ hmass
  · exact no_supported_of_padic_upper_root μ
      (all_padic_upper_mem_of_nonzero μ hu0 hu) hδ hmass

end VV.BBEKRootEscape
