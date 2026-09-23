import VV.BBEKOrbit
import VV.BBEKMahlerBridge
import VV.BBEKMahler
import VV.BBEKTopology
import Mathlib.MeasureTheory.Group.Action

/-!
No orbit of either local `SL₂` factor can stay in a positive Mahler set.

This is the elementary arithmetic substitute needed at the end of the
specialized low-entropy argument.  For the real factor we multiply a fixed
arithmetic vector by a large power of two.  Its 2-adic coordinate tends to
zero, while an element of `SL₂(ℝ)` can shrink its (nonzero) real coordinate.
The proof for the 2-adic factor is symmetric, using negative powers of two.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped MatrixGroups Topology

namespace VV.BBEKFactorEscape
open BBEKDynamics BBEKQuotient BBEKLattice BBEKOrbit BBEKDyadic

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem norm_pair_zero {E : Type*} [SeminormedAddCommGroup E] (a : E) :
    ‖![a, 0]‖ = ‖a‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
    intro i
    fin_cases i <;> simp
  · simpa using norm_le_pi_norm (![a, 0]) 0

def sendFirstOfFirst (a b : ℝ) (ha : a ≠ 0) : SL(2, ℝ) :=
  ⟨!![a⁻¹, 0; -b, a], by simp [Matrix.det_fin_two, ha]⟩

def sendFirstOfSecond (b : ℝ) (hb : b ≠ 0) : SL(2, ℝ) :=
  ⟨!![0, b⁻¹; -b, 0], by simp [Matrix.det_fin_two, hb]⟩

theorem exists_real_send_to_first (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    ∃ g : SL(2, ℝ), g.val *ᵥ w = ![1, 0] := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      funext i
      fin_cases i <;> assumption
    refine ⟨sendFirstOfSecond (w 1) h1, ?_⟩
    funext i
    fin_cases i <;>
      simp [sendFirstOfSecond, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  · refine ⟨sendFirstOfFirst (w 0) (w 1) h0, ?_⟩
    funext i
    fin_cases i <;>
      simp [sendFirstOfFirst, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0] <;> ring

/-- `SL₂(ℝ)` can make every nonzero vector arbitrarily small. -/
theorem exists_real_shrink {w : Fin 2 → ℝ} (hw : w ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : SL(2, ℝ), ‖g.val *ᵥ w‖ < δ := by
  obtain ⟨g, hg⟩ := exists_real_send_to_first w hw
  let d : SL(2, ℝ) := BBEKDynamics.diagonal (δ / 2) (by positivity)
  refine ⟨d * g, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec w d.val g.val, hg]
  have hv : d.val *ᵥ ![1, (0 : ℝ)] = ![δ / 2, 0] := by
    funext i
    fin_cases i <;>
      simp [d, BBEKDynamics.diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hv, norm_pair_zero, Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith

def sendFirstOfFirstQ2 (a b : Q2) (ha : a ≠ 0) : SL(2, Q2) :=
  ⟨!![a⁻¹, 0; -b, a], by simp [Matrix.det_fin_two, ha]⟩

def sendFirstOfSecondQ2 (b : Q2) (hb : b ≠ 0) : SL(2, Q2) :=
  ⟨!![0, b⁻¹; -b, 0], by simp [Matrix.det_fin_two, hb]⟩

theorem exists_padic_send_to_first (w : Fin 2 → Q2) (hw : w ≠ 0) :
    ∃ g : SL(2, Q2), g.val *ᵥ w = ![1, 0] := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      funext i
      fin_cases i <;> assumption
    refine ⟨sendFirstOfSecondQ2 (w 1) h1, ?_⟩
    funext i
    fin_cases i <;>
      simp [sendFirstOfSecondQ2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  · refine ⟨sendFirstOfFirstQ2 (w 0) (w 1) h0, ?_⟩
    funext i
    fin_cases i <;>
      simp [sendFirstOfFirstQ2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0] <;> ring

/-- `SL₂(ℚ₂)` can make every nonzero vector arbitrarily small. -/
theorem exists_padic_shrink {w : Fin 2 → Q2} (hw : w ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : SL(2, Q2), ‖g.val *ᵥ w‖ < δ := by
  obtain ⟨g, hg⟩ := exists_padic_send_to_first w hw
  have hp : ‖(2 : Q2)‖ < 1 := by
    have he : ‖(2 : Q2)‖ = (2 : ℝ)⁻¹ := padicNormE.norm_p
    rw [he]
    norm_num
  have ht := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp
  have hevent : ∀ᶠ k : ℕ in atTop, dist ((2 : Q2) ^ k) 0 < δ :=
    ht.eventually (Metric.ball_mem_nhds 0 hδ)
  obtain ⟨k, hk⟩ := hevent.exists
  have hk' : ‖(2 : Q2) ^ k‖ < δ := by simpa only [dist_zero_right] using hk
  let d : SL(2, Q2) := BBEKDynamics.diagonal ((2 : Q2) ^ k)
    (pow_ne_zero k (by norm_num))
  refine ⟨d * g, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec w d.val g.val, hg]
  have hv : d.val *ᵥ ![1, (0 : Q2)] = ![(2 : Q2) ^ k, 0] := by
    funext i
    fin_cases i <;>
      simp [d, BBEKDynamics.diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hv, norm_pair_zero]
  exact hk'

def intFirst : Fin 2 → ℤ := ![1, 0]

theorem intFirst_ne_zero : intFirst ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num [intFirst] at hh

theorem cast_intFirst_ne_zero {K : Type*} [Field K] [CharZero K] :
    (fun i => (intFirst i : K)) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num [intFirst] at hh

theorem mulVec_intFirst_ne_zero {K : Type*} [Field K] [CharZero K]
    (M : SL(2, K)) : M.val *ᵥ (fun i => (intFirst i : K)) ≠ 0 := by
  intro h
  apply cast_intFirst_ne_zero (K := K)
  apply M.toLin'.injective
  simpa [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] using h

def scaledFirst (k : ℕ) : Coefficients :=
  fun i => (2 : dyadic) ^ k * (intFirst i : dyadic)

theorem scaledFirst_ne_zero (k : ℕ) : scaledFirst k ≠ 0 := by
  intro h
  have hh := congrFun h 0
  change (2 : dyadic) ^ k * (1 : dyadic) = 0 at hh
  exact (pow_ne_zero k (by norm_num : (2 : dyadic) ≠ 0)) (by simpa using hh)

theorem scaledFirst_vectorImage (M : G) (k : ℕ) :
    vectorImage dyadicToReal dyadicToQ2 M (scaledFirst k) =
      ((2 : ℝ) ^ k • (M.1.val *ᵥ fun i => (intFirst i : ℝ)),
       (2 : Q2) ^ k • (M.2.val *ᵥ fun i => (intFirst i : Q2))) := by
  exact BBEKMahlerBridge.scaled_integer_vectorImage M.1 M.2 intFirst k

theorem padic_scaled_first_tendsto_zero (M : G) :
    Tendsto
      (fun k : ℕ => (2 : Q2) ^ k • (M.2.val *ᵥ fun i => (intFirst i : Q2)))
      atTop (𝓝 0) := by
  have hp : ‖(2 : Q2)‖ < 1 := by
    have he : ‖(2 : Q2)‖ = (2 : ℝ)⁻¹ := padicNormE.norm_p
    rw [he]
    norm_num
  simpa only [zero_smul] using
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).smul_const
      (M.2.val *ᵥ fun i => (intFirst i : Q2))

def halfDyadic : dyadic :=
  ⟨(2 : ℚ)⁻¹, inv_two_mem_dyadic⟩

def inverseScaledFirst (k : ℕ) : Coefficients :=
  fun i => halfDyadic ^ k * (intFirst i : dyadic)

theorem halfDyadic_ne_zero : halfDyadic ≠ 0 := by
  intro h
  have hh := congrArg Subtype.val h
  norm_num [halfDyadic] at hh

theorem inverseScaledFirst_ne_zero (k : ℕ) : inverseScaledFirst k ≠ 0 := by
  intro h
  have hh := congrFun h 0
  change halfDyadic ^ k * (1 : dyadic) = 0 at hh
  exact (pow_ne_zero k halfDyadic_ne_zero) (by simpa using hh)

theorem halfDyadic_real : dyadicToReal halfDyadic = (2 : ℝ)⁻¹ := by
  norm_num [halfDyadic, dyadicToReal_apply]

theorem halfDyadic_padic : dyadicToQ2 halfDyadic = (2 : Q2)⁻¹ := by
  norm_num [halfDyadic, dyadicToQ2_apply]

theorem inverseScaledFirst_vectorImage (M : G) (k : ℕ) :
    vectorImage dyadicToReal dyadicToQ2 M (inverseScaledFirst k) =
      (((2 : ℝ)⁻¹) ^ k • (M.1.val *ᵥ fun i => (intFirst i : ℝ)),
       ((2 : Q2)⁻¹) ^ k • (M.2.val *ᵥ fun i => (intFirst i : Q2))) := by
  apply Prod.ext
  · change M.1.val *ᵥ (fun i => dyadicToReal (halfDyadic ^ k * (intFirst i : dyadic))) = _
    simp only [map_mul, map_pow, map_intCast, halfDyadic_real]
    exact Matrix.mulVec_smul M.1.val (((2 : ℝ)⁻¹) ^ k)
      (fun i => (intFirst i : ℝ))
  · change M.2.val *ᵥ (fun i => dyadicToQ2 (halfDyadic ^ k * (intFirst i : dyadic))) = _
    simp only [map_mul, map_pow, map_intCast, halfDyadic_padic]
    exact Matrix.mulVec_smul M.2.val (((2 : Q2)⁻¹) ^ k)
      (fun i => (intFirst i : Q2))

theorem real_inverse_scaled_first_tendsto_zero (M : G) :
    Tendsto
      (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k • (M.1.val *ᵥ fun i => (intFirst i : ℝ)))
      atTop (𝓝 0) := by
  have hp : ‖(2 : ℝ)⁻¹‖ < 1 := by norm_num [Real.norm_eq_abs]
  simpa only [zero_smul] using
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).smul_const
      (M.1.val *ᵥ fun i => (intFirst i : ℝ))

/-- Every point can be moved out of `K δ` by the real local factor. -/
theorem exists_realFactor_not_mem_K (q : X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : SL(2, ℝ), (g, (1 : SL(2, Q2))) • q ∉ K δ := by
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
      obtain ⟨g, hg⟩ := exists_real_shrink hw hδ
      refine ⟨g, ?_⟩
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

/-- Every point can be moved out of `K δ` by the 2-adic local factor. -/
theorem exists_padicFactor_not_mem_K (q : X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : SL(2, Q2), ((1 : SL(2, ℝ)), g) • q ∉ K δ := by
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
      obtain ⟨g, hg⟩ := exists_padic_shrink hw hδ
      refine ⟨g, ?_⟩
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

/-- A compact set from which every orbit can escape cannot carry an invariant
probability measure of full mass. -/
theorem no_invariant_probability_of_compact_escape
    {H Y : Type*} [Group H] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [BorelSpace Y] [MulAction H Y] [ContinuousConstSMul H Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] [SMulInvariantMeasure H Y μ]
    {C : Set Y} (hC : IsCompact C) (hmass : μ C = 1)
    (hesc : ∀ y ∈ C, ∃ h : H, h • y ∉ C) : False := by
  have hcover : C ⊆ ⋃ h : H, (fun y : Y => h • y) ⁻¹' Cᶜ := by
    intro y hy
    obtain ⟨h, hh⟩ := hesc y hy
    exact mem_iUnion.mpr ⟨h, hh⟩
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover
    (fun h : H => (fun y : Y => h • y) ⁻¹' Cᶜ)
    (fun h => hC.isClosed.isOpen_compl.preimage (continuous_const_smul h)) hcover
  have hcompl : μ Cᶜ = 0 := (prob_compl_eq_zero_iff hC.measurableSet).2 hmass
  have hnull : μ (⋃ h ∈ (T : Set H), (fun y : Y => h • y) ⁻¹' Cᶜ) = 0 :=
    (measure_biUnion_null_iff T.countable_toSet).2
      (fun h _hh => measure_preimage_smul_null hcompl h)
  have hz : μ C = 0 := measure_mono_null hT hnull
  exact zero_ne_one (hz.symm.trans hmass)

/-- The copy of the real local factor in the actual product group. -/
def realFactor : Subgroup G where
  carrier := {g | g.2 = 1}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    change g.2 = 1 at hg
    change h.2 = 1 at hh
    change g.2 * h.2 = 1
    rw [hg, hh, one_mul]
  inv_mem' := by
    intro g hg
    change g.2 = 1 at hg
    change g.2⁻¹ = 1
    rw [hg, inv_one]

/-- The copy of the 2-adic local factor in the actual product group. -/
def padicFactor : Subgroup G where
  carrier := {g | g.1 = 1}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    change g.1 = 1 at hg
    change h.1 = 1 at hh
    change g.1 * h.1 = 1
    rw [hg, hh, one_mul]
  inv_mem' := by
    intro g hg
    change g.1 = 1 at hg
    change g.1⁻¹ = 1
    rw [hg, inv_one]

theorem no_realFactor_invariant_probability_supported_K
    (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure realFactor X μ] {δ : ℝ} (hδ : 0 < δ)
    (hmass : μ (K δ) = 1) : False := by
  apply no_invariant_probability_of_compact_escape (H := realFactor) (Y := X)
    μ (BBEKMahler.compact_K hδ) hmass
  intro q hq
  obtain ⟨g, hg⟩ := exists_realFactor_not_mem_K q hδ
  refine ⟨⟨(g, (1 : SL(2, Q2))), rfl⟩, ?_⟩
  exact hg

theorem no_padicFactor_invariant_probability_supported_K
    (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure padicFactor X μ] {δ : ℝ} (hδ : 0 < δ)
    (hmass : μ (K δ) = 1) : False := by
  apply no_invariant_probability_of_compact_escape (H := padicFactor) (Y := X)
    μ (BBEKMahler.compact_K hδ) hmass
  intro q hq
  obtain ⟨g, hg⟩ := exists_padicFactor_not_mem_K q hδ
  refine ⟨⟨((1 : SL(2, ℝ)), g), rfl⟩, ?_⟩
  exact hg

/-- The contradiction is inherited from any larger subgroup containing the
real local factor. -/
theorem no_subgroup_invariant_probability_supported_K_of_realFactor
    (H : Subgroup G) (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure H X μ] (hH : realFactor ≤ H)
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1) : False := by
  letI : SMulInvariantMeasure realFactor X μ := ⟨fun h s hs =>
      SMulInvariantMeasure.measure_preimage_smul
        (⟨h.val, hH h.property⟩ : H) hs⟩
  exact no_realFactor_invariant_probability_supported_K μ hδ hmass

/-- The corresponding contradiction for any subgroup containing the 2-adic
local factor. -/
theorem no_subgroup_invariant_probability_supported_K_of_padicFactor
    (H : Subgroup G) (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure H X μ] (hH : padicFactor ≤ H)
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (K δ) = 1) : False := by
  letI : SMulInvariantMeasure padicFactor X μ := ⟨fun h s hs =>
      SMulInvariantMeasure.measure_preimage_smul
        (⟨h.val, hH h.property⟩ : H) hs⟩
  exact no_padicFactor_invariant_probability_supported_K μ hδ hmass

end VV.BBEKFactorEscape
