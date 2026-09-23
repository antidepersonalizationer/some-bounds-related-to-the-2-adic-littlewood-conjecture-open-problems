import VV.BBEKParameter
import Mathlib.NumberTheory.Padics.RingHoms

/-! The actual 2-adic normalization needed for S-arithmetic Mahler compactness.
The arithmetic ring and matrix groups here are the ones in `BBEKQuotient`.
No compactness or approximation hypothesis is introduced. -/

noncomputable section
open Matrix
open scoped MatrixGroups Topology

namespace VV.BBEKMahlerPadic
open BBEKDynamics BBEKQuotient BBEKDyadic
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem exists_dyadic_close (x : Q2) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : dyadic, ‖x - dyadicToQ2 q‖ < ε := by
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt 2
    (show 0 < (‖x‖ + 1)⁻¹ by positivity)
  have hp : 0 < ‖(2 : Q2)^k‖ := norm_pos_iff.mpr (pow_ne_zero _ (by norm_num))
  have hsmall : ‖(2 : Q2)^k * x‖ ≤ 1 := by
    rw [norm_mul, show ‖(2 : Q2)^k‖ = (2 : ℝ)^(-(k : ℤ)) from padicNormE.norm_p_pow (p:=2) k]
    have hx : 0 < ‖x‖ + 1 := by positivity
    have ht := (mul_lt_mul_of_pos_right hk hx)
    rw [inv_mul_cancel₀ hx.ne'] at ht
    norm_num only [Nat.cast_ofNat] at ht
    nlinarith [norm_nonneg x, zpow_pos (show (0:ℝ)<2 by norm_num) (-(k:ℤ))]
  let z : ℤ_[2] := ⟨(2 : Q2)^k * x, hsmall⟩
  obtain ⟨m, hm⟩ := PadicInt.denseRange_intCast.exists_dist_lt z (mul_pos hε hp)
  refine ⟨⟨(m : ℚ)/2^k, m, k, rfl⟩, ?_⟩
  have he : x - ((m : ℚ)/2^k : ℚ) =
      ((2 : Q2)^k*x - (m : Q2))/(2 : Q2)^k := by
    push_cast
    field_simp; ring
  rw [dyadicToQ2_apply, he, norm_div, div_lt_iff₀ hp]
  simpa only [dist_eq_norm, PadicInt.norm_def, PadicInt.coe_sub,
    PadicInt.coe_intCast, z] using hm

theorem dyadicToQ2_dense : DenseRange dyadicToQ2 := by
  intro x
  rw [Metric.mem_closure_range_iff]
  intro ε hε
  simpa only [dist_eq_norm] using exists_dyadic_close x hε

def upper {K : Type*} [CommRing K] (u : K) : SL(2,K) :=
  ⟨!![1,u;0,1], by simp [Matrix.det_fin_two]⟩

theorem continuous_upper {K : Type*} [CommRing K] [TopologicalSpace K] :
    Continuous (upper : K → SL(2,K)) := by
  unfold upper
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

@[simp] theorem map_lower {R K : Type*} [CommRing R] [CommRing K]
    (f : R →+* K) (u : R) :
    Matrix.SpecialLinearGroup.map f (lower u) = lower (f u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower, Matrix.SpecialLinearGroup.map]

@[simp] theorem map_upper {R K : Type*} [CommRing R] [CommRing K]
    (f : R →+* K) (u : R) :
    Matrix.SpecialLinearGroup.map f (upper u) = upper (f u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, Matrix.SpecialLinearGroup.map]

/-- Four elementary matrices give every nonzero diagonal element. -/
theorem diagonal_unipotent_factorization {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    diagonal a ha = upper (a-1) * lower 1 * upper (a⁻¹-1) * lower (-a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BBEKDynamics.diagonal, upper, lower, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem gaussian_factorization {K : Type*} [Field K] (M : SL(2,K))
    (ha : M 0 0 ≠ 0) :
    M = lower (M 1 0 / M 0 0) * diagonal (M 0 0) ha * upper (M 0 1 / M 0 0) := by
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by simpa only [Matrix.det_fin_two] using M.property
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BBEKDynamics.diagonal, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · field_simp
  · field_simp
    linear_combination hd

/-- Elementary upper and lower matrices generate the actual two-dimensional group. -/
theorem sl2_eq_top_of_unipotents {K : Type*} [Field K] (H : Subgroup SL(2,K))
    (hupper : ∀ u, upper u ∈ H) (hlower : ∀ u, lower u ∈ H) : H = ⊤ := by
  have hdiag (a : K) (ha : a ≠ 0) : diagonal a ha ∈ H := by
    rw [diagonal_unipotent_factorization]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hupper _) (hlower _)) (hupper _)) (hlower _)
  have hcase (M : SL(2,K)) (ha : M 0 0 ≠ 0) : M ∈ H := by
    rw [gaussian_factorization M ha]
    exact H.mul_mem (H.mul_mem (hlower _) (hdiag _ ha)) (hupper _)
  apply top_unique
  intro M _
  by_cases ha : M 0 0 = 0
  · have hc : M 1 0 ≠ 0 := by
      intro hc
      have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by simpa only [Matrix.det_fin_two] using M.property
      simp [ha,hc] at hd
    have hn : (upper (1 : K) * M) 0 0 ≠ 0 := by
      simpa [upper, Matrix.mul_apply, Fin.sum_univ_two, ha] using hc
    exact (H.mul_mem_cancel_left (hupper 1)).mp (hcase _ hn)
  · exact hcase M ha

theorem dyadicSL2_dense :
    DenseRange (Matrix.SpecialLinearGroup.map dyadicToQ2 (n:=Fin 2)) := by
  let H := (Matrix.SpecialLinearGroup.map dyadicToQ2 (n:=Fin 2)).range
  have heq : H.topologicalClosure = ⊤ := by
    apply sl2_eq_top_of_unipotents
    · intro u
      refine dyadicToQ2_dense.induction_on (p := fun u => upper u ∈ H.topologicalClosure) u ?_ ?_
      · exact H.isClosed_topologicalClosure.preimage continuous_upper
      · intro a
        exact H.le_topologicalClosure ⟨upper a, map_upper _ _⟩
    · intro u
      refine dyadicToQ2_dense.induction_on (p := fun u => lower u ∈ H.topologicalClosure) u ?_ ?_
      · exact H.isClosed_topologicalClosure.preimage continuous_lower
      · intro a
        exact H.le_topologicalClosure ⟨lower a, map_lower _ _⟩
  intro M
  change M ∈ H.topologicalClosure
  rw [heq]
  trivial

/-- The literal compact integral subgroup, described by its four entries. -/
def padicIntegral : Set SL(2,Q2) := {M | ∀ i j, ‖M i j‖ ≤ 1}

theorem padicIntegral_mul {A B : SL(2,Q2)} (hA : A ∈ padicIntegral)
    (hB : B ∈ padicIntegral) : A*B ∈ padicIntegral := by
  intro i j
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  apply (padicNormE.nonarchimedean _ _).trans
  apply max_le
  · rw [norm_mul]
    exact mul_le_one₀ (hA i 0) (norm_nonneg _) (hB 0 j)
  · rw [norm_mul]
    exact mul_le_one₀ (hA i 1) (norm_nonneg _) (hB 1 j)

theorem padicIntegral_map_int (A : SL(2,ℤ)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom Q2) A ∈ padicIntegral := by
  intro i j
  exact padicNormE.norm_int_le_one (p:=2) (A i j)

theorem padicIntegral_mulVec_int {P : SL(2,Q2)} (hP : P ∈ padicIntegral)
    (v : Fin 2 → ℤ) : ‖P.val *ᵥ (fun i => (v i : Q2))‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  apply (padicNormE.nonarchimedean _ _).trans
  apply max_le
  · rw [norm_mul]
    exact mul_le_one₀ (hP i 0) (norm_nonneg _) (padicNormE.norm_int_le_one (p:=2) _)
  · rw [norm_mul]
    exact mul_le_one₀ (hP i 1) (norm_nonneg _) (padicNormE.norm_int_le_one (p:=2) _)

theorem padicIntegral_compact : IsCompact padicIntegral := by
  have hc : IsCompact {M : Matrix (Fin 2) (Fin 2) Q2 | ∀ i j, ‖M i j‖ ≤ 1} := by
    have hball : IsCompact {a : Q2 | ‖a‖ ≤ 1} := by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : Q2) 1
    exact isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hball
  have hd : IsClosed {M : Matrix (Fin 2) (Fin 2) Q2 | M.det = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  exact hd.isClosedEmbedding_subtypeVal.isCompact_preimage hc

/-- Right multiplication by an actual dyadic determinant-one matrix makes
all four 2-adic entries integral. -/
theorem exists_padic_normalization (B : SL(2,Q2)) :
    ∃ A : SL(2,dyadic), B * Matrix.SpecialLinearGroup.map dyadicToQ2 A ∈ padicIntegral := by
  let U : Set SL(2,Q2) := {M | ∀ i j,
    ‖(B*M) i j - (1 : Matrix (Fin 2) (Fin 2) Q2) i j‖ < 1}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_lt _ continuous_const
    fun_prop
  have hne : U.Nonempty := by
    refine ⟨B⁻¹, ?_⟩
    intro i j
    simp
  obtain ⟨A, hA⟩ := dyadicSL2_dense.exists_mem_open hU hne
  refine ⟨A, ?_⟩
  intro i j
  have hunit : ‖(1 : Matrix (Fin 2) (Fin 2) Q2) i j‖ ≤ 1 := by
    fin_cases i <;> fin_cases j <;> norm_num
  calc
    ‖(B * Matrix.SpecialLinearGroup.map dyadicToQ2 A) i j‖ =
        ‖((B * Matrix.SpecialLinearGroup.map dyadicToQ2 A) i j -
          (1 : Matrix (Fin 2) (Fin 2) Q2) i j) +
          (1 : Matrix (Fin 2) (Fin 2) Q2) i j‖ := by congr 1; ring
    _ ≤ max ‖(B * Matrix.SpecialLinearGroup.map dyadicToQ2 A) i j -
          (1 : Matrix (Fin 2) (Fin 2) Q2) i j‖
          ‖(1 : Matrix (Fin 2) (Fin 2) Q2) i j‖ := padicNormE.nonarchimedean _ _
    _ ≤ 1 := max_le (hA i j).le hunit

theorem quotient_has_padic_integral_representative (z : X) :
    ∃ R : SL(2,ℝ), ∃ P : SL(2,Q2), P ∈ padicIntegral ∧ mk (R,P) = z := by
  induction z using Quotient.inductionOn with | _ M =>
  obtain ⟨A,hA⟩ := exists_padic_normalization M.2
  exact ⟨(M*diagonalEmbedding A).1, (M*diagonalEmbedding A).2, hA,
    mk_right_gamma M A⟩

end VV.BBEKMahlerPadic


