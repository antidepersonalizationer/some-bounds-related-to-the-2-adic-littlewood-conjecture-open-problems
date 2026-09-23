import VV.BBEKMahlerPadic
import VV.BBEKOrbit

/-! From the genuine S-arithmetic no-short-vector condition to a uniform
lower bound for the ordinary real integer lattice after 2-adic normalization. -/

noncomputable section
open Matrix
open scoped MatrixGroups Topology

namespace VV.BBEKMahlerBridge
open BBEKDynamics BBEKQuotient BBEKDyadic BBEKLattice BBEKOrbit BBEKMahlerPadic
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem scaled_integer_vectorImage (R : SL(2,ℝ)) (P : SL(2,Q2))
    (v : Fin 2 → ℤ) (k : ℕ) :
    vectorImage dyadicToReal dyadicToQ2 (R,P)
      (fun i => (2 : dyadic)^k * (v i : dyadic)) =
      ((2:ℝ)^k • (R.val *ᵥ fun i => (v i:ℝ)),
       (2:Q2)^k • (P.val *ᵥ fun i => (v i:Q2))) := by
  apply Prod.ext
  · change R.val *ᵥ (fun i => dyadicToReal ((2:dyadic)^k * (v i:dyadic))) = _
    simp only [map_mul, map_pow, map_intCast, map_ofNat]
    exact Matrix.mulVec_smul R.val ((2:ℝ)^k) (fun i => (v i:ℝ))
  · change P.val *ᵥ (fun i => dyadicToQ2 ((2:dyadic)^k * (v i:dyadic))) = _
    simp only [map_mul, map_pow, map_intCast, map_ofNat]
    exact Matrix.mulVec_smul P.val ((2:Q2)^k) (fun i => (v i:Q2))

/-- The square in the lower bound is essential: the 2-adic component of
an integral vector alone could mask a very short real component. Scaling
by the suitable power of 2 makes both components simultaneously short. -/
theorem real_integer_minimum_of_mem_K {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : SL(2,ℝ)) (P : SL(2,Q2)) (hP : P ∈ padicIntegral)
    (hK : mk (R,P) ∈ K δ) (v : Fin 2 → ℤ) (hv : v ≠ 0) :
    δ^2/2 ≤ ‖R.val *ᵥ (fun i => (v i:ℝ))‖ := by
  by_contra! hshort
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hδ hδ1
    (by norm_num : (0:ℝ)<(2:ℝ)⁻¹) (by norm_num : (2:ℝ)⁻¹<1)
  let k := n+1
  have hnorm : ‖(2:Q2)^k‖ < δ := by
    rw [show ‖(2:Q2)^k‖ = (2:ℝ)^(-(k:ℤ)) from padicNormE.norm_p_pow (p:=2) k]
    simpa only [zpow_neg, zpow_natCast, inv_pow, k] using hn
  have hscale : (2:ℝ)^k * δ ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left hn' (pow_nonneg (by norm_num : (0:ℝ)≤2) n)
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero n (by norm_num))] at hh
    dsimp [k]
    rw [pow_succ]
    nlinarith
  let r : Coefficients := fun i => (2:dyadic)^k * (v i:dyadic)
  have hr : r ≠ 0 := by
    intro he
    apply hv
    funext i
    have h := congrFun he i
    change (2:dyadic)^k * (v i:dyadic) = 0 at h
    have hp : (2:dyadic)^k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hz := (mul_eq_zero.mp h).resolve_left hp
    exact_mod_cast hz
  have hk := (mem_K_mk_iff δ (R,P)).mp hK r hr
  rw [show r = (fun i => (2:dyadic)^k * (v i:dyadic)) from rfl,
    scaled_integer_vectorImage, Prod.norm_def] at hk
  apply not_lt_of_ge hk
  apply max_lt
  · rw [norm_smul, norm_pow, Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    have hp : (0:ℝ)<2^k := pow_pos (by norm_num) _
    have hh := mul_lt_mul_of_pos_left hshort hp
    have hbound : (2:ℝ)^k * (δ^2/2) ≤ δ := by
      nlinarith [mul_le_mul_of_nonneg_right hscale hδ.le]
    exact hh.trans_le hbound
  · rw [norm_smul]
    calc
      ‖(2:Q2)^k‖ * ‖P.val *ᵥ (fun i => (v i:Q2))‖ ≤ ‖(2:Q2)^k‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (padicIntegral_mulVec_int hP v)
      _ < δ := hnorm

end VV.BBEKMahlerBridge
