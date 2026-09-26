import VV.BBEKLeafEntropySubordinate

/-! The actual mixed inverse time contracts all lower-root parameters at rate 4⁻ⁿ. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric Topology
open scoped Topology ENNReal
namespace VV.BBEKLeafEntropySubordinateTime
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKUniformPlaques BBEKPlaqueSelection
  BBEKLeafEntropyBoundary BBEKLeafEntropySafety BBEKLeafEntropySafetyCuts
  BBEKLeafEntropySubordinate BBEKRootLeafKernel
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def inverseTime (q : X) : X := (psi time0 1)⁻¹ • q
def contractReal (n : ℕ) (u : ℝ) : ℝ := (Real.exp (-2*time0))^n*u
def contractPadic (n : ℕ) (u : Q2) : Q2 := (((2:Q2)^2)^n)*u
def contractJoint (n : ℕ) (u : Leaf) : Leaf := (contractReal n u.1,contractPadic n u.2)

theorem inverseTime_iterate (n : ℕ) (q : X) :
    (inverseTime^[n]) q = ((psi time0 1)⁻¹)^n • q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (psi time0 1)⁻¹ • ((inverseTime^[n]) q) = _
    rw [ih,← mul_smul,← pow_succ']

theorem real_factor_le_quarter : Real.exp (-2*time0) ≤ (1/4:ℝ) := by
  calc
    Real.exp (-2*time0) ≤ Real.exp (-(Real.log 2+Real.log 2)) :=
      Real.exp_le_exp.mpr (by unfold time0; linarith)
    _ = 1/4 := by rw [Real.exp_neg,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num

theorem norm_contractReal_le (n : ℕ) (u : ℝ) :
    ‖contractReal n u‖ ≤ (1/4:ℝ)^n*‖u‖ := by
  unfold contractReal
  rw [norm_mul,norm_pow,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Real.exp_pos _).le real_factor_le_quarter n) (norm_nonneg u)

theorem norm_contractPadic (n : ℕ) (u : Q2) :
    ‖contractPadic n u‖ = (1/4:ℝ)^n*‖u‖ := by
  unfold contractPadic
  rw [norm_mul,norm_pow,norm_pow,
    show ‖(2:Q2)‖ = (2:ℝ)⁻¹ from padicNormE.norm_p]
  norm_num

theorem norm_contractJoint_le (n : ℕ) (u : Leaf) :
    ‖contractJoint n u‖ ≤ (1/4:ℝ)^n*‖u‖ := by
  rw [contractJoint,Prod.norm_def,Prod.norm_def]
  apply max_le
  · exact (norm_contractReal_le n u.1).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
  · rw [norm_contractPadic]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

theorem inverseTime_conjugates_root (n : ℕ) (u : Leaf) (q : X) :
    (inverseTime^[n]) (x u.1 u.2 • q) =
      x (contractJoint n u).1 (contractJoint n u).2 • (inverseTime^[n]) q := by
  rw [inverseTime_iterate,inverseTime_iterate,← mul_smul,← mul_smul]
  congr 1
  calc
    ((psi time0 1)⁻¹)^n*x u.1 u.2 =
      (((psi time0 1)⁻¹)^n*x u.1 u.2*(psi time0 1)^n)*((psi time0 1)⁻¹)^n := by group
    _ = _ := by rw [psi_inverse_iterate_conjugate]; rfl

theorem inverseTime_conjugates_real (n : ℕ) (u : ℝ) (q : X) :
    (inverseTime^[n]) (x u 0 • q) = x (contractReal n u) 0 • (inverseTime^[n]) q := by
  simpa only [contractJoint,contractPadic,mul_zero] using
    inverseTime_conjugates_root n (u,0) q

theorem inverseTime_conjugates_padic (n : ℕ) (u : Q2) (q : X) :
    (inverseTime^[n]) (x 0 u • q) = x 0 (contractPadic n u) • (inverseTime^[n]) q := by
  simpa only [contractJoint,contractReal,mul_zero] using
    inverseTime_conjugates_root n (0,u) q

end VV.BBEKLeafEntropySubordinateTime
