import VV.BBEKLeafwiseKernel

/-! Actual one-root conditional kernels. The real and 2-adic lower root groups
are disintegrated separately; the unused factor is part of the transverse coordinate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKRootLeafKernel
open BBEKDynamics BBEKGaussChart BBEKLeafwiseKernel
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev RealTransverse := ({a : ℝ // a ≠ 0} × ℝ) × Params Q2
abbrev PadicTransverse := Params ℝ × ({a : Q2 // a ≠ 0} × Q2)

def realSplit : GroupParams ≃ₜ RealTransverse × ℝ where
  toFun p := ((p.1.2,p.2),p.1.1)
  invFun q := ((q.2,q.1.1),q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def padicSplit : GroupParams ≃ₜ PadicTransverse × Q2 where
  toFun p := ((p.1,p.2.2),p.2.1)
  invFun q := (q.1.1,(q.2,q.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def realLeafScaling (t : ℝ) : ℝ ≃ₜ ℝ :=
  Homeomorph.smulOfNeZero (Real.exp (2*t)) (Real.exp_ne_zero _)
def padicLeafScaling (n : ℤ) : Q2 ≃ₜ Q2 :=
  Homeomorph.smulOfNeZero ((2 : Q2)^(-2*n)) (zpow_ne_zero _ (by norm_num))
def realUpperScaling (t : ℝ) : ℝ ≃ₜ ℝ :=
  Homeomorph.smulOfNeZero (Real.exp (-2*t)) (Real.exp_ne_zero _)
def padicUpperScaling (n : ℤ) : Q2 ≃ₜ Q2 :=
  Homeomorph.smulOfNeZero ((2 : Q2)^(2*n)) (zpow_ne_zero _ (by norm_num))

def realParamsScaling (t : ℝ) : Params ℝ ≃ₜ Params ℝ :=
  (realLeafScaling t).prodCongr ((Homeomorph.refl _).prodCongr (realUpperScaling t))
def padicParamsScaling (n : ℤ) : Params Q2 ≃ₜ Params Q2 :=
  (padicLeafScaling n).prodCongr ((Homeomorph.refl _).prodCongr (padicUpperScaling n))

def realTransverseScaling (t : ℝ) (n : ℤ) : RealTransverse ≃ₜ RealTransverse :=
  ((Homeomorph.refl _).prodCongr (realUpperScaling t)).prodCongr (padicParamsScaling n)
def padicTransverseScaling (t : ℝ) (n : ℤ) : PadicTransverse ≃ₜ PadicTransverse :=
  (realParamsScaling t).prodCongr ((Homeomorph.refl _).prodCongr (padicUpperScaling n))

theorem realSplit_psiParams (t : ℝ) (n : ℤ) (p : GroupParams) :
    realSplit (psiParams t n p) =
      Prod.map (realTransverseScaling t n) (realLeafScaling t) (realSplit p) := rfl
theorem padicSplit_psiParams (t : ℝ) (n : ℤ) (p : GroupParams) :
    padicSplit (psiParams t n p) =
      Prod.map (padicTransverseScaling t n) (padicLeafScaling n) (padicSplit p) := rfl

def realCoordinateMeasure (μ : Measure GroupParams) : Measure (RealTransverse × ℝ) :=
  μ.map realSplit
def padicCoordinateMeasure (μ : Measure GroupParams) : Measure (PadicTransverse × Q2) :=
  μ.map padicSplit

instance realCoordinateMeasure_finite (μ : Measure GroupParams) [IsFiniteMeasure μ] :
    IsFiniteMeasure (realCoordinateMeasure μ) := by unfold realCoordinateMeasure; infer_instance
instance padicCoordinateMeasure_finite (μ : Measure GroupParams) [IsFiniteMeasure μ] :
    IsFiniteMeasure (padicCoordinateMeasure μ) := by unfold padicCoordinateMeasure; infer_instance

def realLeafKernel (μ : Measure GroupParams) [IsFiniteMeasure μ] : Kernel RealTransverse ℝ :=
  (realCoordinateMeasure μ).condKernel
def padicLeafKernel (μ : Measure GroupParams) [IsFiniteMeasure μ] : Kernel PadicTransverse Q2 :=
  (padicCoordinateMeasure μ).condKernel

theorem realCoordinateMeasure_scaling (μ : Measure GroupParams) (t : ℝ) (n : ℤ) :
    realCoordinateMeasure (μ.map (psiParams t n)) =
      (realCoordinateMeasure μ).map (Prod.map (realTransverseScaling t n) (realLeafScaling t)) := by
  unfold realCoordinateMeasure
  rw [Measure.map_map realSplit.measurable (measurable_psiParams t n),
    Measure.map_map ((realTransverseScaling t n).measurable.prodMap (realLeafScaling t).measurable)
      realSplit.measurable]
  rfl

theorem padicCoordinateMeasure_scaling (μ : Measure GroupParams) (t : ℝ) (n : ℤ) :
    padicCoordinateMeasure (μ.map (psiParams t n)) =
      (padicCoordinateMeasure μ).map (Prod.map (padicTransverseScaling t n) (padicLeafScaling n)) := by
  unfold padicCoordinateMeasure
  rw [Measure.map_map padicSplit.measurable (measurable_psiParams t n),
    Measure.map_map ((padicTransverseScaling t n).measurable.prodMap (padicLeafScaling n).measurable)
      padicSplit.measurable]
  rfl

theorem realLeafKernel_diagonal_covariance (μ : Measure GroupParams) [IsFiniteMeasure μ]
    (t : ℝ) (n : ℤ) :
    ∀ᵐ b ∂(realCoordinateMeasure μ).fst,
      realLeafKernel (μ.map (psiParams t n)) (realTransverseScaling t n b) =
        (realLeafKernel μ b).map (realLeafScaling t) := by
  unfold realLeafKernel
  rw [condKernel_congr (realCoordinateMeasure_scaling μ t n)]
  exact condKernel_map_prod (realCoordinateMeasure μ)
    (realTransverseScaling t n).toMeasurableEquiv (realLeafScaling t).measurable

theorem padicLeafKernel_diagonal_covariance (μ : Measure GroupParams) [IsFiniteMeasure μ]
    (t : ℝ) (n : ℤ) :
    ∀ᵐ b ∂(padicCoordinateMeasure μ).fst,
      padicLeafKernel (μ.map (psiParams t n)) (padicTransverseScaling t n b) =
        (padicLeafKernel μ b).map (padicLeafScaling n) := by
  unfold padicLeafKernel
  rw [condKernel_congr (padicCoordinateMeasure_scaling μ t n)]
  exact condKernel_map_prod (padicCoordinateMeasure μ)
    (padicTransverseScaling t n).toMeasurableEquiv (padicLeafScaling n).measurable

/-- Fibers are the actual real one-parameter lower-unipotent orbits. -/
theorem realMatrix_leaf_add (b : RealTransverse) (u v : ℝ) :
    groupMatrixOf (realSplit.symm (b,v+u)) =
      x v 0 * groupMatrixOf (realSplit.symm (b,u)) := by
  apply Prod.ext
  · change lower (v+u) * _ * _ = lower v * (lower u * _ * _)
    rw [lower_add]
    simp only [mul_assoc]
    rfl
  · change matrixOf b.2 = lower 0 * matrixOf b.2
    rw [lower_zero,one_mul]

/-- Fibers are the actual 2-adic one-parameter lower-unipotent orbits. -/
theorem padicMatrix_leaf_add (b : PadicTransverse) (u v : Q2) :
    groupMatrixOf (padicSplit.symm (b,v+u)) =
      x 0 v * groupMatrixOf (padicSplit.symm (b,u)) := by
  apply Prod.ext
  · change matrixOf b.1 = lower 0 * matrixOf b.1
    rw [lower_zero,one_mul]
  · change lower (v+u) * _ * _ = lower v * (lower u * _ * _)
    rw [lower_add]
    simp only [mul_assoc]
    rfl

end VV.BBEKRootLeafKernel
