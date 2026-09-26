import VV.BBEKShearLimit
import VV.BBEKMeasureStabilizer

/-! The numerical SL₂ shear is the actual displacement of two points of X
under a pure-factor diagonal time and a root translation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology MatrixGroups
namespace VV.BBEKPureRootShear
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKEntropyExpansive BBEKSl2Shear
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

def realDiagonal (a : ℝ) (ha : a ≠ 0) : G := (diagonal a ha,1)
def padicDiagonal (a : Q2) (ha : a ≠ 0) : G := (1,diagonal a ha)

theorem realDiagonal_mem_A (a : ℝ) (ha : a ≠ 0) : realDiagonal a ha ∈ A :=
  ⟨⟨a,ha,rfl⟩,(diagonalGroup Q2).one_mem⟩
theorem padicDiagonal_mem_A (a : Q2) (ha : a ≠ 0) : padicDiagonal a ha ∈ A :=
  ⟨(diagonalGroup ℝ).one_mem,⟨a,ha,rfl⟩⟩

theorem realTime_preserving (μ : Measure X) [SMulInvariantMeasure A X μ]
    (a : ℝ) (ha : a ≠ 0) :
    MeasurePreserving (fun q : X => realDiagonal a ha • q) μ μ :=
  measurePreserving_smul (⟨realDiagonal a ha,realDiagonal_mem_A a ha⟩ : A) μ
theorem padicTime_preserving (μ : Measure X) [SMulInvariantMeasure A X μ]
    (a : Q2) (ha : a ≠ 0) :
    MeasurePreserving (fun q : X => padicDiagonal a ha • q) μ μ :=
  measurePreserving_smul (⟨padicDiagonal a ha,padicDiagonal_mem_A a ha⟩ : A) μ

theorem real_norm_two : ‖(2 : ℝ)‖ = 2 := by norm_num
theorem padic_norm_half : ‖(2 : Q2)⁻¹‖ = 2 := by
  rw [norm_inv,show ‖(2 : Q2)‖ = (2 : ℝ)⁻¹ from padicNormE.norm_p,inv_inv]

theorem realDiagonal_conjugate (a : ℝ) (ha : a ≠ 0) (g : G) (n : ℕ) :
    (realDiagonal a ha)^n * g * ((realDiagonal a ha)^n)⁻¹ =
      (diagConjugate (a^n) (pow_ne_zero n ha) g.1,g.2) := by
  apply Prod.ext
  · change (diagonal a ha)^n * g.1 * ((diagonal a ha)^n)⁻¹ = _
    rw [← inv_pow]
    exact power_diagConjugate a ha g.1 n
  · change (1 : SL(2,Q2))^n * g.2 * ((1 : SL(2,Q2))^n)⁻¹ = _
    simp

theorem padicDiagonal_conjugate (a : Q2) (ha : a ≠ 0) (g : G) (n : ℕ) :
    (padicDiagonal a ha)^n * g * ((padicDiagonal a ha)^n)⁻¹ =
      (g.1,diagConjugate (a^n) (pow_ne_zero n ha) g.2) := by
  apply Prod.ext
  · change (1 : SL(2,ℝ))^n * g.1 * ((1 : SL(2,ℝ))^n)⁻¹ = _
    simp
  · change (diagonal a ha)^n * g.2 * ((diagonal a ha)^n)⁻¹ = _
    rw [← inv_pow]
    exact power_diagConjugate a ha g.2 n

theorem displacement_after_root (d h g : G) (q : X) (n : ℕ) :
    h • (d^n • (g • q)) =
      (h*(d^n*g*(d^n)⁻¹)*h⁻¹) • (h • (d^n • q)) := by
  simp only [← mul_smul]
  congr 1
  group

theorem inv_lower {F : Type*} [Field F] (u : F) :
    (BBEKFiniteQuotients.lower u)⁻¹ = BBEKFiniteQuotients.lower (-u) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← BBEKFiniteQuotients.lower_add, add_neg_cancel, BBEKFiniteQuotients.lower_zero]

theorem real_root_conjugate (u : ℝ) (g : G) :
    x u 0 * g * (x u 0)⁻¹ = (lowerShear u g.1,g.2) := by
  apply Prod.ext
  · change BBEKFiniteQuotients.lower u * g.1 * (BBEKFiniteQuotients.lower u)⁻¹ = _
    rw [inv_lower]
    rfl
  · change BBEKFiniteQuotients.lower (0 : Q2) * g.2 * (BBEKFiniteQuotients.lower (0 : Q2))⁻¹ = _
    simp

theorem padic_root_conjugate (u : Q2) (g : G) :
    x 0 u * g * (x 0 u)⁻¹ = (g.1,lowerShear u g.2) := by
  apply Prod.ext
  · change BBEKFiniteQuotients.lower (0 : ℝ) * g.1 * (BBEKFiniteQuotients.lower (0 : ℝ))⁻¹ = _
    simp
  · change BBEKFiniteQuotients.lower u * g.2 * (BBEKFiniteQuotients.lower u)⁻¹ = _
    rw [inv_lower]
    rfl

/-- A genuine pair y=gx evolves by exactly the polynomial displacement used
by the quantitative shearing theorems, including the unchanged other factor. -/
theorem real_paired_shear_relation (a : ℝ) (ha : a ≠ 0) (u : ℝ)
    (g : G) (q q' : X) (hqq' : q' = g • q) (k : ℕ) :
    x u 0 • ((fun z : X => realDiagonal a ha • z)^[k] q') =
      (lowerShear u (diagConjugate (a^k) (pow_ne_zero k ha) g.1),g.2) •
        (x u 0 • ((fun z : X => realDiagonal a ha • z)^[k] q)) := by
  rw [hqq',smul_iterate_apply,smul_iterate_apply,
    displacement_after_root,realDiagonal_conjugate,real_root_conjugate]

theorem padic_paired_shear_relation (a : Q2) (ha : a ≠ 0) (u : Q2)
    (g : G) (q q' : X) (hqq' : q' = g • q) (k : ℕ) :
    x 0 u • ((fun z : X => padicDiagonal a ha • z)^[k] q') =
      (g.1,lowerShear u (diagConjugate (a^k) (pow_ne_zero k ha) g.2)) •
        (x 0 u • ((fun z : X => padicDiagonal a ha • z)^[k] q)) := by
  rw [hqq',smul_iterate_apply,smul_iterate_apply,
    displacement_after_root,padicDiagonal_conjugate,padic_root_conjugate]

theorem real_displacement_limit (g : ℕ → G) (hg : Tendsto g atTop (𝓝 1))
    (h : ℕ → SL(2,ℝ)) {u : ℝ}
    (hh : Tendsto h atTop (𝓝 (BBEKFiniteQuotients.lower u))) :
    Tendsto (fun n => (h n,(g n).2)) atTop (𝓝 (x u 0)) := by
  have he : x u 0 = (BBEKFiniteQuotients.lower u,(1 : SL(2,Q2))) := by
    apply Prod.ext
    · rfl
    · change BBEKFiniteQuotients.lower 0 = 1
      exact BBEKFiniteQuotients.lower_zero
  rw [he]
  exact hh.prodMk_nhds (continuous_snd.continuousAt.tendsto.comp hg)

theorem padic_displacement_limit (g : ℕ → G) (hg : Tendsto g atTop (𝓝 1))
    (h : ℕ → SL(2,Q2)) {u : Q2}
    (hh : Tendsto h atTop (𝓝 (BBEKFiniteQuotients.lower u))) :
    Tendsto (fun n => ((g n).1,h n)) atTop (𝓝 (x 0 u)) := by
  have he : x 0 u = ((1 : SL(2,ℝ)),BBEKFiniteQuotients.lower u) := by
    apply Prod.ext
    · change BBEKFiniteQuotients.lower 0 = 1
      exact BBEKFiniteQuotients.lower_zero
    · rfl
  rw [he]
  exact (continuous_fst.continuousAt.tendsto.comp hg).prodMk_nhds hh

end VV.BBEKPureRootShear
