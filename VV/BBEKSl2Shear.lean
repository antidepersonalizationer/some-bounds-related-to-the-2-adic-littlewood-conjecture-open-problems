import VV.BBEKDynamics
import VV.BBEKFiniteQuotients

/-!
# The explicit rank-one shearing polynomial

The low-entropy argument used by BBEK ultimately specializes to the elementary
quadratic divergence of two nearby `SL₂` points under a unipotent leaf.  This
file records that algebraic input for an arbitrary field.  In particular, it
does not package a measure-rigidity conclusion as an assumption.
-/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace VV.BBEKSl2Shear

open BBEKFiniteQuotients

variable {F : Type*} [Field F]

/-- Conjugation by the lower root, in the orientation used for leafwise
shearing. -/
def lowerShear (u : F) (g : SL(2, F)) : SL(2, F) :=
  lower u * g * lower (-u)

@[simp] theorem lowerShear_zero (g : SL(2, F)) : lowerShear 0 g = g := by
  simp [lowerShear]

@[simp] theorem lowerShear_00 (u : F) (g : SL(2, F)) :
    lowerShear u g 0 0 = g 0 0 - g 0 1 * u := by
  simp [lowerShear, lower, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

@[simp] theorem lowerShear_01 (u : F) (g : SL(2, F)) :
    lowerShear u g 0 1 = g 0 1 := by
  simp [lowerShear, lower, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

@[simp] theorem lowerShear_10 (u : F) (g : SL(2, F)) :
    lowerShear u g 1 0 =
      g 1 0 + (g 0 0 - g 1 1) * u - g 0 1 * u ^ 2 := by
  simp [lowerShear, lower, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

@[simp] theorem lowerShear_11 (u : F) (g : SL(2, F)) :
    lowerShear u g 1 1 = g 1 1 + g 0 1 * u := by
  simp [lowerShear, lower, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

/-- The lower-left displacement splits into its linear and quadratic
coefficients.  The quadratic coefficient is precisely the opposite-root
coordinate. -/
theorem lowerShear_10_sub (u : F) (g : SL(2, F)) :
    lowerShear u g 1 0 - g 1 0 =
      (g 0 0 - g 1 1) * u - g 0 1 * u ^ 2 := by
  rw [lowerShear_10]
  ring

/-- A matrix commutes with every element of the lower root exactly when its
opposite-root entry vanishes and its two diagonal entries agree. -/
theorem commutes_lower_iff (g : SL(2, F)) :
    (∀ u : F, lower u * g = g * lower u) ↔
      g 0 1 = 0 ∧ g 0 0 = g 1 1 := by
  constructor
  · intro h
    have h1 := h 1
    have h01 := congrArg (fun m : SL(2, F) => m 0 0) h1
    have h10 := congrArg (fun m : SL(2, F) => m 1 0) h1
    simp [lower, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h01 h10
    exact ⟨h01, by linear_combination h10⟩
  · rintro ⟨hb, hd⟩ u
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [lower, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb, hd] <;> ring

/-- The same centralizer criterion can be read from the shearing polynomial:
all lower conjugates are constant precisely in the centralizer case. -/
theorem lowerShear_eq_self_iff (g : SL(2, F)) :
    (∀ u : F, lowerShear u g = g) ↔
      g 0 1 = 0 ∧ g 0 0 = g 1 1 := by
  constructor
  · intro h
    have h1 := h 1
    have h00 := congrArg (fun m : SL(2, F) => m 0 0) h1
    have h10 := congrArg (fun m : SL(2, F) => m 1 0) h1
    simp only [lowerShear_00, lowerShear_10, one_pow, mul_one] at h00 h10
    have hb : g 0 1 = 0 := by
      calc
        g 0 1 = g 0 0 - (g 0 0 - g 0 1) := by ring
        _ = 0 := by rw [h00]; ring
    rw [hb] at h10
    have had : g 0 0 - g 1 1 = 0 := by
      calc
        g 0 0 - g 1 1 =
            (g 1 0 + (g 0 0 - g 1 1) - 0) - g 1 0 := by ring
        _ = 0 := by rw [h10]; ring
    exact ⟨hb, sub_eq_zero.mp had⟩
  · rintro ⟨hb, hd⟩ u
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hd] <;> ring

/-- Conjugation by the upper root. -/
def upperShear (u : F) (g : SL(2, F)) : SL(2, F) :=
  upper u * g * upper (-u)

@[simp] theorem upperShear_zero (g : SL(2, F)) : upperShear 0 g = g := by
  simp [upperShear]

@[simp] theorem upperShear_00 (u : F) (g : SL(2, F)) :
    upperShear u g 0 0 = g 0 0 + g 1 0 * u := by
  simp [upperShear, upper, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

@[simp] theorem upperShear_10 (u : F) (g : SL(2, F)) :
    upperShear u g 1 0 = g 1 0 := by
  simp [upperShear, upper, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

@[simp] theorem upperShear_01 (u : F) (g : SL(2, F)) :
    upperShear u g 0 1 =
      g 0 1 + (g 1 1 - g 0 0) * u - g 1 0 * u ^ 2 := by
  simp [upperShear, upper, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

@[simp] theorem upperShear_11 (u : F) (g : SL(2, F)) :
    upperShear u g 1 1 = g 1 1 - g 1 0 * u := by
  simp [upperShear, upper, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

theorem upperShear_01_sub (u : F) (g : SL(2, F)) :
    upperShear u g 0 1 - g 0 1 =
      (g 1 1 - g 0 0) * u - g 1 0 * u ^ 2 := by
  rw [upperShear_01]
  ring

theorem commutes_upper_iff (g : SL(2, F)) :
    (∀ u : F, upper u * g = g * upper u) ↔
      g 1 0 = 0 ∧ g 0 0 = g 1 1 := by
  constructor
  · intro h
    have h1 := h 1
    have h00 := congrArg (fun m : SL(2, F) => m 0 0) h1
    have h01 := congrArg (fun m : SL(2, F) => m 0 1) h1
    simp [upper, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h00 h01
    have had : g 0 0 - g 1 1 = 0 := by
      calc
        g 0 0 - g 1 1 =
            (g 0 0 + g 0 1) - (g 0 1 + g 1 1) := by ring
        _ = 0 := by rw [← h01]; ring
    exact ⟨h00, sub_eq_zero.mp had⟩
  · rintro ⟨hc, hd⟩ u
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [upper, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hc, hd] <;> ring

end VV.BBEKSl2Shear
