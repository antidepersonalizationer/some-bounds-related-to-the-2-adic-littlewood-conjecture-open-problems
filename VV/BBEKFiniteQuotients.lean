import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
The algebraic finite-index step in BBEK, Theorem 5.2.

We prove directly that every homomorphism from SL₂ over a characteristic-zero
field to a finite group is trivial. The proof uses divisibility of the upper and
lower unipotent groups and explicit two-by-two elimination. It has no dynamical,
entropy, measure-rigidity, or computational assumptions.
-/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace VV.BBEKFiniteQuotients

variable {K : Type*}

def upper [CommRing K] (u : K) : SL(2, K) :=
  ⟨!![1, u; 0, 1], by simp [Matrix.det_fin_two]⟩

def lower [CommRing K] (u : K) : SL(2, K) :=
  ⟨!![1, 0; u, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem upper_zero [CommRing K] : upper (0 : K) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper]

@[simp] theorem lower_zero [CommRing K] : lower (0 : K) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower]

theorem upper_add [CommRing K] (u v : K) : upper (u + v) = upper u * upper v := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lower_add [CommRing K] (u v : K) : lower (u + v) = lower u * lower v := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upper_pow [CommRing K] (u : K) (n : ℕ) :
    upper u ^ n = upper ((n : K) * u) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← upper_add]; simp [add_mul]

theorem lower_pow [CommRing K] (u : K) (n : ℕ) :
    lower u ^ n = lower ((n : K) * u) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← lower_add]; simp [add_mul]

theorem upper_image_eq_one [Field K] [CharZero K]
    {F : Type*} [Group F] [Finite F] (φ : SL(2, K) →* F) (u : K) :
    φ (upper u) = 1 := by
  letI := Fintype.ofFinite F
  have hn : (Fintype.card F : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hpow : upper (u / (Fintype.card F : K)) ^ Fintype.card F = upper u := by
    rw [upper_pow]
    congr 1
    field_simp
  rw [← hpow, map_pow]
  exact pow_card_eq_one

theorem lower_image_eq_one [Field K] [CharZero K]
    {F : Type*} [Group F] [Finite F] (φ : SL(2, K) →* F) (u : K) :
    φ (lower u) = 1 := by
  letI := Fintype.ofFinite F
  have hn : (Fintype.card F : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hpow : lower (u / (Fintype.card F : K)) ^ Fintype.card F = lower u := by
    rw [lower_pow]
    congr 1
    field_simp
  rw [← hpow, map_pow]
  exact pow_card_eq_one

/-- Explicit generation by three unipotents when the lower-left entry is nonzero. -/
theorem factorization [Field K] (g : SL(2, K)) (hc : g 1 0 ≠ 0) :
    g = upper ((g 0 0 - 1) / g 1 0) * lower (g 1 0) *
      upper ((g 1 1 - 1) / g 1 0) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals linear_combination -hdet

theorem image_eq_one_of_lower_left_ne_zero [Field K] [CharZero K]
    {F : Type*} [Group F] [Finite F] (φ : SL(2, K) →* F)
    (g : SL(2, K)) (hc : g 1 0 ≠ 0) : φ g = 1 := by
  rw [factorization g hc]
  simp only [map_mul, upper_image_eq_one, lower_image_eq_one, one_mul]

/-- Every homomorphism from SL₂ over a characteristic-zero field to a finite
group is trivial. There are no topological assumptions on the homomorphism. -/
theorem sl2_hom_finite_eq_one [Field K] [CharZero K]
    {F : Type*} [Group F] [Finite F] (φ : SL(2, K) →* F) (g : SL(2, K)) :
    φ g = 1 := by
  by_cases hc : g 1 0 = 0
  · have hdet : g 0 0 * g 1 1 = 1 := by
      simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using g.property
    have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hshift : (lower (1 : K) * g : SL(2, K)) 1 0 ≠ 0 := by
      simpa [lower, Matrix.mul_apply, Fin.sum_univ_two, hc] using ha
    have himg := image_eq_one_of_lower_left_ne_zero φ (lower 1 * g) hshift
    simpa only [map_mul, lower_image_eq_one, one_mul] using himg
  · exact image_eq_one_of_lower_left_ne_zero φ g hc

/-- There are no proper finite-index subgroups, including nonnormal ones.
The finite quotient by the normal core handles the nonnormal case. -/
theorem sl2_finiteIndex_eq_top [Field K] [CharZero K]
    (H : Subgroup SL(2, K)) [H.FiniteIndex] : H = ⊤ := by
  apply (Subgroup.eq_top_iff' H).mpr
  intro g
  apply H.normalCore_le
  apply (QuotientGroup.eq_one_iff g).mp
  exact sl2_hom_finite_eq_one (QuotientGroup.mk' H.normalCore) g

/-- The product version applies in particular to SL₂(ℝ) × SL₂(ℚ₂),
the actual group in BBEK Section 5. -/
theorem prod_sl2_hom_finite_eq_one [Field K] [CharZero K]
    {L : Type*} [Field L] [CharZero L]
    {F : Type*} [Group F] [Finite F]
    (φ : (SL(2, K) × SL(2, L)) →* F) (g : SL(2, K) × SL(2, L)) :
    φ g = 1 := by
  have h₁ := sl2_hom_finite_eq_one
    (φ.comp (MonoidHom.inl SL(2, K) SL(2, L))) g.1
  have h₂ := sl2_hom_finite_eq_one
    (φ.comp (MonoidHom.inr SL(2, K) SL(2, L))) g.2
  change φ (g.1, 1) = 1 at h₁
  change φ (1, g.2) = 1 at h₂
  calc
    φ g = φ (g.1, 1) * φ (1, g.2) := by rw [← map_mul]; simp
    _ = 1 := by rw [h₁, h₂, one_mul]

theorem prod_sl2_finiteIndex_eq_top [Field K] [CharZero K]
    {L : Type*} [Field L] [CharZero L]
    (H : Subgroup (SL(2, K) × SL(2, L))) [H.FiniteIndex] : H = ⊤ := by
  apply (Subgroup.eq_top_iff' H).mpr
  intro g
  apply H.normalCore_le
  apply (QuotientGroup.eq_one_iff g).mp
  exact prod_sl2_hom_finite_eq_one (QuotientGroup.mk' H.normalCore) g

end VV.BBEKFiniteQuotients
