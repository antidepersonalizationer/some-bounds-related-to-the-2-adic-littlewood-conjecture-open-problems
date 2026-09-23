import VV.BBEKOrbit

/-! Explicit arbitrarily short nonzero arithmetic lattice vectors.
This proves properness of K_delta. It does not assert Mahler compactness. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace VV.BBEKNoncompact
open BBEKDynamics BBEKQuotient BBEKLattice BBEKOrbit

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A sequence of concrete determinant-one diagonal pairs. -/
def shrinkingDiagonal (n : ℕ) : G :=
  (BBEKDynamics.diagonal ((1 / 2 : ℝ) ^ n) (by positivity),
    BBEKDynamics.diagonal ((2 : Q2) ^ n) (pow_ne_zero n (by norm_num)))

def firstCoefficient : Coefficients := ![1,0]

theorem firstCoefficient_ne_zero : firstCoefficient ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simpa [firstCoefficient] using hh

theorem shrinkingDiagonal_vector (n : ℕ) :
    vectorImage dyadicToReal dyadicToQ2 (shrinkingDiagonal n) firstCoefficient =
      (![(1 / 2 : ℝ) ^ n,0], ![(2 : Q2) ^ n,0]) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [vectorImage,shrinkingDiagonal,BBEKDynamics.diagonal,firstCoefficient,
      Matrix.mulVec,dotProduct,Fin.sum_univ_two,Function.comp_def]

private theorem norm_pair_zero {E : Type*} [SeminormedAddCommGroup E] (a : E) :
    ‖![a,0]‖ = ‖a‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
    intro i
    fin_cases i <;> simp
  · simpa using norm_le_pi_norm (![a,0]) 0

theorem shrinkingDiagonal_vector_norm (n : ℕ) :
    ‖vectorImage dyadicToReal dyadicToQ2 (shrinkingDiagonal n) firstCoefficient‖ =
      (1 / 2 : ℝ) ^ n := by
  rw [shrinkingDiagonal_vector, Prod.norm_def, norm_pair_zero, norm_pair_zero]
  have hp : ‖(2 : Q2) ^ n‖ = (1 / 2 : ℝ) ^ n := by
    simpa [zpow_neg, inv_pow] using padicNormE.norm_p_zpow (p := 2) (n : ℤ)
  rw [hp, Real.norm_eq_abs, abs_of_pos (by positivity), max_self]

/-- For every positive cutoff there is an actual quotient point containing
a nonzero vector shorter than the cutoff. -/
theorem exists_not_mem_K {δ : ℝ} (hδ : 0 < δ) : ∃ q : X, q ∉ K δ := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨mk (shrinkingDiagonal n), ?_⟩
  intro hK
  have hlarge := (mem_K_mk_iff δ (shrinkingDiagonal n)).mp hK
    firstCoefficient firstCoefficient_ne_zero
  rw [shrinkingDiagonal_vector_norm] at hlarge
  exact (not_le_of_gt hn) hlarge

theorem K_ne_univ {δ : ℝ} (hδ : 0 < δ) : K δ ≠ Set.univ := by
  obtain ⟨q,hq⟩ := exists_not_mem_K hδ
  intro h
  exact hq (h ▸ Set.mem_univ q)

theorem K_ssubset_univ {δ : ℝ} (hδ : 0 < δ) : K δ ⊂ Set.univ :=
  Set.ssubset_univ_iff.mpr (K_ne_univ hδ)

end VV.BBEKNoncompact
