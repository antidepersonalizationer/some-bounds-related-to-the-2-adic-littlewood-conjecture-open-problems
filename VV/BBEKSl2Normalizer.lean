import VV.BBEKGaussChart
import VV.BBEKSl2Reductive

/-! The exact two components of the normalizer of the split diagonal line.
This is a matrix statement; it makes no claim that algebraic connectedness
or an algebraic group's Lie algebra has already been constructed. -/
noncomputable section
open Matrix
open scoped Matrix MatrixGroups
namespace VV.BBEKSl2Normalizer

variable {K : Type*} [Field K] [CharZero K]

def hMatrix : Matrix (Fin 2) (Fin 2) K := !![1,0;0,-1]

/-- Intertwining the diagonal infinitesimal generator with a scalar multiple
forces a determinant-one matrix to be diagonal or antidiagonal. -/
theorem diagonal_or_antidiagonal (g : SL(2,K)) (r : K)
    (h : g.val * hMatrix = r • (hMatrix * g.val)) :
    (g 0 1=0 ∧ g 1 0=0) ∨ (g 0 0=0 ∧ g 1 1=0) := by
  have h00 := congrArg (fun m : Matrix (Fin 2) (Fin 2) K => m 0 0) h
  have h01 := congrArg (fun m : Matrix (Fin 2) (Fin 2) K => m 0 1) h
  have h10 := congrArg (fun m : Matrix (Fin 2) (Fin 2) K => m 1 0) h
  have h11 := congrArg (fun m : Matrix (Fin 2) (Fin 2) K => m 1 1) h
  simp [hMatrix,Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two] at h00 h01 h10 h11
  by_cases ha : g 0 0=0
  · right
    have hb : g 0 1 ≠ 0 := by
      intro hb
      have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
      simp [Matrix.det_fin_two,ha,hb] at hd
    have hr : r = -1 := by
      have he : (r+1)*g 0 1=0 := by linear_combination -h01
      exact eq_neg_iff_add_eq_zero.mpr ((mul_eq_zero.mp he).resolve_right hb)
    refine ⟨ha,?_⟩
    rw [hr] at h11
    have he : (2:K)*g 1 1=0 := by linear_combination h11
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  · left
    have hr : r=1 := by
      have he : (r-1)*g 0 0=0 := by linear_combination -h00
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right ha)
    rw [hr] at h01 h10
    constructor
    · have he : (2:K)*g 0 1=0 := by linear_combination -h01
      exact (mul_eq_zero.mp he).resolve_left (by norm_num)
    · have he : (2:K)*g 1 0=0 := by linear_combination h10
      exact (mul_eq_zero.mp he).resolve_left (by norm_num)

/-- Conversely both components normalize the line, with eigenvalue +1 and -1. -/
theorem intertwines_iff (g : SL(2,K)) :
    (∃ r : K, g.val * hMatrix = r • (hMatrix * g.val)) ↔
    (g 0 1=0 ∧ g 1 0=0) ∨ (g 0 0=0 ∧ g 1 1=0) := by
  constructor
  · rintro ⟨r,hr⟩
    exact diagonal_or_antidiagonal g r hr
  · rintro (⟨hb,hc⟩ | ⟨ha,hd⟩)
    · refine ⟨1,?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hMatrix,Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two,hb,hc]
    · refine ⟨-1,?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hMatrix,Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two,ha,hd]

/-- The identity component is distinguished from the Weyl component by the
nonvanishing of its first diagonal entry. -/
theorem diagonal_of_intertwines_of_entry_ne_zero (g : SL(2,K))
    (h : ∃ r : K, g.val*hMatrix=r • (hMatrix*g.val)) (hg : g 0 0 ≠ 0) :
    g ∈ VV.BBEKDiagonal.diagonalGroup K := by
  apply (VV.BBEKGaussChart.mem_diagonalGroup_iff g).mpr
  exact (intertwines_iff g).mp h |>.resolve_right (fun he => hg he.1)

/-- Preservation of a proper reductive trace-zero Lie algebra containing H
puts a group element in the actual two-component diagonal normalizer. -/
theorem normalizer_of_proper_reductive
    (S : LieSubalgebra K (Matrix (Fin 2) (Fin 2) K))
    [LieAlgebra.HasCentralRadical K S]
    (hH : BBEKSl2Reductive.H ∈ S)
    (htrace : S ≤ LieAlgebra.SpecialLinear.sl (Fin 2) K)
    (hproper : S ≠ LieAlgebra.SpecialLinear.sl (Fin 2) K)
    (g : SL(2,K))
    (hpres : ∀ M ∈ S, g.val * M * (g⁻¹).val ∈ S) :
    (g 0 1=0 ∧ g 1 0=0) ∨ (g 0 0=0 ∧ g 1 1=0) := by
  have hp := hpres BBEKSl2Reductive.H hH
  rw [BBEKSl2Reductive.proper_eq_diagonal S hH htrace hproper] at hp
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hp
  apply diagonal_or_antidiagonal g r
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M * g.val) hr.symm
  simpa only [Matrix.mul_assoc,← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.mul_one,
    Matrix.smul_mul] using he

end VV.BBEKSl2Normalizer


