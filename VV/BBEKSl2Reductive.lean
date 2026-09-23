import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Matrix LieAlgebra
open scoped Matrix
namespace VV.BBEKSl2Reductive

section StableLine
variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- An invariant line is an abelian ideal. -/
def lineIdeal (z : L) (hz : ∀ x : L, ⁅x,z⁆ ∈ K ∙ z) : LieIdeal K L where
  toSubmodule := K ∙ z
  lie_mem := by
    intro x y hy
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [lie_smul]
    exact Submodule.smul_mem _ c (hz x)

instance lineIdeal_abelian (z : L) (hz : ∀ x : L, ⁅x,z⁆ ∈ K ∙ z) :
    IsLieAbelian (lineIdeal z hz) where
  trivial x y := by
    apply Subtype.ext
    change ⁅x.val,y.val⁆=0
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp x.property
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp y.property
    rw [← ha,← hb,smul_lie,lie_smul,lie_self,smul_zero,smul_zero]

/-- In a reductive Lie algebra every invariant line is central; this uses
mathlib's actual solvable radical, not an assumed matrix classification. -/
theorem invariant_line_central [HasCentralRadical K L]
    (z : L) (hz : ∀ x : L, ⁅x,z⁆ ∈ K ∙ z) (x : L) : ⁅x,z⁆=0 := by
  let I := lineIdeal z hz
  have hsolv : IsSolvable I := inferInstance
  have hle : I ≤ radical K L := le_sSup hsolv
  have hmem : z ∈ radical K L := hle (Submodule.mem_span_singleton_self z)
  rw [radical_eq_center] at hmem
  exact (LieModule.mem_maxTrivSubmodule K L L z).mp hmem x
end StableLine

variable {K : Type*} [Field K] [CharZero K]
abbrev Mat2 (K : Type*) := Matrix (Fin 2) (Fin 2) K

def H : Mat2 K := !![1,0;0,-1]
def E : Mat2 K := !![0,1;0,0]
def F : Mat2 K := !![0,0;1,0]

 theorem extract_E (M : Mat2 K) :
    (1/8:K) • (⁅(H : Mat2 K),⁅(H : Mat2 K),M⁆⁆ + (2:K) • ⁅(H : Mat2 K),M⁆) = M 0 1 • (E : Mat2 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H,E,Ring.lie_def,Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two] <;> ring

theorem extract_F (M : Mat2 K) :
    (1/8:K) • (⁅(H : Mat2 K),⁅(H : Mat2 K),M⁆⁆ - (2:K) • ⁅(H : Mat2 K),M⁆) = M 1 0 • (F : Mat2 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H,F,Ring.lie_def,Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two] <;> ring

theorem E_mem_of_upper_ne_zero (S : LieSubalgebra K (Mat2 K)) (hH : H ∈ S)
    {M : Mat2 K} (hM : M ∈ S) (hb : M 0 1 ≠ 0) : E ∈ S := by
  have hm := S.smul_mem (1/8:K) (S.add_mem (S.lie_mem hH (S.lie_mem hH hM))
    (S.smul_mem (2:K) (S.lie_mem hH hM)))
  rw [extract_E] at hm
  have hs := S.smul_mem (M 0 1)⁻¹ hm
  simpa only [smul_smul,inv_mul_cancel₀ hb,one_smul] using hs

theorem F_mem_of_lower_ne_zero (S : LieSubalgebra K (Mat2 K)) (hH : H ∈ S)
    {M : Mat2 K} (hM : M ∈ S) (hc : M 1 0 ≠ 0) : F ∈ S := by
  have hm := S.smul_mem (1/8:K) (S.sub_mem (S.lie_mem hH (S.lie_mem hH hM))
    (S.smul_mem (2:K) (S.lie_mem hH hM)))
  rw [extract_F] at hm
  have hs := S.smul_mem (M 1 0)⁻¹ hm
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hs

theorem bracket_E (M : Mat2 K) (hc : M 1 0=0) : ⁅M,(E : Mat2 K)⁆=(M 0 0-M 1 1) • (E : Mat2 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E,Ring.lie_def,Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two,hc]

theorem bracket_F (M : Mat2 K) (hb : M 0 1=0) : ⁅M,(F : Mat2 K)⁆=(M 1 1-M 0 0) • (F : Mat2 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [F,Ring.lie_def,Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two,hb]

theorem E_mem_iff_F_mem (S : LieSubalgebra K (Mat2 K)) [HasCentralRadical K S]
    (hH : H ∈ S) : E ∈ S ↔ F ∈ S := by
  constructor
  · intro hE
    by_contra hF
    have hz (M : S) : M.val 1 0=0 := by
      by_contra hc
      exact hF (F_mem_of_lower_ne_zero S hH M.property hc)
    let e : S := ⟨E,hE⟩
    have hline (M : S) : ⁅M,e⁆ ∈ K ∙ e := by
      apply Submodule.mem_span_singleton.mpr
      refine ⟨M.val 0 0-M.val 1 1,?_⟩
      apply Subtype.ext
      exact (bracket_E M.val (hz M)).symm
    have hzero := invariant_line_central e hline (⟨H,hH⟩ : S)
    have he := congrArg (fun M : S => M.val 0 1) hzero
    norm_num [e,H,E,Ring.lie_def,Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two] at he
  · intro hF
    by_contra hE
    have hz (M : S) : M.val 0 1=0 := by
      by_contra hb
      exact hE (E_mem_of_upper_ne_zero S hH M.property hb)
    let f : S := ⟨F,hF⟩
    have hline (M : S) : ⁅M,f⁆ ∈ K ∙ f := by
      apply Submodule.mem_span_singleton.mpr
      refine ⟨M.val 1 1-M.val 0 0,?_⟩
      apply Subtype.ext
      exact (bracket_F M.val (hz M)).symm
    have hzero := invariant_line_central f hline (⟨H,hH⟩ : S)
    have he := congrArg (fun M : S => M.val 1 0) hzero
    norm_num [f,H,F,Ring.lie_def,Matrix.mul_apply,Matrix.vecMul,vecHead,vecTail,Fin.sum_univ_two] at he





theorem traceZero_decomposition (M : Mat2 K) (hM : Matrix.trace M=0) :
    M = M 0 0 • H + M 0 1 • (E : Mat2 K) + M 1 0 • (F : Mat2 K) := by
  have hsum : M 0 0+M 1 1=0 := by simpa [Matrix.trace,Fin.sum_univ_two] using hM
  have hd : M 1 1 = -(M 0 0) := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hsum)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H,E,F,hd]

/-- The diagonal trace-zero Lie algebra as the actual line generated by H. -/
def diagonalLie : LieSubalgebra K (Mat2 K) where
  toSubmodule := K ∙ H
  lie_mem' := by
    intro x y hx hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [smul_lie,lie_smul,lie_self,smul_zero]
    exact Submodule.zero_mem _

/-- The rank-one reductive dichotomy in actual 2-by-2 matrices. A reductive
trace-zero Lie subalgebra containing the full split diagonal line is either
that diagonal line or the whole special linear Lie algebra. -/
theorem eq_diagonal_or_eq_sl (S : LieSubalgebra K (Mat2 K))
    [HasCentralRadical K S] (hH : H ∈ S)
    (htrace : S ≤ LieAlgebra.SpecialLinear.sl (Fin 2) K) :
    S=diagonalLie ∨ S=LieAlgebra.SpecialLinear.sl (Fin 2) K := by
  by_cases hE : E ∈ S
  · right
    apply le_antisymm htrace
    intro M hM
    have ht : Matrix.trace M=0 := hM
    rw [traceZero_decomposition M ht]
    exact S.add_mem (S.add_mem (S.smul_mem _ hH) (S.smul_mem _ hE))
      (S.smul_mem _ ((E_mem_iff_F_mem S hH).mp hE))
  · left
    apply le_antisymm
    · intro M hM
      have hb : M 0 1=0 := by
        by_contra hb
        exact hE (E_mem_of_upper_ne_zero S hH hM hb)
      have hc : M 1 0=0 := by
        by_contra hc
        exact hE ((E_mem_iff_F_mem S hH).mpr (F_mem_of_lower_ne_zero S hH hM hc))
      apply Submodule.mem_span_singleton.mpr
      refine ⟨M 0 0,?_⟩
      have hm := traceZero_decomposition M (htrace hM)
      simpa only [hb,hc,zero_smul,add_zero] using hm.symm
    · intro M hM
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hM
      exact S.smul_mem _ hH

/-- In particular, a proper reductive Lie subalgebra containing H is
commutative and consists exactly of diagonal trace-zero matrices. -/
theorem proper_eq_diagonal (S : LieSubalgebra K (Mat2 K))
    [HasCentralRadical K S] (hH : H ∈ S)
    (htrace : S ≤ LieAlgebra.SpecialLinear.sl (Fin 2) K)
    (hproper : S ≠ LieAlgebra.SpecialLinear.sl (Fin 2) K) :
    S=diagonalLie := (eq_diagonal_or_eq_sl S hH htrace).resolve_right hproper

theorem proper_offdiagonal_zero (S : LieSubalgebra K (Mat2 K))
    [HasCentralRadical K S] (hH : H ∈ S)
    (htrace : S ≤ LieAlgebra.SpecialLinear.sl (Fin 2) K)
    (hproper : S ≠ LieAlgebra.SpecialLinear.sl (Fin 2) K)
    {M : Mat2 K} (hM : M ∈ S) : M 0 1=0 ∧ M 1 0=0 := by
  rw [proper_eq_diagonal S hH htrace hproper] at hM
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hM
  simp [H]

end VV.BBEKSl2Reductive


