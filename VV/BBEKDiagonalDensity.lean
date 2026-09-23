import VV.BBEKOrbitBaire
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Eval

/-! Polynomial density of the actual split diagonal torus: a neighborhood
in the local-field topology suffices to determine every polynomial equation. -/
noncomputable section
open Matrix Set Filter
open scoped Topology MatrixGroups LaurentPolynomial
namespace VV.BBEKDiagonalDensity
open BBEKDynamics BBEKDiagonal

variable {K : Type*} [Field K]

theorem laurent_eq_zero_of_infinite (f : LaurentPolynomial K)
    {U : Set Kˣ} (hU : U.Infinite)
    (hf : ∀ a ∈ U, LaurentPolynomial.eval₂ (RingHom.id K) a f=0) : f=0 := by
  obtain ⟨n,p,hp⟩ := LaurentPolynomial.exists_T_pow f
  have hroots : ∀ a ∈ U, p.eval (a:K)=0 := by
    intro a ha
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) a) hp
    simpa only [LaurentPolynomial.eval₂_toLaurent,map_mul,hf a ha,zero_mul] using he
  have hz : p=0 := Polynomial.eq_zero_of_infinite_isRoot p
    ((hU.image (fun a _ b _ h => Units.ext h)).mono (by
      rintro x ⟨a,ha,rfl⟩
      exact hroots a ha))
  have he := congrArg (fun z => z*LaurentPolynomial.T (-(n:ℤ))) hp
  simpa [hz,LaurentPolynomial.mul_T_assoc] using he.symm

theorem laurent_vanishes_of_infinite (f : LaurentPolynomial K)
    {U : Set Kˣ} (hU : U.Infinite)
    (hf : ∀ a ∈ U, LaurentPolynomial.eval₂ (RingHom.id K) a f=0) :
    ∀ a : Kˣ, LaurentPolynomial.eval₂ (RingHom.id K) a f=0 := by
  obtain ⟨n,p,hp⟩ := LaurentPolynomial.exists_T_pow f
  have hroots : ∀ a ∈ U, p.eval (a:K)=0 := by
    intro a ha
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) a) hp
    simpa only [LaurentPolynomial.eval₂_toLaurent,map_mul,
      hf a ha,zero_mul] using he
  have hz : p=0 := Polynomial.eq_zero_of_infinite_isRoot p
    ((hU.image (fun a _ b _ h => Units.ext h)).mono (by
      rintro x ⟨a,ha,rfl⟩
      exact hroots a ha))
  intro a
  have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) a) hp
  simp only [hz,map_zero,map_mul,LaurentPolynomial.eval₂_T_n] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (pow_ne_zero n a.ne_zero)

def diagonalVariables (ij : Fin 2 × Fin 2) : LaurentPolynomial K :=
  if ij=(0,0) then LaurentPolynomial.T 1 else
    if ij=(1,1) then LaurentPolynomial.T (-1) else 0

def diagonalRestriction (p : MvPolynomial (Fin 2 × Fin 2) K) : LaurentPolynomial K :=
  p.eval₂ LaurentPolynomial.C diagonalVariables

def unitDiagonalMatrix (a : Kˣ) : SL(2,K) := diagonal a.val a.ne_zero

theorem eval_diagonalRestriction (p : MvPolynomial (Fin 2 × Fin 2) K) (a : Kˣ) :
    LaurentPolynomial.eval₂ (RingHom.id K) a (diagonalRestriction p)=
      MvPolynomial.eval (fun ij => unitDiagonalMatrix a ij.1 ij.2) p := by
  unfold diagonalRestriction
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (LaurentPolynomial.eval₂ (RingHom.id K) a).comp LaurentPolynomial.C =
      RingHom.id K := by ext x; simp
  rw [hc]
  apply congrArg (fun v => MvPolynomial.eval₂ (RingHom.id K) v p)
  funext ij
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [diagonalVariables,unitDiagonalMatrix,BBEKDynamics.diagonal]

def matrixZeroSet (P : Set (MvPolynomial (Fin 2 × Fin 2) K)) : Set SL(2,K) :=
  {g | ∀ p ∈ P, MvPolynomial.eval (fun ij => g ij.1 ij.2) p=0}

theorem diagonal_subset_zeroSet_of_infinite
    (P : Set (MvPolynomial (Fin 2 × Fin 2) K)) {U : Set Kˣ} (hU : U.Infinite)
    (hP : ∀ a ∈ U, unitDiagonalMatrix a ∈ matrixZeroSet P) :
    ∀ a : Kˣ, unitDiagonalMatrix a ∈ matrixZeroSet P := by
  intro a p hp
  rw [← eval_diagonalRestriction]
  apply laurent_vanishes_of_infinite (diagonalRestriction p) hU _ a
  intro b hb
  rw [eval_diagonalRestriction]
  exact hP b hb p hp

section LocalField
variable {F : Type*} [NontriviallyNormedField F]

theorem infinite_of_units_nhds {U : Set Fˣ} (hU : U ∈ 𝓝 (1:Fˣ)) : U.Infinite := by
  have he : Topology.IsOpenEmbedding (Units.val : Fˣ → F) := by
    refine ⟨Units.isEmbedding_val₀,?_⟩
    have hr : Set.range (Units.val : Fˣ → F) = {x | x ≠ 0} := by
      ext x
      exact isUnit_iff_ne_zero
    rw [hr]
    exact isClosed_singleton.isOpen_compl
  have hIm : Units.val '' U ∈ 𝓝 (1:F) := by
    simpa only [Units.val_one] using he.isOpenMap.image_mem_nhds hU
  exact (infinite_of_mem_nhds (1:F) hIm).of_image

/-- Full polynomial density from a literal neighborhood of the identity.
The family P may be infinite; no Noetherian or dimension premise is used. -/
theorem diagonal_subset_zeroSet_of_nhds
    (P : Set (MvPolynomial (Fin 2 × Fin 2) F))
    (hP : {a : Fˣ | unitDiagonalMatrix a ∈ matrixZeroSet P} ∈ 𝓝 1) :
    ∀ a : Fˣ, unitDiagonalMatrix a ∈ matrixZeroSet P :=
  diagonal_subset_zeroSet_of_infinite P (infinite_of_units_nhds hP) (fun _ ha => ha)

end LocalField
end VV.BBEKDiagonalDensity

