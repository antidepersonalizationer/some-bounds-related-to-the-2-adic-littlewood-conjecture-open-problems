import VV.BBEKTangentDiagonal
import Mathlib.RingTheory.Derivation.Lie

/-! Lie closure of the actual algebraic tangent, proved with invariant
polynomial vector fields preserving the actual vanishing ideal. -/
noncomputable section
open Matrix MvPolynomial
open scoped MatrixGroups
namespace VV.BBEKTangentLie
open BBEKPolynomialDifferential BBEKAlgebraicTangent

variable {K : Type*} [Field K]

def vectorFieldVariables (M : Mat2 K) (ij : Fin 2 × Fin 2) : Polys K :=
  ∑ k : Fin 2, X (ij.1,k)*C (M k ij.2)

def fieldDerivation (M : Mat2 K) : Derivation K (Polys K) (Polys K) :=
  MvPolynomial.mkDerivation K (vectorFieldVariables M)

theorem eval_vectorFieldVariables (M g : Mat2 K) (ij : Fin 2 × Fin 2) :
    eval (entries g) (vectorFieldVariables M ij)=entries (g*M) ij := by
  simp [vectorFieldVariables,entries,Matrix.mul_apply,Fin.sum_univ_two]

theorem fieldDerivation_eval (M g : Mat2 K) (p : Polys K) :
    eval (entries g) (fieldDerivation M p)=
      differential (entries g) p (entries (g*M)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [fieldDerivation]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    rw [(fieldDerivation M).leibniz]
    simp only [smul_eq_mul,map_add,map_mul,hp]
    rw [show fieldDerivation M (X i)=vectorFieldVariables M i from mkDerivation_X K (vectorFieldVariables M) i,
      eval_vectorFieldVariables,differential_mul,differential_X,eval_X]
    ring

def leftVariables (g : SL(2,K)) (ij : Fin 2 × Fin 2) : Polys K :=
  ∑ k : Fin 2, C (g ij.1 k)*X (k,ij.2)

theorem eval_leftVariables (g : SL(2,K)) (M : Mat2 K) (ij : Fin 2 × Fin 2) :
    eval (entries M) (leftVariables g ij)=entries (g.val*M) ij := by
  simp [leftVariables,entries,Matrix.mul_apply,Fin.sum_univ_two]

theorem differential_leftVariables (g : SL(2,K)) (M : Mat2 K)
    (x : Fin 2 × Fin 2 → K) (ij : Fin 2 × Fin 2) :
    differential x (leftVariables g ij) (entries M)=entries (g.val*M) ij := by
  simp [leftVariables,differential_mul,entries,Matrix.mul_apply,Fin.sum_univ_two]

def leftPullback (g : SL(2,K)) (p : Polys K) : Polys K := p.eval₂ C (leftVariables g)

theorem eval_leftPullback (g : SL(2,K)) (M : Mat2 K) (p : Polys K) :
    eval (entries M) (leftPullback g p)=eval (entries (g.val*M)) p := by
  unfold leftPullback
  rw [eval₂_comp_left]
  have hc : (eval (entries M)).comp C=RingHom.id K := by ext a; simp
  rw [hc]
  congr 1
  funext ij
  exact eval_leftVariables g M ij

theorem leftPullback_mem (L : Subgroup SL(2,K)) {g : SL(2,K)} (hg : g ∈ L)
    {p : Polys K} (hp : p ∈ vanishingIdeal L) : leftPullback g p ∈ vanishingIdeal L := by
  intro h hh
  rw [eval_leftPullback]
  exact hp (g*h) (L.mul_mem hg hh)

/-- A tangent vector gives an invariant derivation preserving every actual
polynomial equation of the subgroup. -/
theorem fieldDerivation_mem (L : Subgroup SL(2,K)) {M : Mat2 K} (hM : M ∈ tangent L)
    {p : Polys K} (hp : p ∈ vanishingIdeal L) : fieldDerivation M p ∈ vanishingIdeal L := by
  intro g hg
  rw [fieldDerivation_eval]
  have hz := hM (leftPullback g p) (leftPullback_mem L hg hp)
  unfold leftPullback at hz
  rw [differential_substitute] at hz
  have he : (fun ij => eval identityEntries (leftVariables g ij))=entries g.val := by
    funext ij
    rw [identityEntries,eval_leftVariables,Matrix.mul_one]
  simpa only [he,differential_leftVariables] using hz

theorem fieldDerivation_bracket (M N : Mat2 K) :
    fieldDerivation ⁅M,N⁆ = ⁅fieldDerivation M,fieldDerivation N⁆ := by
  apply MvPolynomial.derivation_ext
  intro ij
  rw [Derivation.commutator_apply]
  simp [fieldDerivation,vectorFieldVariables,Fin.sum_univ_two,Derivation.leibniz,
    smul_eq_mul,Ring.lie_def,Matrix.mul_apply]
  ring

theorem tangent_lie_mem (L : Subgroup SL(2,K)) {M N : Mat2 K}
    (hM : M ∈ tangent L) (hN : N ∈ tangent L) : ⁅M,N⁆ ∈ tangent L := by
  intro p hp
  have hm := fieldDerivation_mem L hM (fieldDerivation_mem L hN hp)
  have hn := fieldDerivation_mem L hN (fieldDerivation_mem L hM hp)
  have hz : fieldDerivation ⁅M,N⁆ p ∈ vanishingIdeal L := by
    rw [fieldDerivation_bracket,Derivation.commutator_apply]
    exact (vanishingIdeal L).sub_mem hm hn
  have he := hz 1 L.one_mem
  rw [fieldDerivation_eval] at he
  simpa only [Matrix.SpecialLinearGroup.coe_one,Matrix.one_mul,identityEntries] using he

/-- The actual Lie algebra of the subgroup's defining ideal at the identity. -/
def tangentLie (L : Subgroup SL(2,K)) : LieSubalgebra K (Mat2 K) where
  toSubmodule := tangent L
  lie_mem' := tangent_lie_mem L

theorem tangentLie_le_sl (L : Subgroup SL(2,K)) :
    tangentLie L ≤ LieAlgebra.SpecialLinear.sl (Fin 2) K := by
  intro M hM
  exact tangent_trace_zero L hM

theorem H_mem_tangentLie [Infinite K] (L : Subgroup SL(2,K))
    (hD : BBEKDiagonal.diagonalGroup K ≤ L) : BBEKSl2Reductive.H ∈ tangentLie L :=
  BBEKTangentDiagonal.H_mem_tangent L hD

end VV.BBEKTangentLie

