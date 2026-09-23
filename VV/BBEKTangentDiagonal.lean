import VV.BBEKAlgebraicTangent
import Mathlib.Algebra.DualNumber

/-! The diagonal infinitesimal generator belongs to the actual tangent:
evaluate the vanishing Laurent restriction at the dual-number unit 1+epsilon. -/
noncomputable section
open MvPolynomial Matrix Set TrivSqZeroExt
open scoped MatrixGroups DualNumber
namespace VV.BBEKTangentDiagonal
open BBEKPolynomialDifferential BBEKAlgebraicTangent BBEKDiagonalDensity

variable {K σ : Type*} [Field K] [Fintype σ]

def firstJet (x v : σ → K) : MvPolynomial σ K →+* DualNumber K :=
  eval₂Hom (inlHom K K) (fun i => (x i,v i))

theorem firstJet_eq (x v : σ → K) (p : MvPolynomial σ K) :
    firstJet x v p=(eval x p,differential x p v) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [firstJet,TrivSqZeroExt.inl]
  | add p q hp hq =>
    rw [map_add,hp,hq]
    apply TrivSqZeroExt.ext <;> simp
  | mul_X p i hp =>
    rw [map_mul,hp]
    have hx : firstJet x v (X i)=(x i,v i) := by simp [firstJet]
    rw [hx]
    apply TrivSqZeroExt.ext <;> simp [differential_mul,DualNumber.snd_mul,add_comm,mul_comm]

def dualOne : (DualNumber K)ˣ where
  val := (1,1)
  inv := (1,-1)
  val_inv := by apply TrivSqZeroExt.ext <;> simp [DualNumber.snd_mul]
  inv_val := by apply TrivSqZeroExt.ext <;> simp [DualNumber.snd_mul]

theorem restriction_firstJet (p : Polys K) :
    LaurentPolynomial.eval₂ (inlHom K K) dualOne (diagonalRestriction p) =
      firstJet identityEntries (entries BBEKSl2Reductive.H) p := by
  unfold diagonalRestriction firstJet
  rw [eval₂_comp_left]
  have hc : (LaurentPolynomial.eval₂ (inlHom K K) (dualOne (K:=K))).comp
      LaurentPolynomial.C = inlHom K K := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,LaurentPolynomial.eval₂_C]
  rw [hc]
  apply congrArg (fun f => eval₂ (inlHom K K) f p)
  funext ij
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [diagonalVariables,dualOne,identityEntries,entries,BBEKSl2Reductive.H] <;> rfl

theorem infinite_units [Infinite K] : (Set.univ : Set Kˣ).Infinite := by
  have hi : ({x : K | x ≠ 0} : Set K).Infinite := by
    have he : (Set.univ \ {0} : Set K)={x : K | x ≠ 0} := by ext x; simp
    rw [← he]
    exact Set.infinite_univ.diff (Set.finite_singleton (0:K))
  have hr : Units.val '' (Set.univ : Set Kˣ) = {x : K | x ≠ 0} := by
    rw [Set.image_univ]
    ext x
    exact isUnit_iff_ne_zero
  rw [← hr] at hi
  exact hi.of_image

/-- This uses the actual vanishing ideal and actual formal tangent. The H
membership is a theorem obtained from torus containment, not a field of an
abstract algebraic-group interface. -/
theorem H_mem_tangent [Infinite K] (L : Subgroup SL(2,K))
    (hD : BBEKDiagonal.diagonalGroup K ≤ L) : BBEKSl2Reductive.H ∈ tangent L := by
  intro p hp
  have hz : diagonalRestriction p=0 :=
    laurent_eq_zero_of_infinite _ infinite_units (fun a _ => by
      rw [eval_diagonalRestriction]
      exact hp (unitDiagonalMatrix a) (hD ⟨a.val,a.ne_zero,rfl⟩))
  have he : firstJet identityEntries (entries BBEKSl2Reductive.H) p=0 := by
    rw [← restriction_firstJet,hz,map_zero]
  have hs := congrArg TrivSqZeroExt.snd he
  simpa only [firstJet_eq,TrivSqZeroExt.snd_mk,TrivSqZeroExt.snd_zero] using hs

end VV.BBEKTangentDiagonal

