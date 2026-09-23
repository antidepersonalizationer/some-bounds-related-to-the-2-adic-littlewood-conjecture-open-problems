import VV.BBEKTangentLie
import Mathlib.Algebra.Polynomial.Derivative

/-! A square-zero tangent vector integrates into the actual algebraic subgroup.
The proof uses invariant polynomial derivations and ordinary Taylor coefficients. -/
noncomputable section
open Matrix MvPolynomial Set
open scoped MatrixGroups Polynomial
namespace VV.BBEKNilpotentTangent
open BBEKPolynomialDifferential BBEKAlgebraicTangent BBEKTangentLie BBEKDiagonalDensity

variable {K : Type*} [Field K] [CharZero K]

def curveVariables (M : Mat2 K) (ij : Fin 2 × Fin 2) : K[X] :=
  Polynomial.C (identityEntries ij)+Polynomial.C (M ij.1 ij.2)*Polynomial.X

def curve (M : Mat2 K) : Polys K →+* K[X] := eval₂Hom Polynomial.C (curveVariables M)

theorem eval_curve (M : Mat2 K) (p : Polys K) (t : K) :
    (curve M p).eval t = eval (entries (1+t • M)) p := by
  change (Polynomial.evalRingHom t) (eval₂ Polynomial.C (curveVariables M) p)=_
  rw [eval₂_comp_left]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id K := by
    ext a
    simp
  rw [hc]
  congr 1
  funext ij
  change Polynomial.eval t (Polynomial.C (identityEntries ij)+
    Polynomial.C (M ij.1 ij.2)*Polynomial.X)=_
  rw [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_C,
    Polynomial.eval_X]
  change identityEntries ij+M ij.1 ij.2*t=identityEntries ij+t*M ij.1 ij.2
  ring

theorem curve_fieldDerivation_X {M : Mat2 K} (hM : M*M=0) (ij : Fin 2 × Fin 2) :
    curve M (fieldDerivation M (X ij))=Polynomial.C (M ij.1 ij.2) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_univ.mono
  intro t _
  change (curve M (fieldDerivation M (X ij))).eval t=
    (Polynomial.C (M ij.1 ij.2)).eval t
  rw [eval_curve]
  rw [show fieldDerivation M (X ij)=vectorFieldVariables M ij from
    mkDerivation_X K (vectorFieldVariables M) ij]
  rw [eval_vectorFieldVariables]
  simp [add_mul,Matrix.smul_mul,hM,entries]

theorem derivative_curve {M : Mat2 K} (hM : M*M=0) (p : Polys K) :
    Polynomial.derivative (curve M p)=curve M (fieldDerivation M p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [curve,fieldDerivation]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    rw [map_mul,Polynomial.derivative_mul,hp,(fieldDerivation M).leibniz]
    simp only [smul_eq_mul,map_add,map_mul,curve_fieldDerivation_X hM]
    have hx : Polynomial.derivative (curve M (X i))=Polynomial.C (M i.1 i.2) := by
      simp [curve,curveVariables]
    rw [hx]
    ring

theorem iterate_derivative_curve {M : Mat2 K} (hM : M*M=0) (p : Polys K) (n : ℕ) :
    Polynomial.derivative^[n] (curve M p)=curve M ((fieldDerivation M)^[n] p) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,derivative_curve hM,
      Function.iterate_succ_apply']

theorem curve_eq_zero (L : Subgroup SL(2,K)) {M : Mat2 K}
    (hM : M ∈ tangent L) (hM2 : M*M=0) {p : Polys K} (hp : p ∈ vanishingIdeal L) :
    curve M p=0 := by
  have hiter (n : ℕ) : (fieldDerivation M)^[n] p ∈ vanishingIdeal L := by
    induction n with
    | zero => exact hp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact fieldDerivation_mem L hM ih
  have hz (n : ℕ) : (Polynomial.derivative^[n] (curve M p)).eval 0=0 := by
    rw [iterate_derivative_curve hM2,eval_curve]
    simpa using hiter n 1 L.one_mem
  ext n
  have he := hz n
  rw [← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_iterate_derivative] at he
  simp only [zero_add,Nat.descFactorial_self,nsmul_eq_mul] at he
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simpa only [Polynomial.coeff_zero] using (mul_eq_zero.mp he).resolve_left hn

/-- All defining polynomial equations hold along 1+tM, by a proved Taylor
argument. No exponentiation or Lie-integration premise appears. -/
theorem equations_hold_on_nilpotent_curve (L : Subgroup SL(2,K)) {M : Mat2 K}
    (hM : M ∈ tangent L) (hM2 : M*M=0) {p : Polys K} (hp : p ∈ vanishingIdeal L)
    (t : K) : eval (entries (1+t • M)) p=0 := by
  rw [← eval_curve,curve_eq_zero L hM hM2 hp,Polynomial.eval_zero]

open BBEKDynamics BBEKMahlerPadic
open BBEKSl2Reductive (E F)

theorem upper_mem_of_E_tangent (L : Subgroup SL(2,K))
    (P : Set (Polys K)) (hL : (L : Set SL(2,K))=matrixZeroSet P)
    (hE : E ∈ tangent L) (u : K) : upper u ∈ L := by
  change upper u ∈ (L : Set SL(2,K))
  rw [hL]
  intro p hp
  have hv : p ∈ vanishingIdeal L := by
    intro g hg
    change g ∈ (L : Set SL(2,K)) at hg
    rw [hL] at hg
    exact hg p hp
  have hnil : (E : Mat2 K)*E=0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E,Matrix.mul_apply,Fin.sum_univ_two]
  have he := equations_hold_on_nilpotent_curve L hE hnil hv u
  have hm : (1+u • (E : Mat2 K))=(upper u).val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E,upper]
  simpa only [hm] using he

theorem lower_mem_of_F_tangent (L : Subgroup SL(2,K))
    (P : Set (Polys K)) (hL : (L : Set SL(2,K))=matrixZeroSet P)
    (hF : F ∈ tangent L) (u : K) : lower u ∈ L := by
  change lower u ∈ (L : Set SL(2,K))
  rw [hL]
  intro p hp
  have hv : p ∈ vanishingIdeal L := by
    intro g hg
    change g ∈ (L : Set SL(2,K)) at hg
    rw [hL] at hg
    exact hg p hp
  have hnil : (F : Mat2 K)*F=0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [F,Matrix.mul_apply,Fin.sum_univ_two]
  have he := equations_hold_on_nilpotent_curve L hF hnil hv u
  have hm : (1+u • (F : Mat2 K))=(lower u).val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [F,lower]
  simpa only [hm] using he

/-- A proper subgroup defined by actual polynomial equations has proper
tangent Lie algebra. This is proved directly in SL2, without assuming a
dimension theorem, connectedness, or a Lie-group/algebraic-group bridge. -/
theorem tangentLie_ne_sl_of_proper (L : Subgroup SL(2,K))
    (P : Set (Polys K)) (hL : (L : Set SL(2,K))=matrixZeroSet P)
    (hproper : L ≠ ⊤) : tangentLie L ≠ LieAlgebra.SpecialLinear.sl (Fin 2) K := by
  intro he
  have hE : E ∈ tangent L := by
    change E ∈ tangentLie L
    rw [he]
    change Matrix.trace (E : Mat2 K)=0
    simp [Matrix.trace,Fin.sum_univ_two,E]
  have hF : F ∈ tangent L := by
    change F ∈ tangentLie L
    rw [he]
    change Matrix.trace (F : Mat2 K)=0
    simp [Matrix.trace,Fin.sum_univ_two,F]
  exact hproper (sl2_eq_top_of_unipotents L
    (upper_mem_of_E_tangent L P hL hE) (lower_mem_of_F_tangent L P hL hF))

end VV.BBEKNilpotentTangent
