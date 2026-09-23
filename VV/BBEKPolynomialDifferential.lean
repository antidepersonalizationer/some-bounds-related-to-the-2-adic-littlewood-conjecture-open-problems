import VV.BBEKAlgebraicOrbit
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Formal polynomial differentials at an actual point, with a proved chain
rule. This is the concrete input for an algebraic subgroup's tangent space. -/
noncomputable section
open MvPolynomial
namespace VV.BBEKPolynomialDifferential

variable {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]

def differential (x : σ → K) (p : MvPolynomial σ K) : (σ → K) →ₗ[K] K where
  toFun v := ∑ i, eval x (pderiv i p)*v i
  map_add' := by intros; simp [mul_add,Finset.sum_add_distrib]
  map_smul' := by intros; simp [mul_left_comm,Finset.mul_sum]

theorem differential_apply (x v : σ → K) (p : MvPolynomial σ K) :
    differential x p v = ∑ i, eval x (pderiv i p)*v i := rfl

@[simp] theorem differential_C (x v : σ → K) (a : K) :
    differential x (C a) v=0 := by simp [differential,pderiv_C]

@[simp] theorem differential_one (x v : σ → K) :
    differential x (1 : MvPolynomial σ K) v=0 := by
  simpa using differential_C x v (1:K)

@[simp] theorem differential_zero (x v : σ → K) :
    differential x (0 : MvPolynomial σ K) v=0 := by
  simpa using differential_C x v (0:K)

@[simp] theorem differential_X (x v : σ → K) (i : σ) :
    differential x (X i) v=v i := by
  classical
  simp [differential,pderiv_X,Pi.single_apply]

@[simp] theorem differential_add (x v : σ → K) (p q : MvPolynomial σ K) :
    differential x (p+q) v=differential x p v+differential x q v := by
  simp [differential,map_add,add_mul,Finset.sum_add_distrib]

@[simp] theorem differential_sub (x v : σ → K) (p q : MvPolynomial σ K) :
    differential x (p-q) v=differential x p v-differential x q v := by
  simp [differential,map_sub,sub_mul,Finset.sum_sub_distrib]

theorem differential_mul (x v : σ → K) (p q : MvPolynomial σ K) :
    differential x (p*q) v =
      differential x p v * eval x q + eval x p * differential x q v := by
  simp only [differential_apply,pderiv_mul,map_add,map_mul,add_mul,
    Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- The formal chain rule, proved for actual substitution of polynomials. -/
theorem differential_substitute (x v : σ → K) (f : τ → MvPolynomial σ K)
    (p : MvPolynomial τ K) :
    differential x (p.eval₂ C f) v =
      differential (fun i => eval x (f i)) p (fun i => differential x (f i) v) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    have he : eval x (p.eval₂ C f)=eval (fun i => eval x (f i)) p := by
      rw [eval₂_comp_left]
      have hc : (eval x).comp C = RingHom.id K := by ext a; simp
      rw [hc]
      rfl
    rw [eval₂_mul,eval₂_X,differential_mul,differential_mul,hp,differential_X,eval_X,he]

end VV.BBEKPolynomialDifferential
