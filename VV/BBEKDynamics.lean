import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
The concrete p=2 homogeneous dynamics of BBEK, Section 5. The two factors
are actual determinant-one matrix groups over the reals and 2-adics.
-/

noncomputable section
open Matrix Filter
open scoped Topology MatrixGroups

namespace VV.BBEKDynamics

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev Q2 := ℚ_[2]
abbrev G := SL(2, ℝ) × SL(2, Q2)

instance slTopologicalSpace {K : Type*} [CommRing K] [TopologicalSpace K] :
    TopologicalSpace SL(2,K) :=
  inferInstanceAs (TopologicalSpace {M : Matrix (Fin 2) (Fin 2) K // M.det=1})

instance slContinuousMul {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] :
    ContinuousMul SL(2,K) where
  continuous_mul :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

instance slTopologicalGroup {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] :
    IsTopologicalGroup SL(2,K) where
  continuous_inv := continuous_subtype_val.matrix_adjugate.subtype_mk _

def lower {K : Type*} [CommRing K] (u : K) : SL(2, K) :=
  ⟨!![1,0;u,1],by simp [Matrix.det_fin_two]⟩

def diagonal {K : Type*} [Field K] (a : K) (ha : a≠0) : SL(2, K) :=
  ⟨!![a,0;0,a⁻¹],by simp [Matrix.det_fin_two,ha]⟩

theorem lower_add {K : Type*} [CommRing K] (u v : K) :
    lower (u+v)=lower u*lower v := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower,Matrix.mul_apply,Fin.sum_univ_two,add_comm]

@[simp] theorem lower_zero {K : Type*} [CommRing K] : lower (0:K)=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower]

@[simp] theorem diagonal_one {K : Type*} [Field K] : diagonal (1:K) one_ne_zero=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

theorem diagonal_mul {K : Type*} [Field K] (a b : K) (ha : a≠0) (hb : b≠0) :
    diagonal (a*b) (mul_ne_zero ha hb)=diagonal a ha*diagonal b hb := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]

theorem diagonal_inv {K : Type*} [Field K] (a : K) (ha : a≠0) :
    (diagonal a ha)⁻¹=diagonal a⁻¹ (inv_ne_zero ha) := by
  apply inv_eq_of_mul_eq_one_left
  rw [← diagonal_mul]
  simp [ha]

theorem diagonal_conjugate {K : Type*} [Field K] (a u : K) (ha : a≠0) :
    diagonal a ha*lower u*(diagonal a ha)⁻¹=lower (a⁻¹^2*u) := by
  rw [diagonal_inv]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal,lower,Matrix.mul_apply,Fin.sum_univ_two,ha,pow_two] <;> ring

def x (u : ℝ) (v : Q2) : G := (lower u,lower v)

theorem x_add (u u' : ℝ) (v v' : Q2) : x (u+u') (v+v')=x u v*x u' v' := by
  simp only [x,Prod.mk_mul_mk,lower_add]

@[simp] theorem x_zero : x 0 0=1 := by simp [x]

def xHom : Multiplicative (ℝ×Q2) →* G where
  toFun a := x a.toAdd.1 a.toAdd.2
  map_one' := x_zero
  map_mul' a b := x_add _ _ _ _

def lowerUnipotent : Subgroup G := xHom.range

theorem mem_lowerUnipotent_iff (g : G) : g ∈ lowerUnipotent ↔
    ∃ u : ℝ,∃ v : Q2,x u v=g := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.toAdd.1,a.toAdd.2,ha⟩
  · rintro ⟨u,v,he⟩
    exact ⟨Multiplicative.ofAdd (u,v),he⟩

def psi (t : ℝ) (n : ℤ) : G :=
  (diagonal (Real.exp (-t)) (Real.exp_ne_zero _),
    diagonal ((2:Q2)^n) (zpow_ne_zero _ (by norm_num)))

@[simp] theorem psi_zero : psi 0 0=1 := by simp [psi]

theorem psi_add (t s : ℝ) (n m : ℤ) : psi (t+s) (n+m)=psi t n*psi s m := by
  apply Prod.ext
  · change diagonal (Real.exp (-(t+s))) (Real.exp_ne_zero _)=
      diagonal (Real.exp (-t)) (Real.exp_ne_zero _)*diagonal (Real.exp (-s)) (Real.exp_ne_zero _)
    simpa only [neg_add,Real.exp_add] using
      diagonal_mul (Real.exp (-t)) (Real.exp (-s)) (Real.exp_ne_zero _) (Real.exp_ne_zero _)
  · change diagonal ((2:Q2)^(n+m)) (zpow_ne_zero _ (by norm_num))=
      diagonal ((2:Q2)^n) (zpow_ne_zero _ (by norm_num))*
        diagonal ((2:Q2)^m) (zpow_ne_zero _ (by norm_num))
    simpa only [zpow_add₀ (by norm_num : (2:Q2)≠0)] using
      diagonal_mul ((2:Q2)^n) ((2:Q2)^m)
        (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (by norm_num))

theorem psi_neg (t : ℝ) (n : ℤ) : psi (-t) (-n)=(psi t n)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← psi_add]
  simp

/-- The additive parameter group acts by an actual matrix-group homomorphism. -/
def psiHom : Multiplicative (ℝ × ℤ) →* G where
  toFun a := psi a.toAdd.1 a.toAdd.2
  map_one' := psi_zero
  map_mul' a b := psi_add _ _ _ _

theorem psi_nat_mul (t : ℝ) (n : ℤ) (k : ℕ) :
    psi ((k:ℝ)*t) ((k:ℤ)*n)=(psi t n)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
      push_cast
      rw [add_mul,one_mul,add_mul,one_mul,psi_add,ih,pow_succ]

def Cone (t : ℝ) (n : ℤ) : Prop := 0≤n ∧ (2:ℝ)^n≤Real.exp t

theorem cone_iff (t : ℝ) (n : ℤ) : Cone t n ↔ 0≤n ∧ (n:ℝ)*Real.log 2≤t := by
  have h := Real.log_le_log_iff (zpow_pos (by norm_num : (0:ℝ)<2) n) (Real.exp_pos t)
  rw [Real.log_zpow,Real.log_exp] at h
  exact and_congr_right (fun _ => h.symm)

theorem cone_zero : Cone 0 0 := by norm_num [Cone]

theorem Cone.add {t s : ℝ} {n m : ℤ} (h : Cone t n) (k : Cone s m) : Cone (t+s) (n+m) := by
  refine ⟨add_nonneg h.1 k.1,?_⟩
  rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),Real.exp_add]
  exact mul_le_mul h.2 k.2 (zpow_nonneg (by norm_num) _) (Real.exp_pos _).le

theorem Cone.nat_mul {t : ℝ} {n : ℤ} (h : Cone t n) (k : ℕ) :
    Cone ((k:ℝ)*t) ((k:ℤ)*n) := by
  induction k with
  | zero => simpa using cone_zero
  | succ k ih =>
      convert ih.add h using 1 <;> push_cast <;> ring

theorem cone_one_of_log_two_lt {t : ℝ} (ht : Real.log 2<t) : Cone t 1 := by
  refine ⟨by omega,?_⟩
  have h := (Real.exp_lt_exp.mpr ht).le
  rw [Real.exp_log (by norm_num)] at h
  simpa only [zpow_one] using h

/-- An explicit common positive cone translate of any additive parameter.
Consequently C-C is all of R × Z, as used in the Section 5 argument. -/
theorem exists_cone_translate (t : ℝ) (n : ℤ) :
    ∃ s : ℝ,∃ m : ℤ,Cone s m ∧ Cone (t+s) (n+m) := by
  let m : ℤ := max 0 (-n)
  let s : ℝ := max ((m:ℝ)*Real.log 2) (((n+m:ℤ):ℝ)*Real.log 2-t)
  refine ⟨s,m,(cone_iff _ _).mpr ⟨?_,?_⟩,(cone_iff _ _).mpr ⟨?_,?_⟩⟩
  · exact le_max_left _ _
  · exact le_max_left _ _
  · have hm : -n≤m := le_max_right _ _
    omega
  · have hs : ((n+m:ℤ):ℝ)*Real.log 2-t≤s := le_max_right _ _
    linarith

theorem cone_difference_all (t : ℝ) (n : ℤ) :
    ∃ t₁ t₂ : ℝ,∃ n₁ n₂ : ℤ,
      Cone t₁ n₁ ∧ Cone t₂ n₂ ∧ t=t₁-t₂ ∧ n=n₁-n₂ := by
  obtain ⟨s,m,hs,ht⟩ := exists_cone_translate t n
  exact ⟨t+s,s,n+m,m,ht,hs,by ring,by ring⟩

theorem psi_is_cone_quotient (t : ℝ) (n : ℤ) :
    ∃ t₁ t₂ : ℝ,∃ n₁ n₂ : ℤ,Cone t₁ n₁ ∧ Cone t₂ n₂ ∧
      psi t n=psi t₁ n₁*(psi t₂ n₂)⁻¹ := by
  obtain ⟨s,m,hs,ht⟩ := exists_cone_translate t n
  refine ⟨t+s,s,n+m,m,ht,hs,?_⟩
  rw [psi_add,mul_inv_cancel_right]

theorem psi_conjugate (t : ℝ) (n : ℤ) (u : ℝ) (v : Q2) :
    psi t n*x u v*(psi t n)⁻¹ = x (Real.exp (2*t)*u) ((2:Q2)^(-2*n)*v) := by
  apply Prod.ext
  · change diagonal (Real.exp (-t)) (Real.exp_ne_zero _)*lower u*
      (diagonal (Real.exp (-t)) (Real.exp_ne_zero _))⁻¹=lower _
    rw [diagonal_conjugate]
    congr 1
    rw [← Real.exp_neg,neg_neg,← Real.exp_nat_mul]
    norm_num
  · change diagonal ((2:Q2)^n) (zpow_ne_zero _ (by norm_num))*lower v*
      (diagonal ((2:Q2)^n) (zpow_ne_zero _ (by norm_num)))⁻¹=lower _
    rw [diagonal_conjugate]
    congr 1
    rw [← zpow_neg,← zpow_natCast,← zpow_mul]
    congr 2
    ring

theorem psi_inverse_conjugate (t : ℝ) (u : ℝ) (v : Q2) :
    (psi t 1)⁻¹*x u v*psi t 1=x (Real.exp (-2*t)*u) ((2:Q2)^2*v) := by
  have h := psi_conjugate (-t) (-1) u v
  rw [psi_neg,inv_inv] at h
  simpa only [show 2*(-t) = -2*t by ring,show (-2:ℤ)*(-1)=2 by ring,
    zpow_ofNat] using h

theorem psi_inverse_iterate_conjugate (t : ℝ) (u : ℝ) (v : Q2) (k : ℕ) :
    ((psi t 1)⁻¹)^k*x u v*(psi t 1)^k =
      x ((Real.exp (-2*t))^k*u) (((2:Q2)^2)^k*v) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ' ((psi t 1)⁻¹),pow_succ (psi t 1)]
      have he : (psi t 1)⁻¹*((psi t 1)⁻¹)^k*x u v*((psi t 1)^k*psi t 1) =
          (psi t 1)⁻¹*(((psi t 1)⁻¹)^k*x u v*(psi t 1)^k)*psi t 1 := by group
      rw [he,ih,psi_inverse_conjugate]
      simp only [pow_succ]
      congr 1 <;> ring

theorem continuous_lower {K : Type*} [CommRing K] [TopologicalSpace K] :
    Continuous (lower : K → SL(2,K)) := by
  unfold lower
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_x : Continuous (fun a : ℝ×Q2 => x a.1 a.2) :=
  (continuous_lower.comp continuous_fst).prodMk (continuous_lower.comp continuous_snd)

theorem real_inverse_parameter_tendsto {t : ℝ} (ht : 0<t) (u : ℝ) :
    Tendsto (fun k : ℕ => (Real.exp (-2*t))^k*u) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-2*t)).le
    (Real.exp_lt_one_iff.mpr (by linarith : -2*t<0))).mul_const u
  simpa only [zero_mul] using h

theorem padic_inverse_parameter_tendsto (v : Q2) :
    Tendsto (fun k : ℕ => ((2:Q2)^2)^k*v) atTop (𝓝 0) := by
  have hn : ‖(2:Q2)^2‖<1 := by
    rw [norm_pow,show ‖(2:Q2)‖=(2:ℝ)⁻¹ from padicNormE.norm_p]
    norm_num
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn).mul_const v

/-- The complete lower unipotent parameter group is unstable for the
time-(t,1) element: its inverse conjugates tend to the identity in the
actual product topology, whenever t>0. -/
theorem lower_inverse_conjugates_tendsto {t : ℝ} (ht : 0<t) (u : ℝ) (v : Q2) :
    Tendsto (fun k : ℕ => ((psi t 1)⁻¹)^k*x u v*(psi t 1)^k) atTop (𝓝 1) := by
  have hp := (real_inverse_parameter_tendsto ht u).prodMk_nhds
    (padic_inverse_parameter_tendsto v)
  have h := (continuous_x.tendsto (0,0)).comp hp
  simpa only [Function.comp_apply,psi_inverse_iterate_conjugate,x_zero] using h

theorem lowerUnipotent_unstable {t : ℝ} (ht : 0<t) {g : G} (hg : g ∈ lowerUnipotent) :
    Tendsto (fun k : ℕ => ((psi t 1)⁻¹)^k*g*(psi t 1)^k) atTop (𝓝 1) := by
  obtain ⟨u,v,rfl⟩ := (mem_lowerUnipotent_iff g).mp hg
  exact lower_inverse_conjugates_tendsto ht u v

/-- The paper's strict-cone choice n=1 and t>log 2 supplies both the
semigroup condition and the required unstable direction. -/
theorem strict_cone_unstable {t : ℝ} (ht : Real.log 2<t) :
    Cone t 1 ∧ ∀ u : ℝ,∀ v : Q2,
      Tendsto (fun k : ℕ => ((psi t 1)⁻¹)^k*x u v*(psi t 1)^k) atTop (𝓝 1) := by
  refine ⟨cone_one_of_log_two_lt ht,fun u v => lower_inverse_conjugates_tendsto ?_ u v⟩
  exact lt_trans (Real.log_pos (by norm_num : (1:ℝ)<2)) ht

def time0 : ℝ := Real.log 2+1

theorem time0_gt_log_two : Real.log 2<time0 := by unfold time0; linarith

theorem time0_cone_unstable : Cone time0 1 ∧ ∀ u : ℝ,∀ v : Q2,
    Tendsto (fun k : ℕ => ((psi time0 1)⁻¹)^k*x u v*(psi time0 1)^k) atTop (𝓝 1) :=
  strict_cone_unstable time0_gt_log_two

end VV.BBEKDynamics
