import VV.BBEKDynamics
import VV.BBEKFiniteQuotients
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.GroupTheory.GroupAction.Basic

/-! Mautner's contraction argument for continuous isometric actions.
This is a proved representation-theoretic ingredient, not a measure
classification or entropy hypothesis. -/

noncomputable section
open Filter Matrix
open scoped Topology MatrixGroups

namespace VV.BBEKMautner

theorem fixed_of_contracting_conjugates {H E : Type*}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace E] [MulAction H E] [ContinuousSMul H E]
    (hiso : ∀ g : H, Isometry (fun w : E => g • w))
    {a h : H} {v : E} (ha : a • v = v)
    (hc : Tendsto (fun n : ℕ => (a⁻¹)^n * h * a^n) atTop (𝓝 1)) : h • v = v := by
  have hmem : a ∈ MulAction.stabilizer H v := ha
  have hp (n : ℕ) : a^n • v = v :=
    (MulAction.stabilizer H v).pow_mem hmem n
  have hi (n : ℕ) : (a⁻¹)^n • v = v :=
    (MulAction.stabilizer H v).pow_mem ((MulAction.stabilizer H v).inv_mem hmem) n
  have hd (n : ℕ) : dist (((a⁻¹)^n * h * a^n) • v) v = dist (h • v) v := by
    rw [MulAction.mul_smul,MulAction.mul_smul,hp]
    nth_rw 2 [← hi n]
    exact (hiso ((a⁻¹)^n)).dist_eq _ _
  have ht : Tendsto (fun n : ℕ => ((a⁻¹)^n * h * a^n) • v) atTop (𝓝 v) := by
    simpa only [one_smul] using hc.smul (tendsto_const_nhds (x := v))
  have hl : Tendsto (fun _n : ℕ => dist (h • v) v) atTop (𝓝 0) := by
    simpa only [hd,dist_self] using ht.dist (tendsto_const_nhds (x := v))
  have hz : dist (h • v) v = 0 := tendsto_nhds_unique tendsto_const_nhds hl
  exact dist_eq_zero.mp hz

open BBEKDynamics
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem lower_fixed_of_psi_fixed {E : Type*} [MetricSpace E]
    [MulAction G E] [ContinuousSMul G E]
    (hiso : ∀ g : G, Isometry (fun w : E => g • w))
    {t : ℝ} (ht : 0 < t) {w : E} (hw : psi t 1 • w = w)
    (u : ℝ) (v : Q2) : x u v • w = w :=
  fixed_of_contracting_conjugates hiso hw (lower_inverse_conjugates_tendsto ht u v)

def transposeG (g : G) : G := (g.1.transpose,g.2.transpose)

theorem transposeG_mul (g h : G) : transposeG (g*h) = transposeG h*transposeG g := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [transposeG,Matrix.transpose_mul]

theorem transposeG_pow (g : G) (n : ℕ) : transposeG (g^n) = (transposeG g)^n := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [transposeG,Matrix.transpose_pow]

@[simp] theorem transposeG_one : transposeG 1 = 1 := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [transposeG]

@[simp] theorem transposeG_psi (t : ℝ) (n : ℤ) : transposeG (psi t n) = psi t n := by
  apply Prod.ext <;> apply Matrix.SpecialLinearGroup.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem transposeG_psi_inv (t : ℝ) (n : ℤ) :
    transposeG ((psi t n)⁻¹) = (psi t n)⁻¹ := by
  rw [← psi_neg,transposeG_psi]

theorem continuous_transposeG : Continuous transposeG := by
  have hr : Continuous (Matrix.SpecialLinearGroup.transpose : SL(2,ℝ) → SL(2,ℝ)) :=
    continuous_subtype_val.matrix_transpose.subtype_mk _
  have hp : Continuous (Matrix.SpecialLinearGroup.transpose : SL(2,Q2) → SL(2,Q2)) :=
    continuous_subtype_val.matrix_transpose.subtype_mk _
  exact (hr.comp continuous_fst).prodMk (hp.comp continuous_snd)

def upperPoint (u : ℝ) (v : Q2) : G :=
  (BBEKFiniteQuotients.upper u,BBEKFiniteQuotients.upper v)

@[simp] theorem transposeG_x (u : ℝ) (v : Q2) : transposeG (x u v) = upperPoint u v := by
  apply Prod.ext <;> apply Matrix.SpecialLinearGroup.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;> rfl

theorem upper_forward_conjugates_tendsto {t : ℝ} (ht : 0 < t) (u : ℝ) (v : Q2) :
    Tendsto (fun k : ℕ => (psi t 1)^k * upperPoint u v * ((psi t 1)⁻¹)^k)
      atTop (𝓝 1) := by
  have h := (continuous_transposeG.tendsto 1).comp (lower_inverse_conjugates_tendsto ht u v)
  change Tendsto (fun k : ℕ => transposeG (((psi t 1)⁻¹)^k * x u v * (psi t 1)^k))
    atTop (𝓝 (transposeG 1)) at h
  simpa only [Function.comp_apply,transposeG_mul,transposeG_pow,transposeG_psi,
    transposeG_psi_inv,transposeG_x,transposeG_one,mul_assoc] using h

theorem upper_fixed_of_psi_fixed {E : Type*} [MetricSpace E]
    [MulAction G E] [ContinuousSMul G E]
    (hiso : ∀ g : G, Isometry (fun w : E => g • w))
    {t : ℝ} (ht : 0 < t) {w : E} (hw : psi t 1 • w = w)
    (u : ℝ) (v : Q2) : upperPoint u v • w = w := by
  have hi : (psi t 1)⁻¹ • w = w := (MulAction.stabilizer G w).inv_mem hw
  apply fixed_of_contracting_conjugates hiso hi
  simpa only [inv_inv] using upper_forward_conjugates_tendsto ht u v

/-- Explicit SL2 generation; no topological or characteristic-zero
assumption is required for this algebraic step. -/
theorem sl_subgroup_eq_top_of_unipotents {K : Type*} [Field K] (H : Subgroup SL(2,K))
    (hu : ∀ u : K, BBEKFiniteQuotients.upper u ∈ H)
    (hl : ∀ u : K, BBEKFiniteQuotients.lower u ∈ H) : H = ⊤ := by
  have hnonzero (g : SL(2,K)) (hc : g 1 0 ≠ 0) : g ∈ H := by
    rw [BBEKFiniteQuotients.factorization g hc]
    exact H.mul_mem (H.mul_mem (hu _) (hl _)) (hu _)
  apply (Subgroup.eq_top_iff' H).mpr
  intro g
  by_cases hc : g 1 0 = 0
  · have hdet : g 0 0 * g 1 1 = 1 := by
      simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using g.property
    have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hs : (BBEKFiniteQuotients.lower (1:K)*g : SL(2,K)) 1 0 ≠ 0 := by
      simpa [BBEKFiniteQuotients.lower,Matrix.mul_apply,Fin.sum_univ_two,hc] using ha
    have hh := H.mul_mem (H.inv_mem (hl 1)) (hnonzero _ hs)
    simpa only [inv_mul_cancel_left] using hh
  · exact hnonzero g hc

theorem group_fixed_of_unipotents {E : Type*} [MulAction G E] {w : E}
    (hl : ∀ u : ℝ, ∀ v : Q2, x u v • w = w)
    (hu : ∀ u : ℝ, ∀ v : Q2, upperPoint u v • w = w) (g : G) : g • w = w := by
  let H := MulAction.stabilizer G w
  have hleft : H.comap (MonoidHom.inl SL(2,ℝ) SL(2,Q2)) = ⊤ := by
    apply sl_subgroup_eq_top_of_unipotents
    · intro u
      change (BBEKFiniteQuotients.upper u,1) • w = w
      simpa only [upperPoint,BBEKFiniteQuotients.upper_zero] using hu u 0
    · intro u
      change (BBEKFiniteQuotients.lower u,1) • w = w
      simpa only [x,BBEKDynamics.lower_zero] using hl u 0
  have hright : H.comap (MonoidHom.inr SL(2,ℝ) SL(2,Q2)) = ⊤ := by
    apply sl_subgroup_eq_top_of_unipotents
    · intro v
      change (1,BBEKFiniteQuotients.upper v) • w = w
      simpa only [upperPoint,BBEKFiniteQuotients.upper_zero] using hu 0 v
    · intro v
      change (1,BBEKFiniteQuotients.lower v) • w = w
      simpa only [x,BBEKDynamics.lower_zero] using hl 0 v
  have h1 : (g.1,1) ∈ H := (Subgroup.eq_top_iff' _).mp hleft g.1
  have h2 : (1,g.2) ∈ H := (Subgroup.eq_top_iff' _).mp hright g.2
  have hh := H.mul_mem h1 h2
  simpa only [Prod.mk_mul_mk,mul_one,one_mul] using hh

/-- For a continuous isometric action of the actual BBEK group,
invariance under one strictly expanding diagonal element implies
invariance under the full group. This supplies the Mautner part of
the Haar-ergodicity argument. -/
theorem group_fixed_of_psi_fixed {E : Type*} [MetricSpace E]
    [MulAction G E] [ContinuousSMul G E]
    (hiso : ∀ g : G, Isometry (fun w : E => g • w))
    {t : ℝ} (ht : 0 < t) {w : E} (hw : psi t 1 • w = w) (g : G) : g • w = w :=
  group_fixed_of_unipotents (lower_fixed_of_psi_fixed hiso ht hw)
    (upper_fixed_of_psi_fixed hiso ht hw) g

end VV.BBEKMautner
