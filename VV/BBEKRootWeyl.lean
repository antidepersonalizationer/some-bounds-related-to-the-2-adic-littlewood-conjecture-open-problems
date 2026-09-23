import VV.BBEKOneRootGlobal
import VV.BBEKNormalizerOrbit
import VV.BBEKMautner

/-! The actual arithmetic Weyl element exchanges lower and upper roots and
reverses the diagonal flow on the homogeneous quotient. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ENNReal
namespace VV.BBEKRootWeyl
open BBEKDynamics BBEKQuotient BBEKNormalizerOrbit BBEKMautner
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def W : G := (weyl ℝ,weyl Q2)

theorem W_mem_Gamma : W∈Gamma := by
  refine ⟨⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩,?_⟩
  apply Prod.ext <;> apply Matrix.SpecialLinearGroup.ext <;>
    intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalEmbedding,W,weyl,Matrix.SpecialLinearGroup.map]

theorem weyl_conjugate_lower {K : Type*} [Field K] (u : K) :
    weyl K * lower u * (weyl K)⁻¹=BBEKFiniteQuotients.upper (-u) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl,lower,BBEKFiniteQuotients.upper,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

theorem weyl_conjugate_diagonal {K : Type*} [Field K] (a : K) (ha : a≠0) :
    weyl K * diagonal a ha * (weyl K)⁻¹=(diagonal a ha)⁻¹ := by
  rw [diagonal_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl,BBEKDynamics.diagonal,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

theorem W_conjugate_lower (u : ℝ) (v : Q2) :
    W*x u v*W⁻¹=upperPoint (-u) (-v) := by
  exact Prod.ext (weyl_conjugate_lower u) (weyl_conjugate_lower v)

theorem W_conjugate_psi (t : ℝ) (n : ℤ) :
    W*psi t n*W⁻¹=(psi t n)⁻¹ := by
  exact Prod.ext (weyl_conjugate_diagonal _ (Real.exp_ne_zero _))
    (weyl_conjugate_diagonal _ (zpow_ne_zero _ (by norm_num : (2 : Q2)≠0)))

theorem inverse_W_upper (u : ℝ) (v : Q2) :
    W⁻¹*upperPoint u v*W=x (-u) (-v) := by
  have h := W_conjugate_lower (-u) (-v)
  simp only [neg_neg] at h
  rw [← h]
  group

theorem inverse_W_upper_action (u : ℝ) (v : Q2) (q : X) :
    W⁻¹ • (upperPoint u v • q)=x (-u) (-v) • (W⁻¹ • q) := by
  rw [← mul_smul,← mul_smul]
  congr 1
  rw [← inverse_W_upper]
  group

theorem inverse_W_psi_action (t : ℝ) (n : ℤ) (q : X) :
    W⁻¹ • (psi t n • q)=(psi t n)⁻¹ • (W⁻¹ • q) := by
  rw [← mul_smul,← mul_smul]
  congr 1
  have hh := W_conjugate_psi (-t) (-n)
  rw [psi_neg,inv_inv] at hh
  calc
    W⁻¹*psi t n=W⁻¹*(W*(psi t n)⁻¹*W⁻¹) := congrArg (W⁻¹*·) hh.symm
    _ = (psi t n)⁻¹*W⁻¹ := by group

def reflectedMeasure (μ : Measure X) : Measure X :=
  μ.map (fun q : X => W⁻¹ • q)

instance reflectedMeasure_probability (μ : Measure X) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (reflectedMeasure μ) :=
  isProbabilityMeasure_map (continuous_const_smul W⁻¹).measurable.aemeasurable

theorem reflectedMeasure_inverse_invariant (μ : Measure X) (t : ℝ) (n : ℤ)
    (hA : MeasurePreserving (fun q : X => psi t n • q) μ μ) :
    MeasurePreserving (fun q : X => (psi t n)⁻¹ • q)
      (reflectedMeasure μ) (reflectedMeasure μ) := by
  refine ⟨(continuous_const_smul _).measurable,?_⟩
  unfold reflectedMeasure
  rw [Measure.map_map (continuous_const_smul _).measurable (continuous_const_smul _).measurable]
  have he : (fun q : X => (psi t n)⁻¹ • q) ∘ (fun q : X => W⁻¹ • q)=
      (fun q : X => W⁻¹ • q) ∘ (fun q : X => psi t n • q) := by
    funext q
    exact (inverse_W_psi_action t n q).symm
  rw [he,← Measure.map_map (continuous_const_smul _).measurable hA.measurable,hA.map_eq]

theorem reflectedMeasure_compact_mass (μ : Measure X) {K : Set X}
    (hK : IsCompact K) (hμK : μ K=1) :
    IsCompact ((fun q : X => W⁻¹ • q) '' K) ∧
      reflectedMeasure μ ((fun q : X => W⁻¹ • q) '' K)=1 := by
  have hc := hK.image (continuous_const_smul W⁻¹)
  refine ⟨hc,?_⟩
  unfold reflectedMeasure
  rw [Measure.map_apply (continuous_const_smul _).measurable hc.measurableSet,
    Set.preimage_image_eq _ (MulAction.injective W⁻¹),hμK]

end VV.BBEKRootWeyl
