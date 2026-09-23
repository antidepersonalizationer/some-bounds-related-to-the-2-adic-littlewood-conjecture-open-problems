import VV.BBEKLeafAtomDichotomy
import VV.BBEKGlobalLowerCovariance

/-! The atom dichotomy for the actual globally glued joint lower leaves.
The inverse diagonal scaling and its strict contraction are proved here
from the literal real / 2-adic expansion estimates. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Function Metric
open scoped ENNReal Topology

namespace VV.BBEKGlobalLowerAtoms
open BBEKDynamics BBEKQuotient BBEKTopology BBEKLeafwiseKernel
open BBEKGlobalLowerCovariance BBEKLeafAtomDichotomy BBEKEntropyExpansion
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def leafScalingAdd (t : ℝ) (n : ℤ) : Leaf ≃+ Leaf where
  toEquiv := (leafScaling t n).toEquiv
  map_add' u v := by
    apply Prod.ext <;> simp [leafScaling,mul_add]

def inverseLeafScaling (t : ℝ) : Leaf ≃+ Leaf := (leafScalingAdd t 1).symm

theorem expand_inverseLeafScaling (t : ℝ) (u : Leaf) :
    expand t (inverseLeafScaling t u) = u :=
  (leafScaling t 1).apply_symm_apply u

theorem expand_iterate_inverseLeafScaling (t : ℝ) (n : ℕ) (u : Leaf) :
    (expand t)^[n] ((inverseLeafScaling t)^[n] u) = u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply (inverseLeafScaling t),
      Function.iterate_succ_apply' (expand t),ih,expand_inverseLeafScaling]

theorem inverseLeafScaling_iterate_bound {t : ℝ} (ht : Real.log 2 ≤ t)
    (u : Leaf) (n : ℕ) :
    ‖(inverseLeafScaling t)^[n] u‖ ≤ ((4 : ℝ)⁻¹)^n * ‖u‖ := by
  have hb := expand_iterate_norm_lower ht ((inverseLeafScaling t)^[n] u) n
  rw [expand_iterate_inverseLeafScaling] at hb
  have he : ((4 : ℝ)⁻¹)^n * ‖u‖ = ‖u‖ / (4:ℝ)^n := by
    simp only [div_eq_mul_inv,inv_pow,mul_comm]
  rw [he]
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 4^n)).mpr (by simpa only [mul_comm] using hb)

theorem inverseLeafScaling_norm_le {t : ℝ} (ht : Real.log 2 ≤ t) (u : Leaf) :
    ‖inverseLeafScaling t u‖ ≤ ‖u‖ := by
  have h := inverseLeafScaling_iterate_bound ht u 1
  simp only [pow_one,Function.iterate_one] at h
  nlinarith [norm_nonneg u]

theorem inverseLeafScaling_contracts {t : ℝ} (ht : Real.log 2 ≤ t) (u : Leaf) :
    Tendsto (fun n : ℕ => (inverseLeafScaling t)^[n] u) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (inverseLeafScaling_iterate_bound ht u)
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 4⁻¹)
      (by norm_num : (4:ℝ)⁻¹ < 1)).mul_const ‖u‖

theorem normalized_inverse_covariance {μ : Measure X} [IsFiniteMeasure μ]
    {t : ℝ} (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ)
    (η : X → Measure Leaf) {r : ℝ}
    (hcov : ∀ᵐ q ∂μ,
      η (psi t 1 • q) = (((η q).map (leafScaling t 1)) (ball 0 r))⁻¹ •
        (η q).map (leafScaling t 1) ∧
      0 < ((η q).map (leafScaling t 1)) (ball 0 r) ∧
      ((η q).map (leafScaling t 1)) (ball 0 r) ≠ ∞) :
    ∀ᵐ q ∂μ, ∃ d : ℝ≥0∞,
      η ((psi t 1)⁻¹ • q) = d • Measure.map (inverseLeafScaling t) (η q) := by
  filter_upwards [hT.quasiMeasurePreserving.ae hcov] with q hq
  let c := ((η ((psi t 1)⁻¹ • q)).map (leafScaling t 1)) (ball 0 r)
  have hc0 : c ≠ 0 := hq.2.1.ne'
  have hcf : c ≠ ∞ := hq.2.2
  have hEq : η q = c⁻¹ • Measure.map (leafScaling t 1) (η ((psi t 1)⁻¹ • q)) := by
    simpa only [smul_inv_smul] using hq.1
  have hiMeas : Measurable (inverseLeafScaling t) := (leafScaling t 1).symm.measurable
  refine ⟨c,?_⟩
  rw [hEq,Measure.map_smul,Measure.map_map hiMeas
    (leafScaling t 1).measurable]
  have hfun : (inverseLeafScaling t : Leaf → Leaf) ∘ leafScaling t 1 = id :=
    (leafScaling t 1).symm_comp_self
  rw [hfun,Measure.map_id,smul_smul,ENNReal.mul_inv_cancel hc0 hcf,one_smul]

/-- The global lower-leaf family comes from the actual quotient measure,
and satisfies the atom/Dirac dichotomy with no extra leaf-family inputs. -/
theorem exists_global_lower_family_atom_dichotomy (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Leaf, Measurable η ∧
      (∀ᵐ q ∂μ,
        IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
          ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ, η q {0} = 0 ∨ η q = Measure.dirac 0) := by
  obtain ⟨r,hr,η,hη,hgood,hcov⟩ := exists_global_lower_covariant_family μ hK hμK ht hT
  refine ⟨r,hr,η,hη,hgood,?_⟩
  exact ae_zero_atom_or_dirac hT η hη hr
    (hgood.mono fun q hq => hq.2.2.1) (inverseLeafScaling t)
    (leafScaling t 1).symm.measurable (inverseLeafScaling_norm_le ht)
    (inverseLeafScaling_contracts ht) (normalized_inverse_covariance hT η hcov)

end VV.BBEKGlobalLowerAtoms
