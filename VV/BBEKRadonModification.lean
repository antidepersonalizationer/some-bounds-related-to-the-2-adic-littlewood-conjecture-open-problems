import VV.BBEKCompactZeroHit

/-! A measurable null-set modification makes the actual lower-leaf family
Radon and normalized at every point, preserving its a.e. diagonal covariance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal
namespace VV.BBEKRadonModification
open BBEKDynamics BBEKQuotient BBEKLeafwiseKernel BBEKGlobalLowerCovariance

/-- A measurable envelope of the exceptional null set gives an everywhere
good version without assuming that the good-value predicate is measurable. -/
theorem exists_everywhere_good_ae_eq {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]
    (μ : Measure Z) (f : Z → V) (hf : Measurable f) (P : V → Prop)
    (hg : ∀ᵐ z ∂μ, P (f z)) (v₀ : V) (hv₀ : P v₀) :
    ∃ g : Z → V, Measurable g ∧ g =ᵐ[μ] f ∧ ∀ z, P (g z) := by
  classical
  let N := {z | ¬P (f z)}
  let S := toMeasurable μ N
  have hS : MeasurableSet S := measurableSet_toMeasurable μ N
  have hN : μ N = 0 := ae_iff.mp hg
  have hSzero : μ S = 0 := by rw [measure_toMeasurable,hN]
  let g : Z → V := S.piecewise (fun _ => v₀) f
  have hae : ∀ᵐ z ∂μ, z ∉ S := by
    apply ae_iff.mpr
    simpa only [not_not,mem_setOf_eq] using hSzero
  refine ⟨g,measurable_const.piecewise hS hf,?_,?_⟩
  · filter_upwards [hae] with z hz
    exact piecewise_eq_of_notMem S _ _ hz
  · intro z
    by_cases hz : z ∈ S
    · simpa only [g,piecewise_eq_of_mem S _ _ hz] using hv₀
    · rw [show g z = f z from piecewise_eq_of_notMem S _ _ hz]
      by_contra hbad
      exact hz (subset_toMeasurable μ N hbad)

/-- A version of the genuine full lower-leaf family with everywhere Radon,
normalization and support-at-zero properties. Its a.e. covariance survives
because the diagonal transformation preserves the original probability. -/
theorem exists_everywhere_Radon_covariant_family (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμK : μ K = 1)
    {t : ℝ} (ht : Real.log 2 ≤ t)
    (hT : MeasurePreserving (fun q : X => (psi t 1)⁻¹ • q) μ μ) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : X → Measure Leaf, Measurable η ∧
      (∀ q : X, IsLocallyFiniteMeasure (η q) ∧ (η q).Regular ∧ η q (ball 0 r) = 1 ∧
          ∀ ε : ℝ, 0 < ε → 0 < η q (ball 0 ε)) ∧
      (∀ᵐ q ∂μ,
        η (psi t 1 • q) = (((η q).map (leafScaling t 1)) (ball 0 r))⁻¹ •
          (η q).map (leafScaling t 1) ∧
        0 < ((η q).map (leafScaling t 1)) (ball 0 r) ∧
          ((η q).map (leafScaling t 1)) (ball 0 r) ≠ ∞) := by
  obtain ⟨r,hr,η,hη,hgood,hcov⟩ := exists_global_lower_covariant_family μ hK hμK ht hT
  let P : Measure Leaf → Prop := fun ν =>
    IsLocallyFiniteMeasure ν ∧ ν.Regular ∧ ν (ball 0 r) = 1 ∧
      ∀ ε : ℝ, 0 < ε → 0 < ν (ball 0 ε)
  have hP₀ : P (Measure.dirac (0 : Leaf)) := by
    refine ⟨inferInstance,inferInstance,?_,?_⟩
    · simp [Measure.dirac_apply',hr]
    · intro ε hε
      simp [Measure.dirac_apply',hε]
  obtain ⟨θ,hθ,hθη,hP⟩ := exists_everywhere_good_ae_eq μ η hη P hgood (Measure.dirac 0) hP₀
  have hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ := by
    have hh := hT.symm ((Homeomorph.smul ((psi t 1)⁻¹)).toMeasurableEquiv)
    change MeasurePreserving (fun q : X => ((psi t 1)⁻¹)⁻¹ • q) μ μ at hh
    simpa only [inv_inv] using hh
  refine ⟨r,hr,θ,hθ,hP,?_⟩
  filter_upwards [hcov,hθη,hA.quasiMeasurePreserving.ae hθη] with q hc he heA
  rw [he,heA]
  exact hc

end VV.BBEKRadonModification
