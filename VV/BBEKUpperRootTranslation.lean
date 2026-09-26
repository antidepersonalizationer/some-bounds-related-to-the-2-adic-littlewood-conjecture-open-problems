import VV.BBEKOneRootDiagonalNatural
import VV.BBEKOneRootUpper

/-! Weyl transport of strong leaf covariance and transverse diagonal invariance.
The exceptional sets remain independent of the root translation parameter. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal
namespace VV.BBEKUpperRootTranslation
open BBEKDynamics BBEKQuotient BBEKRootWeyl BBEKOneRootUpper
open BBEKOneRootCovariance BBEKLeafwiseStabilizer BBEKOneRootTranslation
open BBEKRootLeafKernel BBEKOneRootDiagonalNatural
open BBEKNormalizerOrbit BBEKMautner

section General
variable {U : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]

theorem negateMeasure_translate (ν : Measure U) (u : U) :
    negateMeasure (translate u ν) = translate (-u) (negateMeasure ν) := by
  unfold negateMeasure translate
  rw [Measure.map_map (show Measurable (fun v : U => -v) from measurable_neg)
      (show Measurable (fun v : U => u+v) from (continuous_const.add continuous_id).measurable),
    Measure.map_map (show Measurable (fun v : U => -u+v) from (continuous_const.add continuous_id).measurable)
      (show Measurable (fun v : U => -v) from measurable_neg)]
  congr 1
  funext v
  simp [add_comm]

theorem lower_normal_of_upper_normal (μ : Measure X) (η : X → Measure U) (r : ℝ)
    (hn : ∀ᵐ q ∂μ, upperFamily η q (ball 0 r) = 1) :
    ∀ᵐ q ∂reflectedMeasure μ, η q (ball 0 r) = 1 := by
  apply (Homeomorph.smul (W⁻¹ : G)).measurableEmbedding.ae_map_iff.mpr
  simpa only [upperFamily,negateMeasure_ball] using hn

theorem upper_translation_on_conull_set (μ : Measure X) (η : X → Measure U) (r : ℝ)
    (lowerRoot upperRoot : U → G)
    (hW : ∀ (u : U) (q : X), W⁻¹ • (upperRoot u • q) = lowerRoot (-u) • (W⁻¹ • q))
    (hcov : ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂reflectedMeasure μ, q ∈ S) ∧
      ∀ q ∈ S, ∀ u : U, lowerRoot u • q ∈ S →
        η (lowerRoot u • q) = ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
        0 < (translate (-u) (η q)) (ball 0 r) ∧
        (translate (-u) (η q)) (ball 0 r) ≠ ∞) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      ∀ q ∈ S, ∀ u : U, upperRoot u • q ∈ S →
        upperFamily η (upperRoot u • q) =
          ((translate (-u) (upperFamily η q)) (ball 0 r))⁻¹ • translate (-u) (upperFamily η q) ∧
        0 < (translate (-u) (upperFamily η q)) (ball 0 r) ∧
        (translate (-u) (upperFamily η q)) (ball 0 r) ≠ ∞ := by
  obtain ⟨S,hS,hμS,hcov⟩ := hcov
  refine ⟨(fun q : X => W⁻¹ • q) ⁻¹' S,
    hS.preimage (continuous_const_smul W⁻¹).measurable,
    ae_of_ae_map (continuous_const_smul W⁻¹).measurable.aemeasurable hμS,?_⟩
  intro q hq u hu
  have hc := hcov (W⁻¹ • q) hq (-u) (by simpa only [mem_preimage,hW] using hu)
  simp only [neg_neg] at hc
  have he : translate (-u) (upperFamily η q) = negateMeasure (translate u (η (W⁻¹ • q))) :=
    (negateMeasure_translate _ u).symm
  rw [he,negateMeasure_ball]
  refine ⟨?_,hc.2.1,hc.2.2⟩
  change negateMeasure (η (W⁻¹ • (upperRoot u • q))) = _
  rw [hW,hc.1,negateMeasure_smul]

omit [BorelSpace U] in
theorem upper_invariant_of_lower_inverse (μ : Measure X) (η : X → Measure U)
    (a : ℝ) (m : ℤ)
    (hi : ∀ᵐ q ∂reflectedMeasure μ, η (psi (-a) (-m) • q) = η q) :
    ∀ᵐ q ∂μ, upperFamily η (psi a m • q) = upperFamily η q := by
  have h := ae_of_ae_map (continuous_const_smul W⁻¹).measurable.aemeasurable hi
  filter_upwards [h] with q hq
  simp only [upperFamily,inverse_W_psi_action,← psi_neg,hq]
end General

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem canonical_real_upper_translation_on_conull_set
    (μ : Measure X) [IsProbabilityMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure ℝ) (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedUpperRootFamily realSplit μ t r η) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      ∀ q ∈ S, ∀ u : ℝ, upperPoint u 0 • q ∈ S →
      η (upperPoint u 0 • q) = ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
      0 < (translate (-u) (η q)) (ball 0 r) ∧
      (translate (-u) (η q)) (ball 0 r) ≠ ∞ := by
  obtain ⟨η₀,hη₀,rfl⟩ := hcanonical
  exact upper_translation_on_conull_set μ η₀ r (fun u => x u 0) (fun u => upperPoint u 0)
    (by intro u q; simpa only [neg_zero] using inverse_W_upper_action u 0 q)
    (canonical_real_lower_translation_on_conull_set (reflectedMeasure μ) hr η₀
      (lower_normal_of_upper_normal μ η₀ r hnormal) hη₀)

theorem canonical_padic_upper_translation_on_conull_set
    (μ : Measure X) [IsProbabilityMeasure μ] {t r : ℝ} (hr : 0 < r)
    (η : X → Measure Q2) (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedUpperRootFamily padicSplit μ t r η) :
    ∃ S : Set X, MeasurableSet S ∧ (∀ᵐ q ∂μ, q ∈ S) ∧
      ∀ q ∈ S, ∀ u : Q2, upperPoint 0 u • q ∈ S →
      η (upperPoint 0 u • q) = ((translate (-u) (η q)) (ball 0 r))⁻¹ • translate (-u) (η q) ∧
      0 < (translate (-u) (η q)) (ball 0 r) ∧
      (translate (-u) (η q)) (ball 0 r) ≠ ∞ := by
  obtain ⟨η₀,hη₀,rfl⟩ := hcanonical
  exact upper_translation_on_conull_set μ η₀ r (fun u => x 0 u) (fun u => upperPoint 0 u)
    (by intro u q; simpa only [neg_zero] using inverse_W_upper_action 0 u q)
    (canonical_padic_lower_translation_on_conull_set (reflectedMeasure μ) hr η₀
      (lower_normal_of_upper_normal μ η₀ r hnormal) hη₀)

theorem canonical_real_upper_padic_invariant
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℤ)
    (hA : MeasurePreserving (fun q : X => psi 0 n • q) μ μ)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedUpperRootFamily realSplit μ t r η) :
    ∀ᵐ q ∂μ, η (psi 0 n • q) = η q := by
  obtain ⟨η₀,hη₀,rfl⟩ := hcanonical
  apply upper_invariant_of_lower_inverse
  simp only [neg_zero]
  apply canonical_real_lower_padic_invariant (reflectedMeasure μ) (-n)
    (by have he := psi_neg 0 n
        simp only [neg_zero] at he
        simpa only [he] using reflectedMeasure_inverse_invariant μ 0 n hA)
    hr η₀ (lower_normal_of_upper_normal μ η₀ r hnormal) hη₀

theorem canonical_padic_upper_real_invariant
    (μ : Measure X) [IsProbabilityMeasure μ] (a : ℝ)
    (hA : MeasurePreserving (fun q : X => psi a 0 • q) μ μ)
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedUpperRootFamily padicSplit μ t r η) :
    ∀ᵐ q ∂μ, η (psi a 0 • q) = η q := by
  obtain ⟨η₀,hη₀,rfl⟩ := hcanonical
  apply upper_invariant_of_lower_inverse
  simp only [neg_zero]
  apply canonical_padic_lower_real_invariant (reflectedMeasure μ) (-a)
    (by have he := psi_neg a 0
        simp only [neg_zero] at he
        simpa only [he] using reflectedMeasure_inverse_invariant μ a 0 hA)
    hr η₀ (lower_normal_of_upper_normal μ η₀ r hnormal) hη₀

end VV.BBEKUpperRootTranslation
