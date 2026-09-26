import VV.BBEKOneRootCovariance

/-! Scaling covariance for any fixed actual canonical root family.
This extracts the selected-plaque proof without selecting a new family, so
subsequent recurrence, stabilizer and nonatomicity results refer to one η. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology ENNReal
namespace VV.BBEKCanonicalCovariance
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseAtlas
open BBEKExpandedPlaques BBEKSelectedPlaques BBEKRootGrowingGlue
open BBEKRootLeafKernel BBEKOneRootLocal BBEKOneRootGlobal
open BBEKOneRootSelectedDiagonal BBEKOneRootCovariance BBEKProjectiveGlue

section General
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U] [SigmaCompactSpace U]

omit [NormedAddCommGroup U] [BorelSpace U] [SecondCountableTopology U]
  [StandardBorelSpace U] [SigmaCompactSpace U] in
theorem mass_pos_of_normalized_restriction (ν P : Measure U)
    {B S : Set U} (hB : MeasurableSet B) (hBS : B ⊆ S) (hνB : ν B = 1)
    (he : ν.restrict S = (P B)⁻¹ • P.restrict S) : 0 < P B := by
  have hh := congrArg (fun ξ : Measure U => ξ B) he
  simp only [Measure.restrict_apply hB,inter_eq_self_of_subset_left hBS,
    Measure.smul_apply,smul_eq_mul,hνB] at hh
  by_contra hp
  have hz : P B = 0 := le_antisymm (not_lt.mp hp) (zero_le _)
  simp only [hz,inv_zero,mul_zero] at hh
  exact one_ne_zero hh
theorem canonical_covariance
    (s : GroupParams ≃ₜ B × U) (β : B ≃ₜ B) (σ : U ≃ₜ U)
    (hσ : ∀ u v : U, σ (u-v) = σ u-σ v)
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (hr : 0 < r)
    (hcoords : ∀ p, s (psiParams t 1 p) = Prod.map β σ (s p))
    (hpre : ∀ n : ℕ, σ ⁻¹' growingBall r (n+1) ⊆ growingBall r n)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ)
    (η : X → Measure U) (hn : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hc : IsConstructedRootFamily s μ t r η) :
    ∀ᵐ q ∂μ,
      η (psi t 1 • q) = ((η q).map σ (ball 0 r))⁻¹ • (η q).map σ ∧
      0 < (η q).map σ (ball 0 r) ∧ (η q).map σ (ball 0 r) ≠ ∞ := by
  obtain ⟨c,index,_hi,_he,hres⟩ := hc
  filter_upwards [hres,hA.quasiMeasurePreserving.ae hres,hn,hA.quasiMeasurePreserving.ae hn,
    ae_selectedMeasureWith_succ s β σ hσ μ c index t hcoords hA]
    with q hq haq hnq hnaq hscale
  apply normalized_scaling_of_restrictions hr (η q) (η (psi t 1 • q)) σ hnaq
  intro n
  have hbase (k : ℕ) : ball (0 : U) r ⊆ growingBall r k := by
    simpa only [growingBall,pow_zero,one_mul] using growingBall_mono hr.le (Nat.zero_le k)
  have hp : 0 < selectedMeasureWith s μ c index t n q (ball 0 r) :=
    mass_pos_of_normalized_restriction (η q) _ isOpen_ball.measurableSet (hbase n)
      hnq (hq n).1
  have hp' : 0 < selectedMeasureWith s μ c index t (n+1) (psi t 1 • q) (ball 0 r) :=
    mass_pos_of_normalized_restriction (η (psi t 1 • q)) _ isOpen_ball.measurableSet (hbase (n+1))
      hnaq (haq (n+1)).1
  exact projective_restrict_scaling (η q) (η (psi t 1 • q))
    (selectedMeasureWith s μ c index t n q)
    (selectedMeasureWith s μ c index t (n+1) (psi t 1 • q))
    σ n (hpre n) hp hp' (hscale n (hq n).2.1) (hq n).1 (haq (n+1)).1
end General

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem canonical_real_lower_covariance
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (ht : Real.log 2 ≤ t) (hr : 0 < r)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ)
    (η : X → Measure ℝ) (hn : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hc : IsConstructedRootFamily realSplit μ t r η) :
    ∀ᵐ q ∂μ,
      η (psi t 1 • q) = ((η q).map (realLeafScaling t) (ball 0 r))⁻¹ • (η q).map (realLeafScaling t) ∧
      0 < (η q).map (realLeafScaling t) (ball 0 r) ∧ (η q).map (realLeafScaling t) (ball 0 r) ≠ ∞ :=
  canonical_covariance realSplit (realTransverseScaling t 1) (realLeafScaling t)
    (fun u v => by simp [realLeafScaling,mul_sub]) μ hr (realSplit_psiParams t 1)
    (real_scaling_preimage_growingBall ht) hA η hn hc

theorem canonical_padic_lower_covariance
    (μ : Measure X) [IsFiniteMeasure μ] {t r : ℝ} (hr : 0 < r)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ)
    (η : X → Measure Q2) (hn : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hc : IsConstructedRootFamily padicSplit μ t r η) :
    ∀ᵐ q ∂μ,
      η (psi t 1 • q) = ((η q).map (padicLeafScaling 1) (ball 0 r))⁻¹ • (η q).map (padicLeafScaling 1) ∧
      0 < (η q).map (padicLeafScaling 1) (ball 0 r) ∧ (η q).map (padicLeafScaling 1) (ball 0 r) ≠ ∞ :=
  canonical_covariance padicSplit (padicTransverseScaling t 1) (padicLeafScaling 1)
    (fun u v => by simp [padicLeafScaling,mul_sub]) μ hr (padicSplit_psiParams t 1)
    padic_scaling_preimage_growingBall hA η hn hc

end VV.BBEKCanonicalCovariance



