import VV.BBEKOneRootLocalDiagonal
import VV.BBEKOneRootGlobal
import VV.BBEKSelectedDiagonal

/-! Exact scaling of successive selected separate-root local probabilities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace VV.BBEKOneRootSelectedDiagonal
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKLeafwiseKernel
  BBEKLeafwiseAtlas BBEKExpandedPlaques BBEKSelectedPlaques BBEKSelectedDiagonal
  BBEKRootLeafKernel BBEKOneRootLocal BBEKOneRootGlobal BBEKOneRootLocalDiagonal

variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U] [SigmaCompactSpace U]

theorem ae_selectedMeasureWith_succ
    (s : GroupParams ≃ₜ B × U) (β : B ≃ₜ B) (σ : U ≃ₜ U)
    (hσ : ∀ u v : U, σ (u-v)=σ u-σ v)
    (μ : Measure X) [IsFiniteMeasure μ] (c : ℕ → Chart) (index : X → ℕ) (t : ℝ)
    (hcoords : ∀ p : GroupParams, s (psiParams t 1 p)=Prod.map β σ (s p))
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∀ᵐ q ∂μ, ∀ n : ℕ, q ∈ (selectedChart c index t n q).image →
      selectedMeasureWith s μ c index t (n+1) (psi t 1 • q)=
        (selectedMeasureWith s μ c index t n q).map σ := by
  have hall : ∀ᵐ q ∂μ, ∀ n k : ℕ, q ∈ (expandedChart (c k) t n).image →
      localMeasureWith s μ (translateChart (expandedChart (c k) t n) t 1) (psi t 1 • q)=
        (localMeasureWith s μ (expandedChart (c k) t n) q).map σ := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact (ae_restrict_iff' (expandedChart (c k) t n).isOpen_image.measurableSet).mp
      (ae_localMeasureWith_translate s β σ hσ μ _ t 1 hcoords hA)
  filter_upwards [hall] with q hq n hn
  unfold selectedMeasureWith
  rw [selectedChart_succ]
  exact hq n (index (((psi t 1)⁻¹)^n • q)) hn

theorem ae_real_selectedMeasure_succ (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) (index : X → ℕ) (t : ℝ)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∀ᵐ q ∂μ, ∀ n : ℕ, q ∈ (selectedChart c index t n q).image →
      selectedMeasureWith realSplit μ c index t (n+1) (psi t 1 • q)=
        (selectedMeasureWith realSplit μ c index t n q).map (realLeafScaling t) :=
  ae_selectedMeasureWith_succ realSplit (realTransverseScaling t 1) (realLeafScaling t)
    (fun u v => by simp [realLeafScaling,mul_sub]) μ c index t (realSplit_psiParams t 1) hA

theorem ae_padic_selectedMeasure_succ (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℕ → Chart) (index : X → ℕ) (t : ℝ)
    (hA : MeasurePreserving (fun q : X => psi t 1 • q) μ μ) :
    ∀ᵐ q ∂μ, ∀ n : ℕ, q ∈ (selectedChart c index t n q).image →
      selectedMeasureWith padicSplit μ c index t (n+1) (psi t 1 • q)=
        (selectedMeasureWith padicSplit μ c index t n q).map (padicLeafScaling 1) :=
  ae_selectedMeasureWith_succ padicSplit (padicTransverseScaling t 1) (padicLeafScaling 1)
    (fun u v => by simp [padicLeafScaling,mul_sub]) μ c index t (padicSplit_psiParams t 1) hA

end VV.BBEKOneRootSelectedDiagonal
