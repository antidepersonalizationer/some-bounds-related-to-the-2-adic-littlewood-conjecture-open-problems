import VV.BBEKInvariantConditionals
import VV.BBEKOneRootDiagonalNatural
import VV.BBEKDiagonal

/-! Exclusion of the centralizer-concentration alternative for the literal
conditional probabilities over the actual canonical root-measure field.
Invariance of that field and of its conditional probabilities is proved from
the original full-diagonal-invariant measure, not supplied as a new premise.
This module does not assert the deep EL dichotomy producing this alternative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology ENNReal MatrixGroups
namespace VV.BBEKCanonicalExceptional
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKRootLeafKernel
open BBEKOneRootCovariance BBEKOneRootDiagonalNatural
open BBEKExceptionalCentralizer BBEKInvariantConditionals
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Nonempty X := ⟨basePoint⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

theorem psi_zero_one : psi 0 1 = ((1 : SL(2,ℝ)),diagonal (2 : Q2) (by norm_num)) := by
  simp [psi]

theorem psi_log_two_zero : psi (Real.log 2) 0 =
    (diagonal (1/2 : ℝ) (by norm_num),(1 : SL(2,Q2))) := by
  have he : Real.exp (-Real.log 2) = (1/2 : ℝ) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  simp [psi,he]

/-- Every fixed canonical real lower-root field has conditionals which
almost surely cannot concentrate on a common-centralizer orbit. -/
theorem real_lower_no_exceptional_conditionals
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {t r : ℝ} (hr : 0 < r) (η : X → Measure ℝ) (hη : Measurable η)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily realSplit μ t r η) :
    ∀ᵐ ν ∂μ.map η, ∀ q : X,
      (condDistrib id η μ ν) (centralizerOrbit realCommonCentralizer q) ≠ 1 := by
  have hA : MeasurePreserving (fun q : X => psi 0 1 • q) μ μ :=
    measurePreserving_smul (⟨psi 0 1,psi_mem_A 0 1⟩ : A) μ
  have hi := canonical_real_lower_padic_invariant μ 1 hA hr η hnormal hcanonical
  rw [psi_zero_one] at hA hi
  exact ae_no_real_centralizer_conditional_concentration μ η hη hA hi

/-- The symmetric literal 2-adic lower-root conditional exclusion. -/
theorem padic_lower_no_exceptional_conditionals
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {t r : ℝ} (hr : 0 < r) (η : X → Measure Q2) (hη : Measurable η)
    (hnormal : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (hcanonical : IsConstructedRootFamily padicSplit μ t r η) :
    ∀ᵐ ν ∂μ.map η, ∀ q : X,
      (condDistrib id η μ ν) (centralizerOrbit padicCommonCentralizer q) ≠ 1 := by
  have hA : MeasurePreserving (fun q : X => psi (Real.log 2) 0 • q) μ μ :=
    measurePreserving_smul (⟨psi (Real.log 2) 0,psi_mem_A (Real.log 2) 0⟩ : A) μ
  have hi := canonical_padic_lower_real_invariant μ (Real.log 2) hA hr η hnormal hcanonical
  rw [psi_log_two_zero] at hA hi
  exact ae_no_padic_centralizer_conditional_concentration μ η hη hA hi

end VV.BBEKCanonicalExceptional
