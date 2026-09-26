import VV.BBEKCanonicalExceptional
import VV.BBEKConditionalLeafFibres
import VV.BBEKUpperRootTranslation

/-! Actual disintegration over the pair of opposite canonical root fields.
The same conditional probabilities are invariant under a contracting time in
the opposite local factor, carry both fields unchanged, and cannot concentrate
on an opposite-root common-centralizer orbit. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology ENNReal MatrixGroups
namespace VV.BBEKPairExceptional
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKRootLeafKernel
open BBEKOneRootCovariance BBEKOneRootUpper BBEKOneRootDiagonalNatural
open BBEKUpperRootTranslation BBEKExceptionalCentralizer BBEKInvariantConditionals
open BBEKCanonicalExceptional BBEKConditionalLeafFibres
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Nonempty X := ⟨basePoint⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩
/-- The literal pair of opposite real root fields has invariant conditionals,
actual equal-field support, and no centralizer-orbit concentration. Different
original normalization radii are permitted and retained. -/
theorem real_pair_conditionals
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure ℝ) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily realSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily realSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular) :
    (∀ᵐ ν ∂μ.map (fun q => (ηlo q,ηup q)),
      MeasurePreserving (fun q : X => psi 0 1 • q)
        (condDistrib id (fun q => (ηlo q,ηup q)) μ ν)
        (condDistrib id (fun q => (ηlo q,ηup q)) μ ν)) ∧
    (∀ᵐ ν ∂μ.map (fun q => (ηlo q,ηup q)), ∀ q : X,
      (condDistrib id (fun q => (ηlo q,ηup q)) μ ν)
        (centralizerOrbit realCommonCentralizer q) ≠ 1) ∧
    (∀ᵐ q ∂μ, ∀ᵐ z ∂condDistrib id (fun q => (ηlo q,ηup q)) μ (ηlo q,ηup q),
      ηlo z = ηlo q ∧ ηup z = ηup q) := by
  have hA : MeasurePreserving (fun q : X => psi 0 1 • q) μ μ :=
    measurePreserving_smul (⟨psi 0 1,psi_mem_A 0 1⟩ : A) μ
  have hiLo := canonical_real_lower_padic_invariant μ 1 hA hrlo ηlo hnlo hclo
  have hiUp := canonical_real_upper_padic_invariant μ 1 hA hrup ηup hnup hcup
  have hi : ∀ᵐ q ∂μ, (ηlo (psi 0 1 • q),ηup (psi 0 1 • q)) = (ηlo q,ηup q) := by
    filter_upwards [hiLo,hiUp] with q hq hq'
    exact Prod.ext hq hq'
  refine ⟨condDistrib_id_measurePreserving μ hA _ (hlo.prodMk hup) hi,?_,
    condDistrib_id_leaf_pair_fibre μ ηlo ηup hlo hup hrglo hrgup⟩
  rw [psi_zero_one] at hA hi
  exact ae_no_real_centralizer_conditional_concentration μ _ (hlo.prodMk hup) hA hi
/-- The literal pair of opposite padic root fields has invariant conditionals,
actual equal-field support, and no centralizer-orbit concentration. Different
original normalization radii are permitted and retained. -/
theorem padic_pair_conditionals
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {tlo tup rlo rup : ℝ} (hrlo : 0 < rlo) (hrup : 0 < rup)
    (ηlo ηup : X → Measure Q2) (hlo : Measurable ηlo) (hup : Measurable ηup)
    (hnlo : ∀ᵐ q ∂μ, ηlo q (ball 0 rlo) = 1)
    (hnup : ∀ᵐ q ∂μ, ηup q (ball 0 rup) = 1)
    (hclo : IsConstructedRootFamily padicSplit μ tlo rlo ηlo)
    (hcup : IsConstructedUpperRootFamily padicSplit μ tup rup ηup)
    (hrglo : ∀ᵐ q ∂μ, (ηlo q).Regular)
    (hrgup : ∀ᵐ q ∂μ, (ηup q).Regular) :
    (∀ᵐ ν ∂μ.map (fun q => (ηlo q,ηup q)),
      MeasurePreserving (fun q : X => psi (Real.log 2) 0 • q)
        (condDistrib id (fun q => (ηlo q,ηup q)) μ ν)
        (condDistrib id (fun q => (ηlo q,ηup q)) μ ν)) ∧
    (∀ᵐ ν ∂μ.map (fun q => (ηlo q,ηup q)), ∀ q : X,
      (condDistrib id (fun q => (ηlo q,ηup q)) μ ν)
        (centralizerOrbit padicCommonCentralizer q) ≠ 1) ∧
    (∀ᵐ q ∂μ, ∀ᵐ z ∂condDistrib id (fun q => (ηlo q,ηup q)) μ (ηlo q,ηup q),
      ηlo z = ηlo q ∧ ηup z = ηup q) := by
  have hA : MeasurePreserving (fun q : X => psi (Real.log 2) 0 • q) μ μ :=
    measurePreserving_smul (⟨psi (Real.log 2) 0,psi_mem_A (Real.log 2) 0⟩ : A) μ
  have hiLo := canonical_padic_lower_real_invariant μ (Real.log 2) hA hrlo ηlo hnlo hclo
  have hiUp := canonical_padic_upper_real_invariant μ (Real.log 2) hA hrup ηup hnup hcup
  have hi : ∀ᵐ q ∂μ, (ηlo (psi (Real.log 2) 0 • q),ηup (psi (Real.log 2) 0 • q)) = (ηlo q,ηup q) := by
    filter_upwards [hiLo,hiUp] with q hq hq'
    exact Prod.ext hq hq'
  refine ⟨condDistrib_id_measurePreserving μ hA _ (hlo.prodMk hup) hi,?_,
    condDistrib_id_leaf_pair_fibre μ ηlo ηup hlo hup hrglo hrgup⟩
  rw [psi_log_two_zero] at hA hi
  exact ae_no_padic_centralizer_conditional_concentration μ _ (hlo.prodMk hup) hA hi
end VV.BBEKPairExceptional
