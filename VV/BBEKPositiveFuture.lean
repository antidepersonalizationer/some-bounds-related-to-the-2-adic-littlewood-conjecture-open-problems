import VV.BBEKStandardBorel
import VV.BBEKTimeInverse
import VV.Entropy.FutureKernelSupport

/-! The genuine forward and backward time maps both have nontrivial
future conditional measures when the designated time has positive KS
entropy.  These are actual conditional kernels on the quotient. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace VV.BBEKPositiveFuture
open BBEKDynamics BBEKQuotient BBEKTopology BBEKStandardBorel
open BBEKEntropyExpansion BBEKTimeInverse ErgodicTheory.Entropy

theorem positive_future_kernels_both_directions {μ : Measure X} [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (timeMap time0) μ μ) (hpos : 0 < ksEntropy hT) :
    (∃ n : ℕ, ∃ P : MeasurePartition μ (Fin n),
      0 < condEntropy μ (entireFutureSigma hT P) P.cells ∧
      ¬ (∀ᵐ x ∂μ, ∃ y, condExpKernel μ (entireFutureSigma hT P) x = Measure.dirac y)) ∧
    (∃ n : ℕ, ∃ P : MeasurePartition μ (Fin n),
      0 < condEntropy μ (entireFutureSigma (inverseTime_measurePreserving hT) P) P.cells ∧
      ¬ (∀ᵐ x ∂μ, ∃ y,
        condExpKernel μ (entireFutureSigma (inverseTime_measurePreserving hT) P) x = Measure.dirac y)) :=
  ⟨exists_nontrivial_future_kernel_of_pos_ksEntropy hT hpos,
   exists_nontrivial_future_kernel_of_pos_ksEntropy (inverseTime_measurePreserving hT)
    (inverseTime_entropy_pos hT hpos)⟩

end VV.BBEKPositiveFuture
