import VV.BBEKPsiEntropy
import VV.BBEKEntropyExpansion
import VV.Entropy.KSEntropyInverse

/-!
# The inverse of the designated BBEK time map

The positive-entropy construction uses `timeMap time0`.  Here it is packaged as an actual
measurable equivalence, and entropy invariance under time reversal is specialized to that map.
-/

noncomputable section
open MeasureTheory

namespace VV.BBEKTimeInverse
open BBEKDynamics BBEKQuotient BBEKTopology BBEKEntropyExpansion BBEKPsiEntropy
open ErgodicTheory.Entropy

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The designated time map as a measurable equivalence. -/
def timeEquiv : X ≃ᵐ X := (psiAction time0 1).toMeasurableEquiv

@[simp] theorem timeEquiv_apply (q : X) : timeEquiv q = timeMap time0 q := rfl

@[simp] theorem timeEquiv_symm_apply (q : X) :
    timeEquiv.symm q = psi (-time0) (-1) • q := by
  change (psi time0 1)⁻¹ • q = psi (-time0) (-1) • q
  rw [psi_neg]

/-- A proof of invariance for the function presentation is also a proof of invariance for the
measurable-equivalence presentation. -/
def timeEquiv_measurePreserving {μ : Measure X}
    (hT : MeasurePreserving (timeMap time0) μ μ) :
    MeasurePreserving timeEquiv μ μ := by
  simpa only [timeEquiv_apply] using hT

/-- The inverse designated time is measure-preserving. -/
def inverseTime_measurePreserving {μ : Measure X}
    (hT : MeasurePreserving (timeMap time0) μ μ) :
    MeasurePreserving timeEquiv.symm μ μ :=
  (timeEquiv_measurePreserving hT).symm timeEquiv

/-- The designated forward and backward time maps have exactly the same system entropy. -/
theorem ksEntropy_inverseTime {μ : Measure X} [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (timeMap time0) μ μ) :
    ksEntropy (inverseTime_measurePreserving hT) = ksEntropy hT := by
  have h := ksEntropy_measurableEquiv_symm timeEquiv (timeEquiv_measurePreserving hT)
  simpa only [proof_irrel_heq] using h.symm

/-- Positive entropy therefore persists in the opposite time direction. -/
theorem inverseTime_entropy_pos {μ : Measure X} [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (timeMap time0) μ μ) (hpos : 0 < ksEntropy hT) :
    0 < ksEntropy (inverseTime_measurePreserving hT) := by
  rwa [ksEntropy_inverseTime hT]

end VV.BBEKTimeInverse
