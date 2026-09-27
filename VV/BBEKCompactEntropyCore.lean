import VV.BBEKMahler
import VV.BBEKTopology
import VV.BBEKDiagonal
import VV.BBEKEntropyExpansion
import VV.Entropy.KSEntropySystem
import Mathlib.Dynamics.Ergodic.Action.Basic

/-! The sole theoretical admission in the shortened Problem 7 route.
This is the compact-support consequence of EL needed by this application.
It is NOT proved by the repository split. Leafwise entropy, actual leaf-return
estimates and their assembly remain unfinished in the companion theory project.
Entropy production, Mahler compactness, Proposition 5.1 and the dimension
reductions are outside this admission. -/
noncomputable section
open MeasureTheory
namespace VV.BBEKCompactEntropyCore
open BBEKQuotient BBEKDiagonal BBEKDynamics BBEKEntropyExpansion
open ErgodicTheory.Entropy
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- UNPROVED EL CONSEQUENCE: no positive-entropy full-diagonal ergodic
probability can give mass one to a positive Mahler compact. -/
theorem no_positive_entropy_supported_K
    (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure A X μ] [ErgodicSMul A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hK : μ (BBEKOrbit.K δ) = 1)
    (hμT : MeasurePreserving (timeMap time0) μ μ)
    (hpos : 0 < ksEntropy hμT) : False := by
  sorry
end VV.BBEKCompactEntropyCore
