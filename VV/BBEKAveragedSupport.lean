import VV.BBEKTopology
import VV.BBEKDiagonalAverage
import VV.BBEKCompactPreservation
import VV.BBEKHomogeneousErgodic

/-! Compact averaging preserves confinement to the actual proper Mahler set.
Consequently that average cannot be invariant under the full group. -/

noncomputable section
open MeasureTheory

namespace VV.BBEKAveragedSupport
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKDiagonalAverage
open BBEKTopology BBEKCompactPreservation BBEKMeasureAverage
local instance : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩

theorem averaged_K_mass (μ : Measure X) [IsProbabilityMeasure μ] (δ : ℝ) :
    averaged μ (BBEKOrbit.K δ) = μ (BBEKOrbit.K δ) :=
  average_apply_of_invariant_set _ μ (BBEKOrbit.isClosed_K δ).measurableSet
    (fun k => compact_preimage_K k δ)

/-- This is the geometric contradiction needed after positive-entropy
classification. The classification itself is not an assumption of this lemma. -/
theorem averaged_not_group_invariant (μ : Measure X) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) (hμ : μ (BBEKOrbit.K δ) = 1) :
    ¬ SMulInvariantMeasure G X (averaged μ) := by
  intro hi
  letI := hi
  exact BBEKHomogeneousErgodic.invariant_probability_K_ne_one (averaged μ) hδ
    ((averaged_K_mass μ δ).trans hμ)

end VV.BBEKAveragedSupport
