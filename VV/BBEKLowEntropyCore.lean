import VV.BBEKPositiveExclusion
import VV.BBEKMeasureStabilizer

/-!
# The single unformalized EL low-entropy input

This is the specialized root-invariance consequence of the
Einsiedler–Lindenstrauss theorem used in BBEK, Section 5 (Theorem EL).
The one admitted proof comprises the leafwise conditional-measure entropy
argument, low-entropy shearing, and removal of the exceptional alternative
using `NoProperReductiveClosedOrbit`.

The conclusion is only one nonzero root element preserving the measure.
Root-group generation, Mahler escape, entropy production and averaging,
the zero-box-dimension conversion, and Problem 7 are proved in other files.
No claim of a complete formalization of EL or Ratner–Tomanov is made.
-/

noncomputable section
open MeasureTheory

namespace VV.BBEKLowEntropyCore
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKMautner
  BBEKMeasureStabilizer BBEKEntropyExpansion BBEKPositiveExclusion
  ErgodicTheory.Entropy

/-- One nonzero upper or lower root element in either local factor fixes μ. -/
def RootAlternative (μ : Measure X) : Prop :=
  (∃ u : ℝ, u ≠ 0 ∧ x u 0 ∈ measureStabilizer μ) ∨
  (∃ u : ℝ, u ≠ 0 ∧ upperPoint u 0 ∈ measureStabilizer μ) ∨
  (∃ u : Q2, u ≠ 0 ∧ x 0 u ∈ measureStabilizer μ) ∨
  (∃ u : Q2, u ≠ 0 ∧ upperPoint 0 u ∈ measureStabilizer μ)

/-- The sole admitted theoretical input. It concerns the literal arithmetic
quotient and full split diagonal, with positive entropy at the designated
time and the already separately formalized reductive-orbit exclusion. -/
theorem rootAlternative_of_positive_entropy
    (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure A X μ] [ErgodicSMul A X μ]
    (hμT : MeasurePreserving (timeMap time0) μ μ)
    (hpos : 0 < ksEntropy hμT)
    (hred : NoProperReductiveClosedOrbit μ) : RootAlternative μ := by
  sorry

end VV.BBEKLowEntropyCore
