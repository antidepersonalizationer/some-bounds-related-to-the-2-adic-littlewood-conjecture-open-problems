import VV.BBEKLowEntropyCore
import VV.BBEKRootEscape

/-!
# Internal BBEK Theorem 4.2 and the final Problem 7 theorem

All steps after the single EL low-entropy input are proved here or in the
imported root-escape modules. The final theorems have no external rigidity
parameter; their only unformalized theoretical dependency is the named core.
-/

noncomputable section
open Set MeasureTheory

namespace VV.BBEKFinal
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKMautner
  BBEKMeasureStabilizer BBEKLowEntropyCore BBEKRootEscape
  BBEKEntropyExpansion BBEKPositiveExclusion BBEKReduction
  P7BoxCover ErgodicTheory.Entropy

/-- Full diagonal normalization expands the nonzero root element into its
whole local root group. All four alternatives use proved root algebra. -/
theorem full_root_of_rootAlternative (μ : Measure X)
    [SMulInvariantMeasure A X μ] (hroot : RootAlternative μ) :
    (∀ u : ℝ, x u 0 ∈ measureStabilizer μ) ∨
    (∀ u : ℝ, upperPoint u 0 ∈ measureStabilizer μ) ∨
    (∀ u : Q2, x 0 u ∈ measureStabilizer μ) ∨
    (∀ u : Q2, upperPoint 0 u ∈ measureStabilizer μ) := by
  rcases hroot with ⟨u, hu0, hu⟩ | ⟨u, hu0, hu⟩ | ⟨u, hu0, hu⟩ | ⟨u, hu0, hu⟩
  · exact Or.inl (all_real_lower_mem_of_nonzero μ hu0 hu)
  · exact Or.inr (Or.inl (all_real_upper_mem_of_nonzero μ hu0 hu))
  · exact Or.inr (Or.inr (Or.inl (all_padic_lower_mem_of_nonzero μ hu0 hu)))
  · exact Or.inr (Or.inr (Or.inr (all_padic_upper_mem_of_nonzero μ hu0 hu)))

/-- Any of the four root alternatives contradicts positive Mahler support. -/
theorem no_supported_of_rootAlternative
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hK : μ (BBEKOrbit.K δ) = 1)
    (hroot : RootAlternative μ) : False := by
  rcases full_root_of_rootAlternative μ hroot with hr | hr | hr | hr
  · exact no_supported_of_real_lower_root μ hr hδ hK
  · exact no_supported_of_real_upper_root μ hr hδ hK
  · exact no_supported_of_padic_lower_root μ hr hδ hK
  · exact no_supported_of_padic_upper_root μ hr hδ hK

/-- There is no positive-entropy, full-diagonal ergodic probability
supported on a positive Mahler compact. The reductive exclusion is derived
from these hypotheses, rather than added as another external premise. -/
theorem no_positive_entropy_supported_K
    (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure A X μ] [ErgodicSMul A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hK : μ (BBEKOrbit.K δ) = 1)
    (hμT : MeasurePreserving (timeMap time0) μ μ)
    (hpos : 0 < ksEntropy hμT) : False := by
  have hred := no_proper_reductive_closed_orbit_of_positive μ hδ hK hμT hpos
  exact no_supported_of_rootAlternative μ hδ hK
    (rootAlternative_of_positive_entropy μ hμT hpos hred)

/-- Entropy production and diagonal averaging turn a failure of zero upper
box dimension into the forbidden compactly supported probability. -/
theorem trappedParameters_zero_upper_box (δ : ℝ) (hδ : 0 < δ) :
    GeometricZeroUpperBox (trappedParameters δ) := by
  by_contra hbox
  obtain ⟨ν, hA, hAE, hK, hνT, hpos, hred⟩ :=
    exists_diagonal_positive_with_reductive_exclusion hδ hbox
  letI : SMulInvariantMeasure A X (ν : Measure X) := hA
  letI : ErgodicSMul A X (ν : Measure X) := hAE
  exact no_supported_of_rootAlternative (ν : Measure X) hδ hK
    (rootAlternative_of_positive_entropy (ν : Measure X) hνT hpos hred)

end VV.BBEKFinal

namespace VV

/-- BBEK Theorem 4.2, internally constructed from the one named EL core. -/
theorem bbekTheorem42 : P7BoxCover.BBEKTheorem42 :=
  BBEKReduction.BBEK_of_trapped_zero_box BBEKFinal.trappedParameters_zero_upper_box

/-- The exact Problem 7 statement, with no external assumptions. Its sole
unformalized theoretical dependency is the EL low-entropy core. -/
theorem problem7 : Problem7.Statement :=
  P7BoxCover.problem7_of_BBEK bbekTheorem42

end VV
