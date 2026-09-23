import VV.BBEKCompactEntropy
import VV.BBEKErgodicPositive

/-! The complete positive-entropy measure construction used before the
Einsiedler--Lindenstrauss classification: full split-diagonal invariance and
ergodicity, positive designated entropy, and actual compact support. -/

noncomputable section
open Set MeasureTheory

namespace VV.BBEKPositiveFullDiagonal
open BBEKDynamics BBEKQuotient BBEKTopology BBEKReduction P7BoxCover
open BBEKEntropyNets BBEKEntropyTrapped BBEKEntropyExpansion BBEKDiagonal BBEKDiagonalAverage
open BBEKConeAverage BBEKCompactPreservation BBEKCompactEntropy BBEKErgodicPositive
open ErgodicTheory.Entropy

local instance : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

/-- Every failure of zero box dimension gives an actual full-diagonal ergodic
probability with positive entropy and mass one on the literal compact Kδ.
No rigidity/classification assertion is a hypothesis of this construction. -/
theorem exists_diagonal_ergodic_pos_ksEntropy_supported_K {δ : ℝ} (hδ : 0 < δ)
    (hbox : ¬ GeometricZeroUpperBox (trappedParameters δ)) :
    ∃ ν : ProbabilityMeasure X,
      ∃ _hA : SMulInvariantMeasure A X (ν : Measure X),
      ErgodicSMul A X (ν : Measure X) ∧
      (ν : Measure X) (BBEKOrbit.K δ) = 1 ∧
      ∃ hνT : MeasurePreserving (timeMap time0) (ν : Measure X) (ν : Measure X),
        0 < ksEntropy hνT := by
  obtain ⟨μ,hμT,hpos,hH,hErg,hK⟩ := exists_trapped_psi_ergodic_pos_ksEntropy hδ hbox
  letI : SMulInvariantMeasure H X (toQuotient δ μ : Measure X) := hH
  letI : ErgodicSMul H X (toQuotient δ μ : Measure X) := hErg
  let ν : ProbabilityMeasure X := ⟨averaged (toQuotient δ μ : Measure X), inferInstance⟩
  have hA : SMulInvariantMeasure A X (ν : Measure X) :=
    averaged_diagonal_invariant (toQuotient δ μ : Measure X)
  have hAE : ErgodicSMul A X (ν : Measure X) :=
    averaged_diagonal_ergodic (toQuotient δ μ : Measure X)
  have hνK : (ν : Measure X) (BBEKOrbit.K δ) = 1 := by
    change BBEKMeasureAverage.average BBEKMeasureAverage.haarProbability
      (toQuotient δ μ : Measure X) (BBEKOrbit.K δ) = 1
    rw [BBEKMeasureAverage.average_apply_of_invariant_set _ _
      (BBEKOrbit.isClosed_K δ).measurableSet (fun k => compact_preimage_K k δ)]
    exact hK
  obtain ⟨hνT,hge⟩ := ksEntropy_le_averaged hδ μ hμT
  exact ⟨ν,hA,hAE,hνK,hνT,hpos.trans_le hge⟩

end VV.BBEKPositiveFullDiagonal
