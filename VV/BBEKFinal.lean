import VV.BBEKCompactEntropyCore
import VV.BBEKPositiveFullDiagonal

/-! Shortened application route. Exactly the compact entropy exclusion is
admitted; no general reductive-orbit or root-classification premise is used. -/
noncomputable section
open MeasureTheory
namespace VV.BBEKFinal
open BBEKQuotient BBEKDiagonal BBEKReduction P7BoxCover
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩
theorem trappedParameters_zero_upper_box (δ : ℝ) (hδ : 0 < δ) :
    GeometricZeroUpperBox (trappedParameters δ) := by
  by_contra hbox
  obtain ⟨ν,hA,hE,hK,hT,hpos⟩ :=
    BBEKPositiveFullDiagonal.exists_diagonal_ergodic_pos_ksEntropy_supported_K hδ hbox
  letI : SMulInvariantMeasure A X (ν : Measure X) := hA
  letI : ErgodicSMul A X (ν : Measure X) := hE
  exact BBEKCompactEntropyCore.no_positive_entropy_supported_K
    (ν : Measure X) hδ hK hT hpos
end VV.BBEKFinal
namespace VV
theorem bbekTheorem42 : P7BoxCover.BBEKTheorem42 :=
  BBEKReduction.BBEK_of_trapped_zero_box BBEKFinal.trappedParameters_zero_upper_box
theorem problem7 : Problem7.Statement :=
  P7BoxCover.problem7_of_BBEK bbekTheorem42
end VV
