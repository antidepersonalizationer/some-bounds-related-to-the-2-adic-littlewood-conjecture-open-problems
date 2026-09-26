import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set
namespace VV.BBEKNormalizedRestriction

theorem normalize_restrict_normalize {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] {S T : Set Z}
    (hS : MeasurableSet S) (hST : S ⊆ T) (hpos : ν S ≠ 0) :
    let κ := (ν T)⁻¹ • ν.restrict T
    (κ S)⁻¹ • κ.restrict S = (ν S)⁻¹ • ν.restrict S := by
  have hT : ν T ≠ 0 := ne_zero_of_lt (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hpos) (measure_mono hST))
  have hTf : ν T ≠ ⊤ := measure_ne_top ν T
  have hval : ((ν T)⁻¹ • ν.restrict T) S = (ν T)⁻¹ * ν S := by
    rw [Measure.smul_apply,Measure.restrict_apply hS,inter_eq_self_of_subset_left hST]
    rfl
  dsimp only
  rw [hval,Measure.restrict_smul,Measure.restrict_restrict hS,
    inter_eq_self_of_subset_left hST,smul_smul]
  congr 1
  rw [ENNReal.mul_inv,inv_inv,mul_right_comm,ENNReal.mul_inv_cancel hT hTf,one_mul]
  · exact Or.inr (measure_ne_top ν S)
  · exact Or.inr hpos

end VV.BBEKNormalizedRestriction
