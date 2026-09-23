import VV.Entropy.FiniteConditionalEntropy
import VV.Entropy.KSEntropyMono

/-! Finite conditional entropy is the average of the entropies of the
actual normalized restrictions to conditioning cells.  The scalar
finite chain rule is imported from the ported upstream proof. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {X I J : Type*} [MeasurableSpace X]

/-- The actual restriction of a measure to a cell, normalized by the
cell mass.  For a null cell this is the zero measure. -/
def conditionalCellMeasure (μ : Measure X) (s : Set X) : Measure X :=
  (μ s)⁻¹ • μ.restrict s

theorem conditionalCellMeasure_apply (μ : Measure X) (s : Set X)
    {t : Set X} (ht : MeasurableSet t) :
    conditionalCellMeasure μ s t = (μ s)⁻¹ * μ (s ∩ t) := by
  simp only [conditionalCellMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply ht,inter_comm]

theorem condEntropyOnCell_eq_entropy_conditionalCellMeasure [Fintype J]
    (μ : Measure X) (s : Set X) (cells : J → Set X)
    (hcells : ∀ j, MeasurableSet (cells j)) :
    condEntropyOnCell μ s cells = entropy (conditionalCellMeasure μ s) cells := by
  simp only [condEntropyOnCell,entropy]
  apply Finset.sum_congr rfl
  intro j hj
  rw [conditionalCellMeasure_apply μ s (hcells j),ENNReal.toReal_mul,ENNReal.toReal_inv]
  congr 1
  rw [div_eq_mul_inv,mul_comm]

theorem condEntropyGivenPartition_eq_average_restriction_entropy [Fintype I] [Fintype J]
    (μ : Measure X) (s : I → Set X) (t : J → Set X)
    (ht : ∀ j, MeasurableSet (t j)) :
    condEntropyGivenPartition μ s t =
      ∑ i, (μ (s i)).toReal * entropy (conditionalCellMeasure μ (s i)) t := by
  simp only [condEntropyGivenPartition,condEntropyOnCell_eq_entropy_conditionalCellMeasure μ _ t ht]

theorem condEntropyGivenPartition_nonneg [Fintype I] [Fintype J]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ I) (Q : MeasurePartition μ J) :
    0 ≤ condEntropyGivenPartition μ P.cells Q.cells := by
  have h := entropy_le_entropy_join P Q
  rw [entropy_join_eq_add_condEntropyGivenPartition P Q] at h
  linarith

theorem condEntropyGivenPartition_le_entropy [Fintype I] [Fintype J]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ I) (Q : MeasurePartition μ J) :
    condEntropyGivenPartition μ P.cells Q.cells ≤ entropy μ Q.cells := by
  have h := entropy_join_le P Q
  rw [entropy_join_eq_add_condEntropyGivenPartition P Q] at h
  linarith

theorem condEntropyGivenPartition_eq_difference [Fintype I] [Fintype J]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ I) (Q : MeasurePartition μ J) :
    condEntropyGivenPartition μ P.cells Q.cells =
      entropy μ (joinCells P.cells Q.cells) - entropy μ P.cells := by
  rw [entropy_join_eq_add_condEntropyGivenPartition P Q]
  ring

end ErgodicTheory.Entropy
