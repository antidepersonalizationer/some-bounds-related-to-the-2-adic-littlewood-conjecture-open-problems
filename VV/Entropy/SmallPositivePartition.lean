import VV.Entropy.ConditionalEntropyNontrivial
import VV.Entropy.FixedRefinement

/-! Positive entropy can be witnessed by an arbitrarily fine finite
partition.  This only uses common refinement, not a generator hypothesis. -/

noncomputable section
open MeasureTheory Set

namespace ErgodicTheory.Entropy

theorem exists_pos_small_partition {X : Type*} [PseudoMetricSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (hpos : 0 < ksEntropy hT)
    {r : ℝ} (hr : 0 < r) :
    ∃ m : ℕ, ∃ P : MeasurePartition μ (Fin m),
      0 < ksEntropyPartition hT P ∧
      ∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < r := by
  classical
  obtain ⟨n,P,hP⟩ := exists_pos_partition_of_pos_ksEntropy hT hpos
  obtain ⟨k,Q,_,hQ⟩ := exists_small_null_frontier_partition μ hr
  let R := joinPartition P (Q.toMeasurePartition μ)
  let e := (Fintype.equivFin (Fin n × Fin k)).symm
  refine ⟨Fintype.card (Fin n × Fin k),R.reindex e,?_,?_⟩
  · rw [ksEntropyPartition_reindex]
    exact hP.trans_le (ksEntropyPartition_le_join hT P (Q.toMeasurePartition μ))
  · intro i x hx y hy
    exact hQ (e i).2 x hx.2 y hy.2

end ErgodicTheory.Entropy
