import VV.Entropy.WeakContinuity

/-! Actual finite small-mesh Borel partitions with null boundaries. -/

noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology ENNReal

namespace ErgodicTheory.Entropy

variable {X : Type*} [MeasurableSpace X]

/-- Turn a finite measurable cover into an exactly disjoint partition by
assigning each point to the first covering set. -/
def FixedPartition.ofCover {n : ℕ} (U : Fin n → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ) :
    FixedPartition X (Fin n) where
  cells := disjointed U
  measurable i := by
    rw [disjointed_eq_inter_compl]
    exact (hU i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hU j).compl)
  disjoint := disjoint_disjointed U
  cover := by rw [iUnion_disjointed, hcover]

@[simp] theorem FixedPartition.ofCover_cells {n : ℕ} (U : Fin n → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ) :
    (FixedPartition.ofCover U hU hcover).cells = disjointed U := rfl

section Metric
variable [PseudoMetricSpace X] [OpensMeasurableSpace X]

omit [OpensMeasurableSpace X] in
lemma measure_frontier_inter_eq_zero (μ : Measure X) {s t : Set X}
    (hs : μ (frontier s) = 0) (ht : μ (frontier t) = 0) :
    μ (frontier (s ∩ t)) = 0 :=
  measure_mono_null (frontier_inter_subset _ _)
    (measure_union_null (measure_mono_null inter_subset_left hs)
      (measure_mono_null inter_subset_right ht))

omit [OpensMeasurableSpace X] in
/-- Removing the finitely many earlier covering sets does not create positive
boundary measure. -/
theorem disjointed_null_frontier {n : ℕ} (μ : Measure X) (U : Fin n → Set X)
    (hboundary : ∀ i, μ (frontier (U i)) = 0) (i : Fin n) :
    μ (frontier (disjointed U i)) = 0 := by
  rw [disjointed_eq_inter_compl]
  apply measure_frontier_inter_eq_zero μ (hboundary i)
  apply measure_frontier_iInter_eq_zero
  intro j
  by_cases hj : j < i
  · simpa [hj] using hboundary j
  · simp [hj]

/-- On a compact metric space, every positive scale admits an actual finite
Borel partition with null boundaries and strictly smaller within-cell distances. -/
theorem exists_small_null_frontier_partition [CompactSpace X]
    (μ : Measure X) [SFinite μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ P : FixedPartition X (Fin n),
      (∀ i, μ (frontier (P.cells i)) = 0) ∧
      (∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < ε) := by
  classical
  have hr : ∀ x : X, ∃ r : ℝ, 0 < r ∧ 2 * r < ε ∧ μ (frontier (Metric.ball x r)) = 0 := by
    intro x
    obtain ⟨r, hr, hnull⟩ := exists_null_frontier_thickening μ ({x} : Set X)
      (show ε / 4 < ε / 2 by linarith)
    refine ⟨r, by linarith [hr.1], by linarith [hr.2], ?_⟩
    simpa only [Metric.thickening_singleton] using hnull
  choose r hrpos hrsmall hrnull using hr
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => Metric.ball x (r x)) (fun _ => Metric.isOpen_ball)
    (by intro x hx; exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hrpos x)⟩)
  let n := Fintype.card F
  let e : Fin n ≃ F := (Fintype.equivFin F).symm
  let U : Fin n → Set X := fun i => Metric.ball (e i).val (r (e i).val)
  have hU : ∀ i, MeasurableSet (U i) := fun _ => Metric.isOpen_ball.measurableSet
  have hcover : ⋃ i, U i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨c, hcF, hxc⟩ := mem_iUnion₂.mp (hF (mem_univ x))
    refine mem_iUnion.mpr ⟨e.symm ⟨c, hcF⟩, ?_⟩
    simpa [U] using hxc
  let P := FixedPartition.ofCover U hU hcover
  refine ⟨n, P, ?_, ?_⟩
  · intro i
    exact disjointed_null_frontier μ U (fun j => hrnull (e j).val) i
  · intro i x hx y hy
    have hxball := disjointed_subset U i hx
    have hyball := disjointed_subset U i hy
    change dist x (e i).val < r (e i).val at hxball
    change dist y (e i).val < r (e i).val at hyball
    have htriangle := dist_triangle x (e i).val y
    rw [dist_comm (e i).val y] at htriangle
    linarith [hrsmall (e i).val]

end Metric
end ErgodicTheory.Entropy


