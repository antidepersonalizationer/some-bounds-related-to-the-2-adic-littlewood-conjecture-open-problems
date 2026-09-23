import VV.Entropy.KSEntropyBounds
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
Weak convergence and relative Kolmogorov--Sinai entropy for an actual fixed
finite Borel partition. The upper-semicontinuity result is relative to that
partition, not an assertion of upper semicontinuity of full system entropy.
-/

noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology ENNReal

namespace ErgodicTheory.Entropy

variable {X I J : Type*} [MeasurableSpace X]

/-- A finite measurable partition whose cells do not depend on a measure. -/
structure FixedPartition (X : Type*) [MeasurableSpace X] (I : Type*) [Fintype I] where
  cells : I → Set X
  measurable : ∀ i, MeasurableSet (cells i)
  disjoint : Pairwise (Disjoint on cells)
  cover : ⋃ i, cells i = univ

/-- Exact disjointness gives a measurable partition for every measure. -/
def FixedPartition.toMeasurePartition [Fintype I] (P : FixedPartition X I)
    (μ : Measure X) : MeasurePartition μ I where
  cells := P.cells
  measurable := P.measurable
  aedisjoint := by
    intro i j hij
    change μ (P.cells i ∩ P.cells j) = 0
    rw [disjoint_iff_inter_eq_empty.mp (P.disjoint hij), measure_empty]
  cover := P.cover

@[simp] theorem FixedPartition.toMeasurePartition_cells [Fintype I]
    (P : FixedPartition X I) (μ : Measure X) : (P.toMeasurePartition μ).cells = P.cells := rfl

/-- Finite dynamical refinement of a fixed partition; no invariant measure is
needed to construct it. This also applies to empirical orbit averages. -/
def FixedPartition.dynJoin [Fintype I] (P : FixedPartition X I)
    {T : X → X} (hT : Measurable T) (n : ℕ) : FixedPartition X (Fin n → I) where
  cells := ksJoinCells P.cells T n
  measurable a := MeasurableSet.iInter fun k =>
    (P.measurable (a k)).preimage (hT.iterate k.val)
  disjoint := by
    intro a b hab
    obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra hn
      exact hab (funext fun k => not_not.mp (fun h => hn ⟨k, h⟩))
    apply Disjoint.mono (iInter_subset _ k) (iInter_subset _ k)
    exact (P.disjoint hk).preimage (T^[k.val])
  cover := by
    apply eq_univ_of_forall
    intro x
    have hx : ∀ k : Fin n, ∃ i, (T^[k.val]) x ∈ P.cells i := fun k => by
      apply mem_iUnion.mp
      rw [P.cover]
      exact mem_univ _
    choose a ha using hx
    exact mem_iUnion.mpr ⟨a, mem_iInter.mpr ha⟩

@[simp] theorem FixedPartition.dynJoin_cells [Fintype I] (P : FixedPartition X I)
    {T : X → X} (hT : Measurable T) (n : ℕ) :
    (P.dynJoin hT n).cells = ksJoinCells P.cells T n := rfl

section Weak
variable [PseudoEMetricSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]

/-- Entropy of finitely many fixed cells is continuous along weak convergence
when their boundaries are null for the limiting probability. -/
theorem entropy_tendsto_of_null_frontier [Fintype I]
    {L : Filter J} {μs : J → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs L (𝓝 μ)) (cells : I → Set X)
    (hboundary : ∀ i, (μ : Measure X) (frontier (cells i)) = 0) :
    Tendsto (fun j => entropy (μs j : Measure X) cells) L
      (𝓝 (entropy (μ : Measure X) cells)) := by
  unfold entropy
  apply tendsto_finset_sum
  intro i hi
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hμ (hboundary i)
  exact Real.continuous_negMulLog.continuousAt.tendsto.comp
    ((ENNReal.tendsto_toReal (measure_ne_top (μ : Measure X) (cells i))).comp hm)

omit [OpensMeasurableSpace X] [HasOuterApproxClosed X] in
/-- A finite intersection of sets with null boundaries again has null boundary. -/
theorem measure_frontier_iInter_eq_zero [Fintype I] (μ : Measure X) (s : I → Set X)
    (hs : ∀ i, μ (frontier (s i)) = 0) : μ (frontier (⋂ i, s i)) = 0 := by
  classical
  have hfinite : ∀ F : Finset I, μ (frontier (⋂ i ∈ F, s i)) = 0 := by
    intro F
    induction F using Finset.induction_on with
    | empty => simp
    | @insert i F hi hF =>
      simp only [Finset.mem_insert, iInter_iInter_eq_or_left]
      apply measure_mono_null (frontier_inter_subset _ _)
      exact measure_union_null (measure_mono_null inter_subset_left (hs i))
        (measure_mono_null inter_subset_right hF)
  simpa using hfinite Finset.univ

omit [HasOuterApproxClosed X] in
/-- The boundary of every finite dynamical cell is null if the original
boundaries are null and the limiting probability is invariant. -/
theorem ksJoinCells_null_frontier [Fintype I]
    {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ) (hcont : Continuous T)
    (cells : I → Set X) (hboundary : ∀ i, μ (frontier (cells i)) = 0)
    (n : ℕ) (a : Fin n → I) : μ (frontier (ksJoinCells cells T n a)) = 0 := by
  apply measure_frontier_iInter_eq_zero
  intro k
  apply measure_mono_null ((hcont.iterate k.val).frontier_preimage_subset (cells (a k)))
  rw [(hT.iterate k.val).measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet]
  exact hboundary (a k)

/-- Continuity of every finite iterated-join entropy at a boundary-null limit. -/
theorem ksEntropySeq_tendsto [Fintype I] (P : FixedPartition X I)
    {L : Filter J} {μs : J → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs L (𝓝 μ)) {T : X → X} (hcont : Continuous T)
    (hT : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (hTs : ∀ j, MeasurePreserving T (μs j : Measure X) (μs j : Measure X))
    (hboundary : ∀ i, (μ : Measure X) (frontier (P.cells i)) = 0) (n : ℕ) :
    Tendsto (fun j => ksEntropySeq (hTs j) (P.toMeasurePartition (μs j : Measure X)) n) L
      (𝓝 (ksEntropySeq hT (P.toMeasurePartition (μ : Measure X)) n)) := by
  apply entropy_tendsto_of_null_frontier hμ (ksJoinCells P.cells T n)
  exact ksJoinCells_null_frontier hT hcont P.cells hboundary n

/-- Finite orbit-block entropy continuity also holds for empirical measures,
which need not be invariant. Only the limit probability is invariant. -/
theorem entropy_dynJoin_tendsto [Fintype I] (P : FixedPartition X I)
    {L : Filter J} {μs : J → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs L (𝓝 μ)) {T : X → X} (hcont : Continuous T)
    (hT : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (hboundary : ∀ i, (μ : Measure X) (frontier (P.cells i)) = 0) (n : ℕ) :
    Tendsto (fun j => entropy (μs j : Measure X) (ksJoinCells P.cells T n)) L
      (𝓝 (entropy (μ : Measure X) (ksJoinCells P.cells T n))) :=
  entropy_tendsto_of_null_frontier hμ (ksJoinCells P.cells T n)
    (ksJoinCells_null_frontier hT hcont P.cells hboundary n)

end Weak

/-- The Fekete limit is below every positive finite-time entropy average. -/
theorem ksEntropyPartition_le_div [Fintype I] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I)
    {n : ℕ} (hn : n ≠ 0) : ksEntropyPartition hT P ≤ ksEntropySeq hT P n / n := by
  apply (ksSubadditive hT P).lim_le_div _ hn
  refine ⟨0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact div_nonneg (ksEntropySeq_nonneg hT P k) (Nat.cast_nonneg k)

section UpperSemicontinuity
variable [PseudoEMetricSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]

/-- Relative entropy is eventually below every strict upper bound for the
limit's relative entropy. This proves the actual semicontinuity step by
combining a finite Fekete upper bound with Portmanteau continuity. -/
theorem ksEntropyPartition_eventually_lt [Fintype I] (P : FixedPartition X I)
    {L : Filter J} {μs : J → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs L (𝓝 μ)) {T : X → X} (hcont : Continuous T)
    (hT : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (hTs : ∀ j, MeasurePreserving T (μs j : Measure X) (μs j : Measure X))
    (hboundary : ∀ i, (μ : Measure X) (frontier (P.cells i)) = 0)
    {b : ℝ} (hb : ksEntropyPartition hT (P.toMeasurePartition (μ : Measure X)) < b) :
    ∀ᶠ j in L, ksEntropyPartition (hTs j) (P.toMeasurePartition (μs j : Measure X)) < b := by
  have he := (tendsto_ksEntropySeq hT (P.toMeasurePartition (μ : Measure X))).eventually
    (gt_mem_nhds hb)
  obtain ⟨n, hn, hnlt⟩ := ((eventually_ge_atTop 1).and he).exists
  have hn0 : n ≠ 0 := by omega
  have hc := (ksEntropySeq_tendsto P hμ hcont hT hTs hboundary n).div_const (n : ℝ)
  filter_upwards [hc.eventually (gt_mem_nhds hnlt)] with j hj
  exact (ksEntropyPartition_le_div (hTs j)
    (P.toMeasurePartition (μs j : Measure X)) hn0).trans_lt hj

/-- Weak upper semicontinuity of KS entropy relative to a fixed finite Borel
partition with limit-null boundaries. The result does not assert system-entropy
upper semicontinuity without a generating/entropy-expansive argument. -/
theorem ksEntropyPartition_limsup_le [Fintype I] (P : FixedPartition X I)
    {L : Filter J} [NeBot L] {μs : J → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs L (𝓝 μ)) {T : X → X} (hcont : Continuous T)
    (hT : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (hTs : ∀ j, MeasurePreserving T (μs j : Measure X) (μs j : Measure X))
    (hboundary : ∀ i, (μ : Measure X) (frontier (P.cells i)) = 0) :
    Filter.limsup (fun j => ksEntropyPartition (hTs j)
      (P.toMeasurePartition (μs j : Measure X))) L ≤
      ksEntropyPartition hT (P.toMeasurePartition (μ : Measure X)) := by
  have hc := isCoboundedUnder_le_of_le L (fun j =>
    ksEntropyPartition_nonneg (hTs j) (P.toMeasurePartition (μs j : Measure X)))
  have he := ksEntropyPartition_eventually_lt P hμ hcont hT hTs hboundary
    (lt_add_one (ksEntropyPartition hT (P.toMeasurePartition (μ : Measure X))))
  have hb := isBoundedUnder_of_eventually_le (he.mono (fun _ h => h.le))
  apply (limsup_le_iff hc hb).mpr
  intro b hb
  exact ksEntropyPartition_eventually_lt P hμ hcont hT hTs hboundary hb

end UpperSemicontinuity
end ErgodicTheory.Entropy



