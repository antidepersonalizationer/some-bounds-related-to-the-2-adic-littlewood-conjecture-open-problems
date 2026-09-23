import VV.Entropy.BowenPartition
import VV.Entropy.CompactCores

/-! Finite Bowen-cover bounds imply that sufficiently fine partitions attain
the full system entropy.  The proof uses compact cores and counts actual
names, without assuming any generating-sigma-algebra identity. -/

noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology ENNReal

namespace ErgodicTheory.Entropy

variable {X I : Type*} [MeasurableSpace X]

def corePartition [Fintype I] (K : I → Set X) (hK : ∀ i, MeasurableSet (K i))
    (hd : Pairwise (Disjoint on K)) : FixedPartition X (Option I) where
  cells a := a.elim (⋃ i, K i)ᶜ K
  measurable a := by
    cases a with
    | none => exact (MeasurableSet.iUnion hK).compl
    | some i => exact hK i
  disjoint := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact False.elim (hab rfl)
      | some j =>
        apply Set.disjoint_left.mpr
        intro x hx hy
        exact hx (mem_iUnion.mpr ⟨j,hy⟩)
    | some i =>
      cases b with
      | none =>
        apply Set.disjoint_left.mpr
        intro x hx hy
        exact hy (mem_iUnion.mpr ⟨i,hx⟩)
      | some j => exact hd (fun h => hab (congrArg some h))
  cover := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ ⋃ i, K i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨some i,hi⟩
    · exact mem_iUnion.mpr ⟨none,hx⟩

def binaryEntropy (p : ℝ) : ℝ := Real.negMulLog p + Real.negMulLog (1-p)

theorem entropy_binaryPartition {μ : Measure X} [IsProbabilityMeasure μ]
    (B : Set X) (hB : MeasurableSet B) :
    entropy μ (binaryPartition B hB).cells = binaryEntropy (μ B).toReal := by
  have hcompl : (μ Bᶜ).toReal = 1 - (μ B).toReal := by
    change μ.real Bᶜ = 1 - μ.real B
    rw [measureReal_compl hB, measureReal_univ_eq_one]
  simp [entropy, binaryPartition, Fintype.sum_bool, hcompl, binaryEntropy, add_comm]

theorem exists_small_binary_cost (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ p : ℝ, 0 ≤ p → p < η → binaryEntropy p + p * D < ε := by
  have hcont : Continuous (fun p : ℝ => binaryEntropy p + p * D) :=
    (Real.continuous_negMulLog.add (Real.continuous_negMulLog.comp
      (continuous_const.sub continuous_id))).add (continuous_id.mul continuous_const)
  have hlim : Tendsto (fun p : ℝ => binaryEntropy p + p * D) (𝓝 0) (𝓝 0) := by
    simpa [binaryEntropy] using hcont.continuousAt.tendsto (x := 0)
  have hevent : ∀ᶠ p : ℝ in 𝓝 0, binaryEntropy p + p * D < ε :=
    hlim.eventually (eventually_lt_nhds hε)
  obtain ⟨η,hη,hh⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨η,hη,?_⟩
  intro p hp hpη
  apply hh
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hp] using hpη

section Compact
variable [MetricSpace X] [BorelSpace X] [CompactSpace X]

/-- Every finite measurable partition is bounded in entropy by a sufficiently
fine coarse partition when finite Bowen fibers have uniformly bounded fine
covers.  Compact-core approximation is carried out inside the proof. -/
theorem ksEntropyPartition_le_of_uniformBowenCover
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {m : ℕ} (P : FixedPartition X (Fin m))
    {r : ℝ} (hcover : UniformBowenCover T r)
    (hmesh : ∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < r)
    {q : ℕ} (Q : MeasurePartition μ (Fin q)) :
    ksEntropyPartition hT Q ≤ ksEntropyPartition hT (P.toMeasurePartition μ) := by
  classical
  haveI : Nonempty (Fin q) := by
    obtain ⟨x,hx⟩ := nonempty_of_measure_ne_zero (show μ (univ : Set X) ≠ 0 by simp)
    obtain ⟨i,hi⟩ := mem_iUnion.mp (Q.cover ▸ mem_univ x)
    exact ⟨i⟩
  let Q' := Q.exactify
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨η,hη,hcost⟩ := exists_small_binary_cost (Real.log (Fintype.card (Fin q))) hε
  obtain ⟨K,hsub,hK,hd,hbad,ρ,hρ,hsep⟩ := exists_compact_partition_cores μ Q' hη
  let R := corePartition K (fun i => (hK i).measurableSet) hd
  have hcore : ∀ i, R.cells (some i) ⊆ Q'.cells i := hsub
  have h1 := ksEntropyPartition_le_bad_symbol hT Q' R hcore
  have h2 := coreEntropy_le_coarse_add_binary hT P R hcover hmesh hρ hsep
  rw [entropy_binaryPartition] at h2
  have hc := hcost (μ (R.cells none)).toReal ENNReal.toReal_nonneg hbad
  have hQ : ksEntropyPartition hT (Q'.toMeasurePartition μ) = ksEntropyPartition hT Q :=
    Q.ksEntropy_exactify hT
  rw [hQ] at h1
  exact (by linarith : ksEntropyPartition hT Q <
    ksEntropyPartition hT (P.toMeasurePartition μ) + ε).le

/-- The finite geometric cover property, rather than an assumed entropy or
generator equality, suffices to make a fine partition attain full KS entropy. -/
theorem ksEntropy_eq_of_uniformBowenCover
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {m : ℕ} (P : FixedPartition X (Fin m))
    {r : ℝ} (hcover : UniformBowenCover T r)
    (hmesh : ∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < r) :
    ksEntropy hT = (ksEntropyPartition hT (P.toMeasurePartition μ) : EReal) := by
  apply le_antisymm _ (le_ksEntropy hT (P.toMeasurePartition μ))
  apply iSup_le
  intro q
  apply iSup_le
  intro Q
  exact EReal.coe_le_coe_iff.mpr
    (ksEntropyPartition_le_of_uniformBowenCover hT P hcover hmesh Q)

end Compact
end ErgodicTheory.Entropy

