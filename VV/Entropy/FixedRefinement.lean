import VV.Entropy.KSEntropyMono
import VV.Entropy.SmallPartition
import VV.Entropy.KSEntropySystem

/-! Exact partitions, finite common refinements, and their actual entropy bounds. -/
noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology ENNReal
namespace ErgodicTheory.Entropy
variable {X I J : Type*} [MeasurableSpace X]

/-- Entropy increases under an explicit cellwise refinement. -/
theorem entropy_le_of_refines [Fintype I] [Fintype J]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (P : FixedPartition X I) (Q : FixedPartition X J) (π : J → I)
    (href : ∀ j, Q.cells j ⊆ P.cells (π j)) :
    entropy μ P.cells ≤ entropy μ Q.cells := by
  classical
  have h := entropy_le_entropy_join (P.toMeasurePartition μ) (Q.toMeasurePartition μ)
  have he : entropy μ (joinCells P.cells Q.cells) = entropy μ Q.cells := by
    simp only [entropy, joinCells, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single (π j)]
    · rw [inter_eq_right.mpr (href j)]
    · intro i hi hne
      have hd : Disjoint (P.cells i) (Q.cells j) := (P.disjoint hne).mono_right (href j)
      rw [disjoint_iff_inter_eq_empty.mp hd]
      simp
    · simp
  exact h.trans_eq he

/-- The same cell refinement holds for every finite orbit block. -/
theorem ksEntropyPartition_le_of_refines [Fintype I] [Fintype J]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ)
    (P : FixedPartition X I) (Q : FixedPartition X J) (π : J → I)
    (href : ∀ j, Q.cells j ⊆ P.cells (π j)) :
    ksEntropyPartition hT (P.toMeasurePartition μ) ≤
      ksEntropyPartition hT (Q.toMeasurePartition μ) := by
  apply le_of_tendsto_of_tendsto' (tendsto_ksEntropySeq hT (P.toMeasurePartition μ))
    (tendsto_ksEntropySeq hT (Q.toMeasurePartition μ))
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply entropy_le_of_refines (P.dynJoin hT.measurable n) (Q.dynJoin hT.measurable n)
    (fun a k => π (a k))
  intro a
  exact iInter_mono (fun k => preimage_mono (href (a k)))

/-- A dependent finite family has an actual common refinement. -/
def FixedPartition.iJoin {D : Type*} [Fintype D] [DecidableEq D] {I : D → Type*}
    [∀ d, Fintype (I d)] (P : ∀ d, FixedPartition X (I d)) :
    FixedPartition X (∀ d, I d) where
  cells a := ⋂ d, (P d).cells (a d)
  measurable a := MeasurableSet.iInter (fun d => (P d).measurable (a d))
  disjoint := by
    intro a b hab
    obtain ⟨d, hd⟩ : ∃ d, a d ≠ b d := by
      by_contra hn
      exact hab (funext fun d => not_not.mp (fun h => hn ⟨d, h⟩))
    exact ((P d).disjoint hd).mono (iInter_subset _ d) (iInter_subset _ d)
  cover := by
    apply eq_univ_of_forall
    intro x
    have hx : ∀ d, ∃ i, x ∈ (P d).cells i := by
      intro d
      apply mem_iUnion.mp
      rw [(P d).cover]
      exact mem_univ x
    choose a ha using hx
    exact mem_iUnion.mpr ⟨a, mem_iInter.mpr ha⟩

theorem ksEntropyPartition_le_iJoin {D : Type*} [Fintype D] [DecidableEq D] {I : D → Type*}
    [∀ d, Fintype (I d)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ)
    (P : ∀ d, FixedPartition X (I d)) (d : D) :
    ksEntropyPartition hT ((P d).toMeasurePartition μ) ≤
      ksEntropyPartition hT ((FixedPartition.iJoin P).toMeasurePartition μ) :=
  ksEntropyPartition_le_of_refines hT (P d) (FixedPartition.iJoin P)
    (fun a => a d) (fun _ => iInter_subset _ d)

/-- Null changes in partition cells leave every finite orbit-block entropy unchanged. -/
theorem ksEntropyPartition_eq_of_cells_ae [Fintype I]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (P Q : MeasurePartition μ I)
    (hPQ : ∀ i, P.cells i =ᵐ[μ] Q.cells i) :
    ksEntropyPartition hT P = ksEntropyPartition hT Q := by
  apply Subadditive.lim_eq_of_eq
  funext n
  unfold ksEntropySeq entropy
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  apply measure_congr
  have hh : ∀ k : Fin n, ∀ᵐ x ∂μ,
      (T^[k.val]) x ∈ P.cells (a k) ↔ (T^[k.val]) x ∈ Q.cells (a k) := by
    intro k
    exact (hT.iterate k.val).quasiMeasurePreserving.ae (hPQ (a k)).mem_iff
  filter_upwards [ae_all_iff.mpr hh] with x hx
  apply propext
  change x ∈ (⋂ k : Fin n, T^[k.val] ⁻¹' P.cells (a k)) ↔
    x ∈ (⋂ k : Fin n, T^[k.val] ⁻¹' Q.cells (a k))
  simp only [mem_iInter, mem_preimage]
  exact forall_congr' hx

/-- Exact disjointification, with the original finite index type. -/
def MeasurePartition.exactify {n : ℕ} {μ : Measure X} (P : MeasurePartition μ (Fin n)) :
    FixedPartition X (Fin n) := FixedPartition.ofCover P.cells P.measurable P.cover

theorem MeasurePartition.exactify_cells_ae {n : ℕ} {μ : Measure X}
    (P : MeasurePartition μ (Fin n)) (i : Fin n) :
    P.exactify.cells i =ᵐ[μ] P.cells i := by
  classical
  have hh : ∀ j : Fin n, ∀ᵐ x ∂μ, x ∈ P.cells i → j < i → x ∉ P.cells j := by
    intro j
    by_cases hji : j < i
    · have hd := (ae_eq_empty.mpr (P.aedisjoint (ne_of_gt hji))).mem_iff
      filter_upwards [hd] with x hx
      have hnot : ¬(x ∈ P.cells i ∧ x ∈ P.cells j) := by simpa using hx
      exact fun hi _ hj => hnot ⟨hi, hj⟩
    · filter_upwards with x hx hj
      exact (hji hj).elim
  filter_upwards [ae_all_iff.mpr hh] with x hx
  apply propext
  change x ∈ disjointed P.cells i ↔ x ∈ P.cells i
  rw [disjointed_eq_inter_compl]
  simp only [mem_inter_iff, mem_iInter, mem_compl_iff]
  exact ⟨And.left, fun hxi => ⟨hxi, fun j hj => hx j hxi hj⟩⟩

theorem MeasurePartition.ksEntropy_exactify {n : ℕ} {μ : Measure X}
    [IsProbabilityMeasure μ] {T : X → X} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ (Fin n)) :
    ksEntropyPartition hT (P.exactify.toMeasurePartition μ) = ksEntropyPartition hT P :=
  ksEntropyPartition_eq_of_cells_ae hT _ _ P.exactify_cells_ae

/-- Reindexing a partition changes neither its orbit-block sums nor their limit. -/
theorem ksEntropyPartition_reindex [Fintype I] [Fintype J]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) (e : J ≃ I) :
    ksEntropyPartition hT (P.reindex e) = ksEntropyPartition hT P := by
  apply Subadditive.lim_eq_of_eq
  funext n
  change entropy μ (ksJoinCells (fun j => P.cells (e j)) T n) =
    entropy μ (ksJoinCells P.cells T n)
  convert entropy_reindex μ (Equiv.piCongrRight (fun _ : Fin n => e))
    (ksJoinCells P.cells T n) using 1

/-- The defining `Fin` supremum dominates partitions with any finite index type. -/
theorem ksEntropyPartition_le_ksEntropy [Fintype I]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) :
    (ksEntropyPartition hT P : EReal) ≤ ksEntropy hT := by
  rw [← ksEntropyPartition_reindex hT P (Fintype.equivFin I).symm]
  exact le_ksEntropy hT _

end ErgodicTheory.Entropy

