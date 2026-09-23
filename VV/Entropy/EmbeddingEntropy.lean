import VV.Entropy.FactorEntropy

/-! Entropy is unchanged by a measurable embedding intertwining the dynamics.
This applies to the actual inclusion of a compact trapped set in the quotient. -/

noncomputable section
open MeasureTheory Set Function

namespace ErgodicTheory.Entropy
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype I]

theorem MeasurePartition.eq_of_cells_eq {μ : Measure X}
    {P Q : MeasurePartition μ I} (h : P.cells = Q.cells) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

def embeddingCell {μ : Measure X} (f : X → Y) (P : MeasurePartition μ I)
    (i₀ i : I) : Set Y := by
  classical
  exact f '' P.cells i ∪ if i = i₀ then (range f)ᶜ else ∅

theorem preimage_embeddingCell {μ : Measure X} {f : X → Y} (hf : MeasurableEmbedding f)
    (P : MeasurePartition μ I) (i₀ i : I) : f ⁻¹' embeddingCell f P i₀ i = P.cells i := by
  classical
  by_cases hi : i = i₀
  · simp [embeddingCell,hi,hf.injective.preimage_image]
  · simp [embeddingCell,hi,hf.injective.preimage_image]

theorem measurable_embeddingCell {μ : Measure X} {f : X → Y} (hf : MeasurableEmbedding f)
    (P : MeasurePartition μ I) (i₀ i : I) : MeasurableSet (embeddingCell f P i₀ i) := by
  classical
  unfold embeddingCell
  apply (hf.measurableSet_image.mpr (P.measurable i)).union
  split_ifs
  · exact hf.measurableSet_range.compl
  · exact MeasurableSet.empty

def MeasurePartition.pushedEmbedding {μ : Measure X} {ν : Measure Y} {f : X → Y}
    (hf : MeasurableEmbedding f) (hμf : MeasurePreserving f μ ν)
    (P : MeasurePartition μ I) (i₀ : I) : MeasurePartition ν I where
  cells i := embeddingCell f P i₀ i
  measurable i := measurable_embeddingCell hf P i₀ i
  aedisjoint := by
    intro i j hij
    change ν (embeddingCell f P i₀ i ∩ embeddingCell f P i₀ j) = 0
    rw [← hμf.measure_preimage
      ((measurable_embeddingCell hf P i₀ i).inter
        (measurable_embeddingCell hf P i₀ j)).nullMeasurableSet,
      preimage_inter,preimage_embeddingCell hf P i₀ i,preimage_embeddingCell hf P i₀ j]
    exact P.aedisjoint hij
  cover := by
    classical
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ range f
    · obtain ⟨x,rfl⟩ := hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp (P.cover ▸ mem_univ x)
      exact mem_iUnion.mpr ⟨i,Or.inl ⟨x,hi,rfl⟩⟩
    · exact mem_iUnion.mpr ⟨i₀,Or.inr (by simpa using hy)⟩

theorem pulled_pushedEmbedding {μ : Measure X} {ν : Measure Y} {f : X → Y}
    (hf : MeasurableEmbedding f) (hμf : MeasurePreserving f μ ν)
    (P : MeasurePartition μ I) (i₀ : I) :
    (P.pushedEmbedding hf hμf i₀).pulledBack hμf = P := by
  apply MeasurePartition.eq_of_cells_eq
  funext i
  exact preimage_embeddingCell hf P i₀ i

theorem ksEntropy_eq_of_embedding {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : X → X} {S : Y → Y} {f : X → Y}
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (hf : MeasurableEmbedding f) (hμf : MeasurePreserving f μ ν)
    (hsem : f ∘ T = S ∘ f) : ksEntropy hT = ksEntropy hS := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro P
    cases n with
    | zero =>
      have hc : (∅ : Set X) = univ := by simpa using P.cover
      have hz : μ univ = 0 := by rw [← hc,measure_empty]
      simp at hz
    | succ n =>
      let Q := P.pushedEmbedding hf hμf 0
      have he := factor_relative_eq hT hS hμf hsem Q
      rw [pulled_pushedEmbedding] at he
      rw [he]
      exact le_ksEntropy hS Q
  · apply iSup_le
    intro n
    apply iSup_le
    intro P
    rw [← factor_relative_eq hT hS hμf hsem P]
    exact le_ksEntropy hT (P.pulledBack hμf)

end ErgodicTheory.Entropy
