import VV.Entropy.WeakContinuity

/-!
Finite Shannon-entropy estimates used by the variational principle.  In
particular, none of the probabilities in these estimates need be invariant.
-/

noncomputable section
open MeasureTheory Function Set
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {X I J : Type*} [MeasurableSpace X]

/-- Jensen's inequality for an actual finite mixture, stated using its cell
masses so that it applies to any construction of the mixture measure. -/
theorem entropy_concave_of_apply [Fintype I] [Fintype J]
    (μ : Measure X) (ν : J → Measure X) (cells : I → Set X)
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hwone : ∑ j, w j = 1)
    (hmix : ∀ i, (μ (cells i)).toReal = ∑ j, w j * (ν j (cells i)).toReal) :
    (∑ j, w j * entropy (ν j) cells) ≤ entropy μ cells := by
  have hcell : ∀ i, (∑ j, w j * Real.negMulLog (ν j (cells i)).toReal) ≤
      Real.negMulLog (μ (cells i)).toReal := by
    intro i
    rw [hmix]
    simpa only [smul_eq_mul] using
      Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
        (fun j _ => hw j) hwone
        (fun j _ => Set.mem_Ici.mpr (ENNReal.toReal_nonneg :
          0 ≤ (ν j (cells i)).toReal))
  simp only [entropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun i _ => hcell i

/-- Pullback of an exact finite partition requires only measurability. -/
def FixedPartition.comap [Fintype I] (P : FixedPartition X I)
    {T : X → X} (hT : Measurable T) : FixedPartition X I where
  cells i := T ⁻¹' P.cells i
  measurable i := (P.measurable i).preimage hT
  disjoint := fun i j hij => (P.disjoint hij).preimage T
  cover := by rw [← preimage_iUnion, P.cover, preimage_univ]

@[simp] theorem FixedPartition.comap_cells [Fintype I] (P : FixedPartition X I)
    {T : X → X} (hT : Measurable T) (i : I) :
    (P.comap hT).cells i = T ⁻¹' P.cells i := rfl

/-- Entropy of a finite orbit block, with no invariant-measure assumption. -/
def blockEntropy [Fintype I] (μ : Measure X) (P : FixedPartition X I)
    (T : X → X) (n : ℕ) : ℝ := entropy μ (ksJoinCells P.cells T n)

theorem blockEntropy_nonneg [Fintype I] (μ : Measure X) [IsProbabilityMeasure μ]
    (P : FixedPartition X I) (T : X → X) (n : ℕ) : 0 ≤ blockEntropy μ P T n :=
  entropy_nonneg μ _

theorem blockEntropy_le_length_log [Fintype I] [Nonempty I]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : FixedPartition X I)
    {T : X → X} (hT : Measurable T) (n : ℕ) :
    blockEntropy μ P T n ≤ n * Real.log (Fintype.card I) := by
  have h := entropy_le_log_card_partition ((P.dynJoin hT n).toMeasurePartition μ)
  simpa only [FixedPartition.toMeasurePartition_cells, FixedPartition.dynJoin_cells,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h

/-- Splitting a block works for a non-invariant probability; the second
summand keeps its actual starting time. -/
theorem blockEntropy_add_le [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : FixedPartition X I)
    {T : X → X} (hT : Measurable T) (n m : ℕ) :
    blockEntropy μ P T (n + m) ≤ blockEntropy μ P T n +
      entropy μ (fun a => (T^[n]) ⁻¹' ksJoinCells P.cells T m a) := by
  have h := entropy_join_le ((P.dynJoin hT n).toMeasurePartition μ)
    (((P.dynJoin hT m).comap (hT.iterate n)).toMeasurePartition μ)
  have heq : blockEntropy μ P T (n + m) =
      entropy μ (joinCells (ksJoinCells P.cells T n)
        (fun a => (T^[n]) ⁻¹' ksJoinCells P.cells T m a)) := by
    rw [blockEntropy, ← entropy_reindex μ (Fin.appendEquiv n m)]
    congr 1
    funext a
    exact ksJoinCells_append P.cells T n m a.1 a.2
  rw [heq]
  exact h

/-- A block observed from a specified starting time. -/
def intervalEntropy [Fintype I] (μ : Measure X) (P : FixedPartition X I)
    (T : X → X) (s n : ℕ) : ℝ :=
  entropy μ (fun a => (T^[s]) ⁻¹' ksJoinCells P.cells T n a)

theorem intervalEntropy_nonneg [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : FixedPartition X I)
    (T : X → X) (s n : ℕ) : 0 ≤ intervalEntropy μ P T s n :=
  entropy_nonneg μ _

@[simp] theorem intervalEntropy_zero [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : FixedPartition X I)
    (T : X → X) (s : ℕ) : intervalEntropy μ P T s 0 = 0 := by
  unfold intervalEntropy entropy
  apply Finset.sum_eq_zero
  intro a ha
  simp [ksJoinCells]

@[simp] theorem intervalEntropy_start_zero [Fintype I]
    (μ : Measure X) (P : FixedPartition X I) (T : X → X) (n : ℕ) :
    intervalEntropy μ P T 0 n = blockEntropy μ P T n := by
  simp [intervalEntropy, blockEntropy]

theorem intervalEntropy_le_length_log [Fintype I] [Nonempty I]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : FixedPartition X I)
    {T : X → X} (hT : Measurable T) (s n : ℕ) :
    intervalEntropy μ P T s n ≤ n * Real.log (Fintype.card I) := by
  have h := entropy_le_log_card_partition
    (((P.dynJoin hT n).comap (hT.iterate s)).toMeasurePartition μ)
  simpa only [FixedPartition.toMeasurePartition_cells, FixedPartition.comap_cells,
    FixedPartition.dynJoin_cells, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, Real.log_pow] using h

/-- Interval subadditivity for a possibly non-invariant probability. -/
theorem intervalEntropy_add_le [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : FixedPartition X I)
    {T : X → X} (hT : Measurable T) (s n m : ℕ) :
    intervalEntropy μ P T s (n + m) ≤ intervalEntropy μ P T s n +
      intervalEntropy μ P T (s + n) m := by
  have h := entropy_join_le
    (((P.dynJoin hT n).comap (hT.iterate s)).toMeasurePartition μ)
    (((P.dynJoin hT m).comap (hT.iterate (s + n))).toMeasurePartition μ)
  have heq : intervalEntropy μ P T s (n + m) =
      entropy μ (joinCells (fun a => (T^[s]) ⁻¹' ksJoinCells P.cells T n a)
        (fun b => (T^[s + n]) ⁻¹' ksJoinCells P.cells T m b)) := by
    rw [intervalEntropy, ← entropy_reindex μ (Fin.appendEquiv n m)]
    congr 1
    funext a
    rw [show Fin.appendEquiv n m a = Fin.append a.1 a.2 from rfl,
      ksJoinCells_append, Set.preimage_inter, joinCells_apply]
    congr 1
    rw [← Set.preimage_comp]
    congr 1
    rw [← Function.iterate_add, Nat.add_comm]
  rw [heq]
  exact h

end ErgodicTheory.Entropy
