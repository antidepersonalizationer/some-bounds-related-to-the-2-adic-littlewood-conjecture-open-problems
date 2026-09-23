/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import VV.Entropy.KSEntropySystem
import Mathlib.Data.Fin.Rev

/-!
# Kolmogorov--Sinai entropy of an inverse transformation

This file proves, from the finite-partition definition, that a measure-preserving measurable
equivalence and its inverse have the same Kolmogorov--Sinai entropy.  The finite join for the
inverse is carried to the finite join for the original map by applying the last forward iterate
and reversing the word indexing the cells.
-/

open MeasureTheory Function

namespace ErgodicTheory.Entropy

variable {α : Type*} [MeasurableSpace α]

/-- Reverse the coordinates of a finite word. -/
def reverseWords {ι : Type*} (n : ℕ) : (Fin n → ι) ≃ (Fin n → ι) where
  toFun f := f ∘ Fin.rev
  invFun f := f ∘ Fin.rev
  left_inv f := by
    funext k
    simp
  right_inv f := by
    funext k
    simp

@[simp]
lemma reverseWords_apply {ι : Type*} (n : ℕ) (f : Fin n → ι) (k : Fin n) :
    reverseWords n f k = f k.rev := rfl

/-- The forward and backward finite-join cells agree after translating by the last forward
iterate and reversing their word coordinates. -/
lemma ksJoinCells_measurableEquiv_symm {ι : Type*} (e : α ≃ᵐ α)
    (cells : ι → Set α) (m : ℕ) (f : Fin (m + 1) → ι) :
    ksJoinCells cells (e : α → α) (m + 1) f =
      (e^[m]) ⁻¹' ksJoinCells cells (e.symm : α → α) (m + 1) (reverseWords (m + 1) f) := by
  ext x
  simp only [ksJoinCells_apply, Set.mem_iInter, Set.mem_preimage, reverseWords_apply]
  have hcancel (k : Fin (m + 1)) :
      ((e.symm : α → α)^[(k : ℕ)]) (((e : α → α)^[m]) x) =
        ((e : α → α)^[(k.rev : ℕ)]) x := by
    have hm : ((e : α → α)^[m]) x =
        ((e : α → α)^[(k : ℕ)]) (((e : α → α)^[(k.rev : ℕ)]) x) := by
      rw [← Function.iterate_add_apply, k.add_rev_cast]
    rw [hm]
    have hinv : Function.LeftInverse (e.symm : α → α) (e : α → α) :=
      e.symm_apply_apply
    exact (hinv.iterate (k : ℕ)) _
  constructor
  · intro hx k
    rw [hcancel k]
    exact hx k.rev
  · intro hx k
    have hk := hx k.rev
    rw [hcancel k.rev, Fin.rev_rev] at hk
    exact hk

/-- Every finite iterated-join entropy is unchanged by reversing an invertible system. -/
lemma ksEntropySeq_measurableEquiv_symm [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropySeq he P n = ksEntropySeq (he.symm e) P n := by
  cases n with
  | zero => simp
  | succ m =>
      rw [ksEntropySeq, ksEntropySeq,
        ← entropy_reindex μ (reverseWords (m + 1))
          (ksJoin (he.symm e) P (m + 1)).cells,
        entropy_def, entropy_def]
      refine Finset.sum_congr rfl fun (f : Fin (m + 1) → ι) _ => ?_
      have hcell := ksJoinCells_measurableEquiv_symm e P.cells m f
      simp only [ksJoin_cells] at hcell ⊢
      rw [hcell]
      have hmeas : MeasurableSet
          (ksJoinCells P.cells (e.symm : α → α) (m + 1) (reverseWords (m + 1) f)) := by
        simpa only [ksJoin_cells] using
          (ksJoin (he.symm e) P (m + 1)).measurable (reverseWords (m + 1) f)
      have hmeasure :
          μ ((e^[m]) ⁻¹' ksJoinCells P.cells (e.symm : α → α) (m + 1)
            (reverseWords (m + 1) f)) =
            μ (ksJoinCells P.cells (e.symm : α → α) (m + 1) (reverseWords (m + 1) f)) :=
        (he.iterate m).measure_preimage hmeas.nullMeasurableSet
      rw [hmeasure]

/-- Partition-relative Kolmogorov--Sinai entropy is unchanged by taking the inverse of a
measure-preserving measurable equivalence. -/
lemma ksEntropyPartition_measurableEquiv_symm [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ)
    (P : MeasurePartition μ ι) :
    ksEntropyPartition he P = ksEntropyPartition (he.symm e) P := by
  apply Subadditive.lim_eq_of_eq
  funext n
  exact ksEntropySeq_measurableEquiv_symm e he P n

/-- Kolmogorov--Sinai entropy of a measure-preserving measurable equivalence equals the entropy
of its inverse. -/
lemma ksEntropy_measurableEquiv_symm {μ : Measure α} [IsProbabilityMeasure μ]
    (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ) :
    ksEntropy he = ksEntropy (he.symm e) := by
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun P => ?_
    rw [ksEntropyPartition_measurableEquiv_symm e he P]
    exact le_ksEntropy (he.symm e) P
  · refine iSup_le fun n => iSup_le fun P => ?_
    rw [← ksEntropyPartition_measurableEquiv_symm e he P]
    exact le_ksEntropy he P

end ErgodicTheory.Entropy
