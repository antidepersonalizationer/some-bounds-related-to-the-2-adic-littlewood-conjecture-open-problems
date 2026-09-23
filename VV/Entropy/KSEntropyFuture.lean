import VV.Entropy.ConditionalEntropy
import VV.Entropy.CondEntropyContinuous
import VV.Entropy.CondGivenPartitionBridge
import VV.Entropy.JoinSigmaAlgebra
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! The entropy of a finite partition is its conditional entropy given
the entire strict future.  This is proved from finite block identities,
Lévy continuity, and Cesàro convergence; no conditional entropy formula
is assumed. -/

noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology

namespace ErgodicTheory.Entropy

variable {X I : Type*} [mX : MeasurableSpace X] [Fintype I]
  {μ : Measure X} {T : X → X}

def futurePartition (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) (n : ℕ) :
    MeasurePartition μ (Fin n → I) := (ksJoin hT P n).pullback hT

def futureSigma (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) (n : ℕ) :
    MeasurableSpace X := generatedSigmaAlgebra μ (futurePartition hT P n)

def entireFutureSigma (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) :
    MeasurableSpace X := ⨆ n : ℕ, futureSigma hT P n

theorem futureSigma_eq_comap (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) (n : ℕ) :
    futureSigma hT P n = MeasurableSpace.comap T (generatedSigmaAlgebra μ (ksJoin hT P n)) := by
  rw [futureSigma,futurePartition,generatedSigmaAlgebra,generatedSigmaAlgebra,
    MeasurableSpace.comap_generateFrom,MeasurePartition.pullback_cells]
  rw [Set.range_comp' (T ⁻¹' ·) _]

theorem futureSigma_mono (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) :
    Monotone (futureSigma hT P) := by
  intro n m hnm
  simp only [futureSigma_eq_comap]
  exact MeasurableSpace.comap_mono (generatedSigmaAlgebra_ksJoin_mono hT P hnm)

theorem futureSigma_le (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) (n : ℕ) :
    futureSigma hT P n ≤ mX := generatedSigmaAlgebra_le _

theorem entropy_futurePartition (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) (n : ℕ) :
    entropy μ (futurePartition hT P n).cells = ksEntropySeq hT P n :=
  entropy_pullback hT _

theorem ksJoinCells_cons (P : MeasurePartition μ I) (n : ℕ) (i : I) (f : Fin n → I) :
    ksJoinCells P.cells T (n+1) (Fin.cons i f) =
      P.cells i ∩ T ⁻¹' ksJoinCells P.cells T n f := by
  ext x
  simp only [ksJoinCells,mem_iInter,mem_preimage,mem_inter_iff]
  constructor
  · intro hx
    refine ⟨by simpa using hx 0,fun k => ?_⟩
    simpa only [Fin.cons_succ,Fin.val_succ,Function.iterate_succ_apply] using hx k.succ
  · rintro ⟨hx,hf⟩ k
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa using hx
    · simpa only [Fin.cons_succ,Fin.val_succ,Function.iterate_succ_apply] using hf j

variable [IsProbabilityMeasure μ]

theorem ksEntropySeq_succ_eq_add_future_condEntropy [StandardBorelSpace X]
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) (n : ℕ) :
    ksEntropySeq hT P (n+1) = ksEntropySeq hT P n + condEntropy μ (futureSigma hT P n) P.cells := by
  have he : ksEntropySeq hT P (n+1) =
      entropy μ (joinCells (futurePartition hT P n).cells P.cells) := by
    rw [ksEntropySeq,ksJoin_cells,← entropy_reindex μ (Fin.consEquiv fun _ : Fin (n+1) => I)]
    simp only [entropy,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (Fin.consEquiv fun _ : Fin (n+1) => I) (i,f) = Fin.cons i f from rfl,
      ksJoinCells_cons,joinCells_apply]
    simp only [futurePartition,MeasurePartition.pullback_cells,ksJoin_cells,inter_comm]
  rw [he,entropy_join_eq_add_condEntropyGivenPartition,
    entropy_futurePartition,condEntropyGivenPartition_eq_condEntropy_generated]
  · rfl
  · exact P.measurable

theorem ksEntropySeq_eq_sum_future_condEntropy [StandardBorelSpace X]
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) (n : ℕ) :
    ksEntropySeq hT P n = ∑ k ∈ Finset.range n, condEntropy μ (futureSigma hT P k) P.cells := by
  induction n with
  | zero => simp
  | succ n ih => rw [ksEntropySeq_succ_eq_add_future_condEntropy,ih,Finset.sum_range_succ]

theorem ksEntropyPartition_eq_condEntropy_entireFuture [StandardBorelSpace X] [Nonempty I]
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ I) :
    ksEntropyPartition hT P = condEntropy μ (entireFutureSigma hT P) P.cells := by
  have hlim := condEntropy_tendsto_iSup (futureSigma hT P) (futureSigma_mono hT P)
    (futureSigma_le hT P) P
  have hcesaro := hlim.cesaro
  have he : (fun n : ℕ => (n⁻¹ : ℝ) *
      ∑ k ∈ Finset.range n, condEntropy μ (futureSigma hT P k) P.cells) =
      (fun n : ℕ => ksEntropySeq hT P n / n) := by
    funext n
    rw [← ksEntropySeq_eq_sum_future_condEntropy,div_eq_mul_inv,mul_comm]
  rw [he] at hcesaro
  exact tendsto_nhds_unique (tendsto_ksEntropySeq hT P) hcesaro

end ErgodicTheory.Entropy
