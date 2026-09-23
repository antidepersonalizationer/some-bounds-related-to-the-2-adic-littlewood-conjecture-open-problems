import VV.Entropy.SmallPartition
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Real

/-! Compact cores of a finite partition, with small lost mass and uniform
separation between distinct cores. -/

noncomputable section
open Set MeasureTheory Function
open scoped Topology

namespace ErgodicTheory.Entropy
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem compact_cores_separated {m : ℕ} (K : Fin m → Set X)
    (hK : ∀ i, IsCompact (K i)) (hd : Pairwise (Disjoint on K)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, ρ ≤ dist x y := by
  let A : Set (X × X) := ⋃ p : {p : Fin m × Fin m // p.1 ≠ p.2}, K p.val.1 ×ˢ K p.val.2
  have hc : IsCompact A := isCompact_iUnion (fun p => (hK p.val.1).prod (hK p.val.2))
  have hp : ∀ z ∈ A, 0 < dist z.1 z.2 := by
    rintro z hz
    obtain ⟨p,hz⟩ := mem_iUnion.mp hz
    apply dist_pos.mpr
    intro he
    exact Set.disjoint_left.mp (hd p.property) hz.1 (he ▸ hz.2)
  rcases A.eq_empty_or_nonempty with he | hne
  · refine ⟨1,by norm_num,?_⟩
    intro i j hij x hx y hy
    have hz : (x,y) ∈ A := mem_iUnion.mpr ⟨⟨(i,j),hij⟩,hx,hy⟩
    simpa [he] using hz
  · obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn hne (continuous_fst.dist continuous_snd).continuousOn
    refine ⟨dist z.1 z.2,hp z hz,?_⟩
    intro i j hij x hx y hy
    exact hmin (show (x,y) ∈ A from mem_iUnion.mpr ⟨⟨(i,j),hij⟩,hx,hy⟩)

theorem exists_compact_partition_cores (μ : Measure X) [IsProbabilityMeasure μ]
    {m : ℕ} (P : FixedPartition X (Fin m)) {η : ℝ} (hη : 0 < η) :
    ∃ K : Fin m → Set X, (∀ i, K i ⊆ P.cells i) ∧ (∀ i, IsCompact (K i)) ∧
      Pairwise (Disjoint on K) ∧ μ.real (⋃ i, K i)ᶜ < η ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, ρ ≤ dist x y := by
  have heps : 0 < η / ((m:ℝ)+1) := by positivity
  have hcore (i : Fin m) : ∃ K, K ⊆ P.cells i ∧ IsCompact K ∧
      μ (P.cells i \ K) < ENNReal.ofReal (η / ((m:ℝ)+1)) :=
    (P.measurable i).exists_isCompact_diff_lt (measure_ne_top μ _) (by positivity)
  choose K hsub hc hmass using hcore
  have hd : Pairwise (Disjoint on K) :=
    fun i j hij => (P.disjoint hij).mono (hsub i) (hsub j)
  refine ⟨K,hsub,hc,hd,?_,compact_cores_separated K hc hd⟩
  have hcover : (⋃ i, K i)ᶜ ⊆ ⋃ i, P.cells i \ K i := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (P.cover ▸ mem_univ x)
    refine mem_iUnion.mpr ⟨i,hi,?_⟩
    exact fun h => hx (mem_iUnion.mpr ⟨i,h⟩)
  have hm (i : Fin m) : μ.real (P.cells i \ K i) < η / ((m:ℝ)+1) := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr (hmass i)
    simpa only [ENNReal.toReal_ofReal heps.le] using hh
  calc
    μ.real (⋃ i, K i)ᶜ ≤ μ.real (⋃ i, P.cells i \ K i) := measureReal_mono hcover
    _ ≤ ∑ i, μ.real (P.cells i \ K i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin m, η / ((m:ℝ)+1) := Finset.sum_le_sum (fun i _ => (hm i).le)
    _ = (m:ℝ) * (η / ((m:ℝ)+1)) := by simp
    _ < η := by
      have hmpos : (0:ℝ) < m+1 := by positivity
      rw [← mul_div_assoc,div_lt_iff₀ hmpos]
      nlinarith

end ErgodicTheory.Entropy
