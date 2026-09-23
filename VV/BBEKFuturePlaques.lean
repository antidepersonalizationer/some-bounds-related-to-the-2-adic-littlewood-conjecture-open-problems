import VV.BBEKStandardBorel
import VV.BBEKBowenMetric
import VV.BBEKEntropyExpansive
import VV.Entropy.FutureKernelSupport
import VV.Entropy.BowenGenerator
import VV.Entropy.SmallPartition

/-! Future conditional kernels live on actual center-stable plaques.
Only the explicitly stated upper-triangular conclusion is asserted:
the diagonal part has not been removed, nor has a nonatomicity or
translation-invariance conclusion been inferred from non-Diracness. -/

noncomputable section
open Set Metric MeasureTheory ProbabilityTheory Function
open scoped Topology Uniformity ENNReal

namespace VV.BBEKFuturePlaques
open BBEKDynamics BBEKQuotient BBEKTopology BBEKStandardBorel
open BBEKEntropyExpansion BBEKEntropyNets BBEKFiniteBowen
open BBEKBowenLift BBEKEntropyExpansive ErgodicTheory.Entropy
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem compact_small_future_same_plaque {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : 0 < t) (hf : MapsTo (timeMap t) Y Y) :
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x y : Y,
      (∀ n : ℕ, dist ((restrictedTimeMap hf)^[n+1] x)
        ((restrictedTimeMap hf)^[n+1] y) < ρ) →
      ∃ g : G, g.1 1 0 = 0 ∧ g.2 1 0 = 0 ∧
        (restrictedTimeMap hf y : X) = g • (restrictedTimeMap hf x : X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  obtain ⟨r,hr,ho,hd,hlift⟩ := compact_forward_lift hY (psi t 1)
  let V : Set (Y × Y) := (fun p : Y × Y => ((p.1 : X),(p.2 : X))) ⁻¹' displacementRelation r
  have hV : IsOpen V := ho.preimage (continuous_subtype_val.prodMap continuous_subtype_val)
  have hu : V ∈ 𝓤 Y := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    apply hV.mem_nhdsSet.mpr
    rintro ⟨a,b⟩ (hab : a=b)
    subst b
    exact hd a
  obtain ⟨ρ,hρ,hρV⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨ρ,hρ,?_⟩
  intro x y hxy
  have he (z : Y) (n : ℕ) :
      (psi t 1)^n • (restrictedTimeMap hf z : X) =
        ((restrictedTimeMap hf)^[n+1] z : X) := by
    rw [← restrictedTimeMap_iterate_pow hf (restrictedTimeMap hf z) n,
      Function.iterate_succ_apply]
  obtain ⟨g,hg,hgn⟩ := hlift (restrictedTimeMap hf x) (restrictedTimeMap hf y)
    (fun n => by rw [he]; exact ((restrictedTimeMap hf)^[n+1] x).property)
    (fun n => by simpa only [he] using hρV (hxy n))
  have hzero := lower_zero_of_forward_bounded ht g r (fun n => (hgn n).1.le)
  exact ⟨g,hzero.1,hzero.2,by simpa using (hgn 0).2⟩

theorem futureKernel_same_actual_plaque {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : 0 < t) (hf : MapsTo (timeMap t) Y Y) :
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    letI : StandardBorelSpace Y := hY.measurableSet.standardBorel
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (μ : Measure Y) [IsProbabilityMeasure μ]
      (hT : MeasurePreserving (restrictedTimeMap hf) μ μ)
      (m : ℕ) (P : MeasurePartition μ (Fin m)),
      (∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < ρ) →
      ∀ᵐ x ∂μ, ∀ᵐ y ∂condExpKernel μ (entireFutureSigma hT P) x,
        ∃ g : G, g.1 1 0 = 0 ∧ g.2 1 0 = 0 ∧
          (restrictedTimeMap hf y : X) = g • (restrictedTimeMap hf x : X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : StandardBorelSpace Y := hY.measurableSet.standardBorel
  obtain ⟨ρ,hρ,hplaque⟩ := compact_small_future_same_plaque hY ht hf
  refine ⟨ρ,hρ,?_⟩
  intro μ hμ hT m P hmesh
  filter_upwards [futureKernel_ae_same_cell hT P] with x hx
  filter_upwards [hx] with y hy
  apply hplaque x y
  intro n
  obtain ⟨i,hix,hiy⟩ := hy n
  exact hmesh i _ hix _ hiy

/-- Positive entropy provides an actual conditional kernel with positive
entropy, non-Diracness on a non-null set, and the proved center-stable
plaque constraint.  Both the fine partition and its entropy equality are
constructed from the compact homogeneous dynamics. -/
theorem positive_futureKernel_on_actual_plaques {Y : Set X} (hY : IsCompact Y)
    {t : ℝ} (ht : 0 < t) (hf : MapsTo (timeMap t) Y Y)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (restrictedTimeMap hf) μ μ) (hpos : 0 < ksEntropy hT) :
    letI : StandardBorelSpace Y := hY.measurableSet.standardBorel
    ∃ m : ℕ, ∃ P : MeasurePartition μ (Fin m),
      0 < condEntropy μ (entireFutureSigma hT P) P.cells ∧
      ¬ (∀ᵐ x ∂μ, ∃ y, condExpKernel μ (entireFutureSigma hT P) x = Measure.dirac y) ∧
      ∀ᵐ x ∂μ, ∀ᵐ y ∂condExpKernel μ (entireFutureSigma hT P) x,
        ∃ g : G, g.1 1 0 = 0 ∧ g.2 1 0 = 0 ∧
          (restrictedTimeMap hf y : X) = g • (restrictedTimeMap hf x : X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  letI : StandardBorelSpace Y := hY.measurableSet.standardBorel
  obtain ⟨ρ,hρ,hplaque⟩ := futureKernel_same_actual_plaque hY ht hf
  obtain ⟨r,hr,hcover⟩ := compact_uniformBowenCover hY ht hf
  obtain ⟨m,P,_,hmesh⟩ := exists_small_null_frontier_partition μ (lt_min hρ hr)
  have hmeshρ : ∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < ρ :=
    fun i x hx y hy => (hmesh i x hx y hy).trans_le (min_le_left _ _)
  have hmeshr : ∀ i, ∀ x ∈ P.cells i, ∀ y ∈ P.cells i, dist x y < r :=
    fun i x hx y hy => (hmesh i x hx y hy).trans_le (min_le_right _ _)
  have hp : 0 < ksEntropyPartition hT (P.toMeasurePartition μ) := by
    rw [ksEntropy_eq_of_uniformBowenCover hT P hcover hmeshr] at hpos
    exact EReal.coe_pos.mp hpos
  have hm : m ≠ 0 := by
    intro he
    subst m
    have hc := congrArg μ P.cover
    have hz : (0 : ℝ≥0∞) = 1 := by
      simpa only [iUnion_of_empty,measure_empty,measure_univ] using hc
    exact zero_ne_one hz
  letI : NeZero m := ⟨hm⟩
  have hc : 0 < condEntropy μ (entireFutureSigma hT (P.toMeasurePartition μ)) P.cells := by
    change 0 < condEntropy μ (entireFutureSigma hT (P.toMeasurePartition μ)) (P.toMeasurePartition μ).cells
    rwa [← ksEntropyPartition_eq_condEntropy_entireFuture hT (P.toMeasurePartition μ)]
  refine ⟨m,P.toMeasurePartition μ,hc,not_ae_dirac_of_pos_condEntropy μ _ P.cells hc,?_⟩
  exact hplaque μ hT m (P.toMeasurePartition μ) hmeshρ

end VV.BBEKFuturePlaques
