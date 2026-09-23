import VV.BBEKKernelRestriction

/-! Positivity of all leaf neighborhoods on one conull set, including after recentering. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace Metric
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafwiseKernel

theorem ae_all_ball_pos {U : Type*} [PseudoMetricSpace U] [SecondCountableTopology U]
    [MeasurableSpace U] (μ : Measure U) :
    ∀ᵐ u ∂μ, ∀ ε : ℝ, 0 < ε → 0 < μ (ball u ε) := by
  have hh : ∀ᵐ u ∂μ, ∀ s ∈ countableBasis U, μ s = 0 → u ∉ s := by
    apply (ae_ball_iff (countable_countableBasis U)).mpr
    intro s hs
    by_cases hz : μ s = 0
    · have hn : ∀ᵐ u ∂μ, u ∉ s := by simpa only [ae_iff, not_not] using hz
      exact hn.mono (fun u hu _ => hu)
    · exact ae_of_all _ (fun u hu => (hz hu).elim)
  filter_upwards [hh] with u hu ε hε
  obtain ⟨s,hs,hus,hsub⟩ := (isBasis_countableBasis U).mem_nhds_iff.mp (ball_mem_nhds u hε)
  have hp : 0 < μ s := pos_iff_ne_zero.mpr (fun hz => hu s hs hz hus)
  exact hp.trans_le (measure_mono hsub)

section Kernel
variable {B U : Type*} [MeasurableSpace B] [MeasurableSpace U] [PseudoMetricSpace U]
  [BorelSpace U] [SecondCountableTopology U]

theorem measurable_kernel_ball (κ : Kernel B U) [IsSFiniteKernel κ] (ε : ℝ) :
    Measurable (fun p : B × U => κ p.1 (ball p.2 ε)) := by
  let κ' : Kernel (B × U) U := κ.comap Prod.fst measurable_fst
  have hs : MeasurableSet {q : (B × U) × U | dist q.2 q.1.2 < ε} :=
    measurableSet_lt (measurable_snd.dist measurable_fst.snd) measurable_const
  exact Kernel.measurable_kernel_prodMk_left (κ := κ') hs

variable [StandardBorelSpace U] [Nonempty U]

/-- The actual joint measure almost surely samples a point in the support of its
conditional leaf measure, simultaneously for every neighborhood radius. -/
theorem condKernel_ae_all_ball_pos (ρ : Measure (B × U)) [IsFiniteMeasure ρ] :
    ∀ᵐ p ∂ρ, ∀ ε : ℝ, 0 < ε → 0 < ρ.condKernel p.1 (ball p.2 ε) := by
  have hn (n : ℕ) : ∀ᵐ p ∂ρ,
      0 < ρ.condKernel p.1 (ball p.2 (1 / (n+1 : ℝ))) := by
    have hm := measurable_kernel_ball ρ.condKernel (1 / (n+1 : ℝ))
    have hh : ∀ᵐ p ∂ρ.fst ⊗ₘ ρ.condKernel,
        0 < ρ.condKernel p.1 (ball p.2 (1 / (n+1 : ℝ))) := by
      apply (Measure.ae_compProd_iff (measurableSet_lt measurable_const hm)).mpr
      apply ae_of_all
      intro b
      exact (ae_all_ball_pos (ρ.condKernel b)).mono (fun u hu => hu _ (by positivity))
    rwa [Measure.disintegrate] at hh
  filter_upwards [ae_all_iff.mpr hn] with p hp ε hε
  obtain ⟨n,hnε⟩ := exists_nat_one_div_lt hε
  exact (hp n).trans_le (measure_mono (ball_subset_ball hnε.le))

end Kernel

open BBEKDynamics
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Recenter the actual conditional leaf probability at the sampled point. -/
def centeredLeafKernel {B : Type*} [MeasurableSpace B] (κ : Kernel B Leaf) [IsSFiniteKernel κ] :
    Kernel (B × Leaf) Leaf where
  toFun p := (κ p.1).map (fun v => v - p.2)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hm (p : B × Leaf) : Measurable (fun v : Leaf => v - p.2) :=
      measurable_id.sub measurable_const
    change Measurable (fun p : B × Leaf => ((κ p.1).map (fun v => v-p.2)) s)
    simp_rw [Measure.map_apply (hm _) hs]
    let κ' : Kernel (B × Leaf) Leaf := κ.comap Prod.fst measurable_fst
    exact Kernel.measurable_kernel_prodMk_left (κ := κ')
      (hs.preimage (measurable_snd.sub measurable_fst.snd))

theorem centeredLeafKernel_apply {B : Type*} [MeasurableSpace B] (κ : Kernel B Leaf)
    [IsSFiniteKernel κ] (p : B × Leaf) : centeredLeafKernel κ p = (κ p.1).map (fun v => v-p.2) := rfl

instance centeredLeafKernel_markov {B : Type*} [MeasurableSpace B] (κ : Kernel B Leaf)
    [IsMarkovKernel κ] : IsMarkovKernel (centeredLeafKernel κ) :=
  ⟨fun p => isProbabilityMeasure_map (measurable_id.sub_const p.2).aemeasurable⟩

theorem centeredLeafKernel_ball {B : Type*} [MeasurableSpace B] (κ : Kernel B Leaf)
    [IsSFiniteKernel κ] (p : B × Leaf) (ε : ℝ) :
    centeredLeafKernel κ p (ball 0 ε) = κ p.1 (ball p.2 ε) := by
  have hm : Measurable (fun v : Leaf => v-p.2) := measurable_id.sub measurable_const
  rw [centeredLeafKernel_apply, Measure.map_apply hm (isOpen_ball.measurableSet :
    MeasurableSet (ball (0 : Leaf) ε))]
  congr 1
  ext v
  simp [mem_ball, dist_eq_norm]

theorem centeredLeafKernel_ae_pos {B : Type*} [MeasurableSpace B]
    (ρ : Measure (B × Leaf)) [IsFiniteMeasure ρ] :
    ∀ᵐ p ∂ρ, ∀ ε : ℝ, 0 < ε → 0 < centeredLeafKernel ρ.condKernel p (ball 0 ε) := by
  simpa only [centeredLeafKernel_ball] using condKernel_ae_all_ball_pos ρ

end VV.BBEKLeafwiseKernel
