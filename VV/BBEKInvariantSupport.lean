import VV.BBEKPeriodicAmbient

/-! The closed positive-neighborhood support, constructed from a countable
topological basis rather than supplied as an invariant-support hypothesis. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter TopologicalSpace
open scoped Topology
namespace VV.BBEKInvariantSupport

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]

def positiveSupport (μ : Measure Y) : Set Y :=
  {x | ∀ U : Set Y, IsOpen U → x ∈ U → μ U ≠ 0}

theorem positiveSupport_isClosed (μ : Measure Y) : IsClosed (positiveSupport μ) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change ¬ ∀ U : Set Y, IsOpen U → x ∈ U → μ U ≠ 0 at hx
  push_neg at hx
  obtain ⟨U,hU,hxU,hzero⟩ := hx
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy hys
  exact hys U hU hy hzero

theorem ae_positiveSupport [SecondCountableTopology Y] (μ : Measure Y) :
    ∀ᵐ x ∂μ, x ∈ positiveSupport μ := by
  have hh : ∀ᵐ x ∂μ, ∀ U ∈ countableBasis Y, μ U=0 → x ∉ U := by
    apply (ae_ball_iff (countable_countableBasis Y)).mpr
    intro U hU
    by_cases hz : μ U=0
    · have hn : ∀ᵐ x ∂μ, x ∉ U := by simpa only [ae_iff,not_not] using hz
      exact hn.mono (fun x hx _ => hx)
    · exact ae_of_all _ (fun x h => (hz h).elim)
  filter_upwards [hh] with x hx
  intro U hU hxU hzero
  obtain ⟨V,hV,hxV,hVU⟩ := (isBasis_countableBasis Y).mem_nhds_iff.mp (hU.mem_nhds hxU)
  exact hx V hV (measure_mono_null hVU hzero) hxV

theorem positiveSupport_nonempty [SecondCountableTopology Y]
    (μ : Measure Y) [NeZero μ] : (positiveSupport μ).Nonempty :=
  (ae_positiveSupport μ).exists

theorem positiveSupport_subset_of_closed_full [OpensMeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {C : Set Y}
    (hC : IsClosed C) (hfull : μ C=1) : positiveSupport μ ⊆ C := by
  intro x hx
  by_contra hxc
  have hz : μ Cᶜ=0 := by simp [hC.measurableSet,hfull]
  exact hx Cᶜ hC.isOpen_compl hxc hz

theorem positiveSupport_isCompact [OpensMeasurableSpace Y] [T2Space Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {C : Set Y}
    (hC : IsCompact C) (hfull : μ C=1) : IsCompact (positiveSupport μ) :=
  hC.of_isClosed_subset (positiveSupport_isClosed μ)
    (positiveSupport_subset_of_closed_full μ hC.isClosed hfull)

theorem smul_positiveSupport {H : Type*} [Group H] [MulAction H Y]
    [ContinuousConstSMul H Y] [OpensMeasurableSpace Y] [MeasurableConstSMul H Y]
    (μ : Measure Y) [SMulInvariantMeasure H Y μ] (a : H) :
    MapsTo (fun x : Y => a • x) (positiveSupport μ) (positiveSupport μ) := by
  intro x hx U hU hax
  have hp := hx ((fun y : Y => a • y) ⁻¹' U)
    (hU.preimage (continuous_const_smul a)) hax
  rwa [measure_preimage_smul μ a U] at hp

end VV.BBEKInvariantSupport

