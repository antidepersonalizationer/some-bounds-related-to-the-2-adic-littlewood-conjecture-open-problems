import VV.BBEKOverlapDescent
import VV.BBEKCenteredOverlap
import VV.BBEKPlaqueSelection

/-! Actual projective agreement of centered leaf probabilities on every
common safe ball, almost everywhere for the original quotient measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKSafeBallCompatibility
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKGaussTransition
  BBEKLeafwiseKernel BBEKLeafwiseChart BBEKLeafwiseOverlap BBEKLeafwiseAtlas
  BBEKChartMeasureOverlap BBEKLocalRootFamily BBEKActualKernelOverlap
  BBEKUniformPlaques BBEKOverlapDescent BBEKPlaqueSelection BBEKCenteredOverlap

theorem safeImage_subset_image (c : Chart) {r : ℝ} (hr : 0 ≤ r) :
    safeImage c r ⊆ c.image := by
  intro q hq
  have hc := chartCoordinates_safe hr hq
  refine ⟨chartCoordinates c q,?_,hc.1⟩
  simpa only [leafShift_zero] using hc.2 0 (by simpa only [norm_zero] using hr)

/-- At every good overlap point, all common safe centered balls inherit
projective compatibility from the genuine disintegration identity. -/
theorem projective_on_safe_ball (μ : Measure X) [IsFiniteMeasure μ]
    (c d : Chart) (γ : Gamma) (p : overlapSet c d γ)
    (hker : KernelIdentity μ c d γ p.val.1)
    {r : ℝ} (hr : 0 < r)
    (hc : branchPoint c d γ p ∈ safeImage c r)
    (hd : branchPoint c d γ p ∈ safeImage d r)
    (hposc : 0 < localMeasure μ c (branchPoint c d γ p) (ball 0 r))
    (hposd : 0 < localMeasure μ d (branchPoint c d γ p) (ball 0 r)) :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
      (localMeasure μ c (branchPoint c d γ p)).restrict (ball 0 r) =
        a • (localMeasure μ d (branchPoint c d γ p)).restrict (ball 0 r) := by
  let g := overlapMatrix c d γ
  let M := (splitMeasure μ c).condKernel (groupTransverseBase p.val.1)
  let N := (splitMeasure μ d).condKernel (groupRightTransverse g p.val.1)
  let s := Prod.mk (groupTransverseBase p.val.1) ⁻¹' sourceSet c d γ
  let t := Prod.mk (groupRightTransverse g p.val.1) ⁻¹' targetSet c d γ
  have hs : MeasurableSet s := measurable_prodMk_left (measurableSet_sourceSet c d γ)
  have ht : MeasurableSet t := measurable_prodMk_left (measurableSet_targetSet c d γ)
  have hc' := (chartCoordinates_safe hr.le hc).2
  have hd' := (chartCoordinates_safe hr.le hd).2
  rw [chartCoordinates_branch_source] at hc'
  rw [chartCoordinates_branch_target] at hd'
  have hsub := common_set_mem_sections c d γ p
    (B := ball 0 r)
    (fun u hu => hc' u (by exact (show ‖u‖ < r by simpa only [mem_ball,dist_zero_right] using hu).le))
    (fun u hu => hd' u (by exact (show ‖u‖ < r by simpa only [mem_ball,dist_zero_right] using hu).le))
  have he := normalized_centered_restrictions_eq_of_translate M N hs ht
    (isOpen_ball.measurableSet : MeasurableSet (ball (0 : Leaf) r))
    p.val.2 (groupRightLeafShift g p.val.1) hsub.1 hsub.2 hker
  have hMc : 0 < M s := by
    apply hposc.trans_le
    rw [localMeasure_branch_source]
    rw [Measure.map_apply (show Measurable (fun v : Leaf => v-p.val.2) from
      measurable_id.sub measurable_const) (isOpen_ball.measurableSet : MeasurableSet (ball (0 : Leaf) r))]
    exact measure_mono hsub.1
  have hNd : 0 < N t := by
    apply hposd.trans_le
    rw [localMeasure_branch_target]
    rw [Measure.map_apply (show Measurable (fun v : Leaf =>
      v-(p.val.2+groupRightLeafShift (overlapMatrix c d γ) p.val.1)) from
      measurable_id.sub measurable_const) (isOpen_ball.measurableSet : MeasurableSet (ball (0 : Leaf) r))]
    exact measure_mono hsub.2
  have hMf : M s ≠ ∞ := measure_ne_top M s
  have hNf : N t ≠ ∞ := measure_ne_top N t
  refine ⟨M s*(N t)⁻¹,mul_ne_zero hMc.ne' (ENNReal.inv_ne_zero.mpr hNf),
    ENNReal.mul_ne_top hMf (ENNReal.inv_ne_top.mpr hNd.ne'),?_⟩
  rw [localMeasure_branch_source,localMeasure_branch_target]
  calc
    _ = M s • ((M s)⁻¹ • (M.map (fun v => v-p.val.2)).restrict (ball 0 r)) := by
      rw [smul_smul,ENNReal.mul_inv_cancel hMc.ne' hMf,one_smul]
    _ = _ := by rw [he,smul_smul]

/-- The same conull subset works simultaneously for every radius. There are
no independently chosen uncountable exceptional sets. -/
theorem ae_projective_on_safe_balls (μ : Measure X) [IsFiniteMeasure μ] (c d : Chart) :
    ∀ᵐ q ∂μ, ∀ r : ℝ, 0 < r → q ∈ safeImage c r → q ∈ safeImage d r →
      ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧
        (localMeasure μ c q).restrict (ball 0 r) = a • (localMeasure μ d q).restrict (ball 0 r) := by
  have hker := (ae_restrict_iff'
    (c.isOpen_image.measurableSet.inter d.isOpen_image.measurableSet)).mp
      (ae_kernel_overlap_witness μ c d)
  have hc := (ae_restrict_iff' c.isOpen_image.measurableSet).mp (ae_localMeasure_ball_pos μ c)
  have hd := (ae_restrict_iff' d.isOpen_image.measurableSet).mp (ae_localMeasure_ball_pos μ d)
  filter_upwards [hker,hc,hd] with q hk hpc hpd r hr hrc hrd
  have hqc := safeImage_subset_image c hr.le hrc
  have hqd := safeImage_subset_image d hr.le hrd
  obtain ⟨γ,p,hpq,hp⟩ := hk ⟨hqc,hqd⟩
  subst q
  exact projective_on_safe_ball μ c d γ p hp hr hrc hrd (hpc hqc r hr) (hpd hqd r hr)

end VV.BBEKSafeBallCompatibility

