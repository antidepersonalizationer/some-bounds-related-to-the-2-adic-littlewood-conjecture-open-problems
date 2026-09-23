import VV.BBEKOneRootOverlap
import VV.BBEKSafeBallCompatibility

/-! One-root disintegrations agree on actual common safe plaques. Arithmetic
branches are countable; all radii use the same conull subset. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKOneRootSafe
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKGaussTransition
  BBEKLeafwiseKernel BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKLeafwiseOverlap
  BBEKChartMeasureOverlap BBEKLocalRootFamily BBEKActualKernelOverlap
  BBEKRootLeafKernel BBEKOneRootGeometry BBEKOneRootLocal BBEKOneRootOverlap
  BBEKOverlapDescent BBEKUniformPlaques BBEKPlaqueSelection BBEKCenteredOverlap
  BBEKSafeBallCompatibility
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

section Branch
variable {B U D : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]
  [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D]

variable (s : GroupParams ≃ₜ B × U) (μ : Measure X) [IsFiniteMeasure μ]
  (c d : Chart) (γ : Gamma)
  (e : GroupRightDomain (overlapMatrix c d γ) × Leaf ≃ₜ D × U)
  (f h : D → B) (a : D → U)

def KernelIdentityWith (p : GroupRightDomain (overlapMatrix c d γ) × Leaf) : Prop :=
  ((fiberCondition (splitMeasureWith s μ c).condKernel (measurableSet_sourceSetWith s c d γ))
      (f (e p).1)).map (fun u => u+a (e p).1)=
    (fiberCondition (splitMeasureWith s μ d).condKernel (measurableSet_targetSetWith s c d γ)) (h (e p).1)

variable (hsource : ∀p, s (sourceParams (overlapMatrix c d γ) p)=Prod.map f id (e p))
  (htarget : ∀p, s (targetParams (overlapMatrix c d γ) p)=((h (e p).1),(e p).2+a (e p).1))

include hsource in
theorem localMeasureWith_branch_source (p : overlapSet c d γ) :
    localMeasureWith s μ c (branchPoint c d γ p)=
      ((splitMeasureWith s μ c).condKernel (f (e p.val).1)).map (fun v => v-(e p.val).2) := by
  unfold localMeasureWith
  rw [chartCoordinates_branch_source,hsource,
    condKernel_congr (splitMeasureWith_eq s μ c)]
  rfl

include htarget in
theorem localMeasureWith_branch_target (p : overlapSet c d γ) :
    localMeasureWith s μ d (branchPoint c d γ p)=
      ((splitMeasureWith s μ d).condKernel (h (e p.val).1)).map
        (fun v => v-((e p.val).2+a (e p.val).1)) := by
  unfold localMeasureWith
  rw [chartCoordinates_branch_target,htarget,
    condKernel_congr (splitMeasureWith_eq s μ d)]
  rfl

include hsource htarget in
theorem common_set_mem_sectionsWith (axis : U → Leaf)
    (hshift : ∀p u, e (p.1,p.2+axis u)=((e p).1,(e p).2+u))
    (p : overlapSet c d γ) {T : Set U}
    (hc : ∀u∈T, leafShift (sourceParams (overlapMatrix c d γ) p.val) (axis u)∈c.domain)
    (hd : ∀u∈T, leafShift (targetParams (overlapMatrix c d γ) p.val) (axis u)∈d.domain) :
    (fun v : U => v-(e p.val).2) ⁻¹' T ⊆
      Prod.mk (f (e p.val).1) ⁻¹' sourceSetWith s c d γ ∧
    (fun v : U => v-((e p.val).2+a (e p.val).1)) ⁻¹' T ⊆
      Prod.mk (h (e p.val).1) ⁻¹' targetSetWith s c d γ := by
  have hm (u : U) (hu : u∈T) : (p.val.1,p.val.2+axis u)∈overlapSet c d γ := by
    change sourceParams _ _∈c.domain ∧ targetParams _ _∈d.domain
    rw [sourceParams_add_leaf,targetParams_add_leaf]
    exact ⟨hc u hu,hd u hu⟩
  constructor
  · intro v hv
    refine ⟨⟨(p.val.1,p.val.2+axis (v-(e p.val).2)),hm _ hv⟩,?_⟩
    change s (sourceParams _ _)=_
    rw [hsource,hshift]
    apply Prod.ext
    · rfl
    · dsimp only [Prod.map,id_eq]
      abel
  · intro v hv
    let u := v-((e p.val).2+a (e p.val).1)
    refine ⟨⟨(p.val.1,p.val.2+axis u),hm u hv⟩,?_⟩
    change s (targetParams _ _)=_
    rw [htarget,hshift]
    apply Prod.ext
    · rfl
    · dsimp [u]
      abel

include hsource htarget in
theorem projective_on_safe_ballWith (axis : U → Leaf)
    (hnorm : ∀u, ‖axis u‖≤‖u‖)
    (hshift : ∀p u, e (p.1,p.2+axis u)=((e p).1,(e p).2+u))
    (p : overlapSet c d γ) (hker : KernelIdentityWith s μ c d γ e f h a p.val)
    {r : ℝ} (hr : 0<r)
    (hc : branchPoint c d γ p∈safeImage c r)
    (hd : branchPoint c d γ p∈safeImage d r)
    (hposc : 0<localMeasureWith s μ c (branchPoint c d γ p) (ball 0 r))
    (hposd : 0<localMeasureWith s μ d (branchPoint c d γ p) (ball 0 r)) :
    ∃ k : ℝ≥0∞, k≠0 ∧ k≠∞ ∧
      (localMeasureWith s μ c (branchPoint c d γ p)).restrict (ball 0 r)=
        k • (localMeasureWith s μ d (branchPoint c d γ p)).restrict (ball 0 r) := by
  let M := (splitMeasureWith s μ c).condKernel (f (e p.val).1)
  let N := (splitMeasureWith s μ d).condKernel (h (e p.val).1)
  let S := Prod.mk (f (e p.val).1) ⁻¹' sourceSetWith s c d γ
  let T := Prod.mk (h (e p.val).1) ⁻¹' targetSetWith s c d γ
  have hS : MeasurableSet S := measurable_prodMk_left (measurableSet_sourceSetWith s c d γ)
  have hT : MeasurableSet T := measurable_prodMk_left (measurableSet_targetSetWith s c d γ)
  have hc' := (chartCoordinates_safe hr.le hc).2
  have hd' := (chartCoordinates_safe hr.le hd).2
  rw [chartCoordinates_branch_source] at hc'
  rw [chartCoordinates_branch_target] at hd'
  have hsub := common_set_mem_sectionsWith s c d γ e f h a hsource htarget axis hshift p
    (T := ball 0 r)
    (fun u hu => hc' (axis u) ((hnorm u).trans
      (show ‖u‖≤r by exact (show ‖u‖<r by simpa only [mem_ball,dist_zero_right] using hu).le)))
    (fun u hu => hd' (axis u) ((hnorm u).trans
      (show ‖u‖≤r by exact (show ‖u‖<r by simpa only [mem_ball,dist_zero_right] using hu).le)))
  have he := normalized_centered_restrictions_eq_of_translate M N hS hT
    (isOpen_ball.measurableSet : MeasurableSet (ball (0 : U) r))
    (e p.val).2 (a (e p.val).1) hsub.1 hsub.2 hker
  have hMc : 0<M S := by
    apply hposc.trans_le
    rw [localMeasureWith_branch_source s μ c d γ e f hsource]
    rw [Measure.map_apply (show Measurable (fun v : U => v-(e p.val).2) from
      measurable_id.sub measurable_const) (isOpen_ball.measurableSet : MeasurableSet (ball (0 : U) r))]
    exact measure_mono hsub.1
  have hNd : 0<N T := by
    apply hposd.trans_le
    rw [localMeasureWith_branch_target s μ c d γ e h a htarget]
    rw [Measure.map_apply (show Measurable (fun v : U => v-((e p.val).2+a (e p.val).1)) from
      measurable_id.sub measurable_const) (isOpen_ball.measurableSet : MeasurableSet (ball (0 : U) r))]
    exact measure_mono hsub.2
  refine ⟨M S*(N T)⁻¹,mul_ne_zero hMc.ne' (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)),
    ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.inv_ne_top.mpr hNd.ne'),?_⟩
  rw [localMeasureWith_branch_source s μ c d γ e f hsource,
    localMeasureWith_branch_target s μ c d γ e h a htarget]
  calc
    _ = M S • ((M S)⁻¹ • (M.map (fun v => v-(e p.val).2)).restrict (ball 0 r)) := by
      rw [smul_smul,ENNReal.mul_inv_cancel hMc.ne' (measure_ne_top _ _),one_smul]
    _ = _ := by rw [he,smul_smul]
end Branch

theorem ae_overlap_witness (μ : Measure X) (c d : Chart)
    (P : ∀γ : Gamma, GroupRightDomain (overlapMatrix c d γ) × Leaf → Prop)
    (hP : ∀γ, ∀ᵐ p ∂branchMeasure μ c d γ, P γ p) :
    ∀ᵐ q ∂μ.restrict (c.image∩d.image),
      ∃γ : Gamma, ∃p : overlapSet c d γ, branchPoint c d γ p=q ∧ P γ p.val := by
  have hall : ∀ᵐ q ∂μ, ∀γ : Gamma, q∈branchImage c d γ →
      ∃p : overlapSet c d γ, branchPoint c d γ p=q ∧ P γ p.val := by
    apply ae_all_iff.mpr
    intro γ
    apply (ae_restrict_iff' (measurableSet_branchImage c d γ)).mp
    exact ae_branch_descend μ c d γ (P γ) (hP γ)
  apply (ae_restrict_iff' (c.isOpen_image.measurableSet.inter d.isOpen_image.measurableSet)).mpr
  filter_upwards [hall] with q hq hmem
  rw [← iUnion_branchImage] at hmem
  obtain ⟨γ,hγ⟩ := mem_iUnion.mp hmem
  obtain ⟨p,hpq,hp⟩ := hq γ hγ
  exact ⟨γ,p,hpq,hp⟩

theorem realBranchSplit_shift (g : G) (p : GroupRightDomain g × Leaf) (u : ℝ) :
    realBranchSplit g (p.1,p.2+(u,0))=((realBranchSplit g p).1,(realBranchSplit g p).2+u) := by
  simp [realBranchSplit]

theorem padicBranchSplit_shift (g : G) (p : GroupRightDomain g × Leaf) (u : Q2) :
    padicBranchSplit g (p.1,p.2+(0,u))=((padicBranchSplit g p).1,(padicBranchSplit g p).2+u) := by
  simp [padicBranchSplit]

theorem ae_real_projective_on_safe_balls (μ : Measure X) [IsFiniteMeasure μ] (c d : Chart) :
    ∀ᵐ q ∂μ, ∀r : ℝ, 0<r → q∈safeImage c r → q∈safeImage d r →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (realLocalMeasure μ c q).restrict (ball 0 r)=a • (realLocalMeasure μ d q).restrict (ball 0 r) := by
  let P := fun (γ : Gamma) => KernelIdentityWith realSplit μ c d γ
    (realBranchSplit _) (realBaseSource _) (realBaseTarget _) (realBranchShift _)
  have hP (γ : Gamma) : ∀ᵐ p ∂branchMeasure μ c d γ, P γ p := by
    have he := actual_real_condKernel_overlap μ c d γ
    exact ae_of_ae_map (realBranchSplit _).measurable.aemeasurable
      (ae_of_ae_map measurable_fst.aemeasurable he)
  have hk := (ae_restrict_iff' (c.isOpen_image.measurableSet.inter d.isOpen_image.measurableSet)).mp
    (ae_overlap_witness μ c d P hP)
  have hc := (ae_restrict_iff' c.isOpen_image.measurableSet).mp (ae_realLocalMeasure_ball_pos μ c)
  have hd := (ae_restrict_iff' d.isOpen_image.measurableSet).mp (ae_realLocalMeasure_ball_pos μ d)
  filter_upwards [hk,hc,hd] with q hk hpc hpd r hr hrc hrd
  have hqc := safeImage_subset_image c hr.le hrc
  have hqd := safeImage_subset_image d hr.le hrd
  obtain ⟨γ,p,hpq,hp⟩ := hk ⟨hqc,hqd⟩
  subst q
  exact projective_on_safe_ballWith realSplit μ c d γ (realBranchSplit _)
    (realBaseSource _) (realBaseTarget _) (realBranchShift _)
    (real_source_identity _) (real_target_identity _) (fun u => (u,0))
    (fun u => by simp [Prod.norm_def]) (realBranchSplit_shift _) p hp hr hrc hrd
    (hpc hqc r hr) (hpd hqd r hr)

theorem ae_padic_projective_on_safe_balls (μ : Measure X) [IsFiniteMeasure μ] (c d : Chart) :
    ∀ᵐ q ∂μ, ∀r : ℝ, 0<r → q∈safeImage c r → q∈safeImage d r →
      ∃a : ℝ≥0∞, a≠0 ∧ a≠∞ ∧
        (padicLocalMeasure μ c q).restrict (ball 0 r)=a • (padicLocalMeasure μ d q).restrict (ball 0 r) := by
  let P := fun (γ : Gamma) => KernelIdentityWith padicSplit μ c d γ
    (padicBranchSplit _) (padicBaseSource _) (padicBaseTarget _) (padicBranchShift _)
  have hP (γ : Gamma) : ∀ᵐ p ∂branchMeasure μ c d γ, P γ p := by
    have he := actual_padic_condKernel_overlap μ c d γ
    exact ae_of_ae_map (padicBranchSplit _).measurable.aemeasurable
      (ae_of_ae_map measurable_fst.aemeasurable he)
  have hk := (ae_restrict_iff' (c.isOpen_image.measurableSet.inter d.isOpen_image.measurableSet)).mp
    (ae_overlap_witness μ c d P hP)
  have hc := (ae_restrict_iff' c.isOpen_image.measurableSet).mp (ae_padicLocalMeasure_ball_pos μ c)
  have hd := (ae_restrict_iff' d.isOpen_image.measurableSet).mp (ae_padicLocalMeasure_ball_pos μ d)
  filter_upwards [hk,hc,hd] with q hk hpc hpd r hr hrc hrd
  have hqc := safeImage_subset_image c hr.le hrc
  have hqd := safeImage_subset_image d hr.le hrd
  obtain ⟨γ,p,hpq,hp⟩ := hk ⟨hqc,hqd⟩
  subst q
  exact projective_on_safe_ballWith padicSplit μ c d γ (padicBranchSplit _)
    (padicBaseSource _) (padicBaseTarget _) (padicBranchShift _)
    (padic_source_identity _) (padic_target_identity _) (fun u => (0,u))
    (fun u => by simp [Prod.norm_def]) (padicBranchSplit_shift _) p hp hr hrc hrd
    (hpc hqc r hr) (hpd hqd r hr)

end VV.BBEKOneRootSafe
