import VV.BBEKActualKernelOverlap

/-! The actual arithmetic overlap branches cover each chart intersection.
Their conditional-kernel identities descend to a single conull subset of the
quotient measure; the countable arithmetic group is used explicitly. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKOverlapDescent
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKGaussTransition
  BBEKLeafwiseKernel BBEKLeafwiseChart BBEKLeafwiseOverlap BBEKLeafwiseAtlas
  BBEKChartMeasureOverlap BBEKLocalRootFamily BBEKActualKernelOverlap
  BBEKUniformPlaques

def branchPoint (c d : Chart) (γ : Gamma) : overlapSet c d γ → X :=
  c.domain.restrict (quotientCoordinates c.base) ∘ branchSource c d γ

theorem branchPoint_embedding (c d : Chart) (γ : Gamma) :
    MeasurableEmbedding (branchPoint c d γ) :=
  c.embedding.measurableEmbedding.comp (branchSource_embedding c d γ)

def branchImage (c d : Chart) (γ : Gamma) : Set X := range (branchPoint c d γ)

theorem measurableSet_branchImage (c d : Chart) (γ : Gamma) :
    MeasurableSet (branchImage c d γ) := (branchPoint_embedding c d γ).measurableSet_range

/-- Every point in the actual chart intersection belongs to an arithmetic
branch. In particular no exceptional geometric overlap is discarded. -/
theorem iUnion_branchImage (c d : Chart) :
    ⋃ γ : Gamma, branchImage c d γ = c.image ∩ d.image := by
  apply subset_antisymm
  · intro q hq
    obtain ⟨γ,p,rfl⟩ := mem_iUnion.mp hq
    refine ⟨⟨branchSource c d γ p, (branchSource c d γ p).property,rfl⟩,?_⟩
    refine ⟨branchTarget c d γ p,(branchTarget c d γ p).property,?_⟩
    exact congrFun (branch_quotient_eq c d γ).symm p
  · rintro q ⟨⟨p,hpc,hpq⟩,⟨z,hzd,hzq⟩⟩
    obtain ⟨γ,b,hb,hz⟩ := exists_transition_of_quotient_eq c.base d.base (hpq.trans hzq.symm)
    have hsource : sourceParams (overlapMatrix c d γ) (b,(splitCoordinates p).2) = p := by
      unfold sourceParams
      rw [hb]
      exact splitCoordinates.symm_apply_apply p
    have htarget : targetParams (overlapMatrix c d γ) (b,(splitCoordinates p).2) = z := by
      apply splitCoordinates.injective
      simp only [targetParams,Homeomorph.apply_symm_apply]
      exact hz.symm
    have hm : (b,(splitCoordinates p).2) ∈ overlapSet c d γ := by
      change sourceParams _ _ ∈ c.domain ∧ targetParams _ _ ∈ d.domain
      rw [hsource,htarget]
      exact ⟨hpc,hzd⟩
    refine mem_iUnion.mpr ⟨γ,⟨(b,(splitCoordinates p).2),hm⟩,?_⟩
    change quotientCoordinates c.base (sourceParams _ _) = q
    rw [hsource,hpq]

/-- The product-space branch measure is exactly the coordinate pushforward of
the original quotient measure pulled back through the injective branch chart. -/
theorem branchMeasure_eq (μ : Measure X) (c d : Chart) (γ : Gamma) :
    branchMeasure μ c d γ = (μ.comap (branchPoint c d γ)).map Subtype.val := by
  unfold branchMeasure branchPoint
  rw [Measure.comap_comap (fun _ hs => (branchSource_embedding c d γ).measurableSet_image' hs)
    c.embedding.injective (fun _ hs => c.embedding.measurableEmbedding.measurableSet_image' hs)]

/-- Any actual branch a.e. statement descends to the quotient. The witness is
an actual branch point and its full two-chart coordinates. -/
theorem ae_branch_descend (μ : Measure X) (c d : Chart) (γ : Gamma)
    (P : GroupRightDomain (overlapMatrix c d γ) × Leaf → Prop)
    (hP : ∀ᵐ p ∂branchMeasure μ c d γ, P p) :
    ∀ᵐ q ∂μ.restrict (branchImage c d γ),
      ∃ p : overlapSet c d γ, branchPoint c d γ p = q ∧ P p.val := by
  rw [branchMeasure_eq] at hP
  have hh := ae_of_ae_map measurable_subtype_coe.aemeasurable hP
  unfold branchImage
  rw [← (branchPoint_embedding c d γ).map_comap]
  apply (branchPoint_embedding c d γ).ae_map_iff.mpr
  filter_upwards [hh] with p hp
  exact ⟨p,rfl,hp⟩

def KernelIdentity (μ : Measure X) [IsFiniteMeasure μ] (c d : Chart) (γ : Gamma)
    (b : GroupRightDomain (overlapMatrix c d γ)) : Prop :=
  ((fiberCondition (splitMeasure μ c).condKernel (measurableSet_sourceSet c d γ))
      (groupTransverseBase b)).map (fun u => u + groupRightLeafShift (overlapMatrix c d γ) b) =
    (fiberCondition (splitMeasure μ d).condKernel (measurableSet_targetSet c d γ))
      (groupRightTransverse (overlapMatrix c d γ) b)

/-- One conull subset of the actual chart intersection carries the genuine
conditional-kernel compatibility and a concrete arithmetic overlap witness. -/
theorem ae_kernel_overlap_witness (μ : Measure X) [IsFiniteMeasure μ] (c d : Chart) :
    ∀ᵐ q ∂μ.restrict (c.image ∩ d.image),
      ∃ γ : Gamma, ∃ p : overlapSet c d γ,
        branchPoint c d γ p = q ∧ KernelIdentity μ c d γ p.val.1 := by
  have hall : ∀ᵐ q ∂μ, ∀ γ : Gamma, q ∈ branchImage c d γ →
      ∃ p : overlapSet c d γ, branchPoint c d γ p = q ∧ KernelIdentity μ c d γ p.val.1 := by
    apply ae_all_iff.mpr
    intro γ
    apply (ae_restrict_iff' (measurableSet_branchImage c d γ)).mp
    apply ae_branch_descend μ c d γ (fun p => KernelIdentity μ c d γ p.1)
    exact ae_of_ae_map measurable_fst.aemeasurable (actual_condKernel_overlap μ c d γ)
  apply (ae_restrict_iff' (c.isOpen_image.measurableSet.inter d.isOpen_image.measurableSet)).mpr
  filter_upwards [hall] with q hq hmem
  rw [← iUnion_branchImage] at hmem
  obtain ⟨γ,hγ⟩ := mem_iUnion.mp hmem
  obtain ⟨p,hpq,hp⟩ := hq γ hγ
  exact ⟨γ,p,hpq,hp⟩

theorem chartCoordinates_branch_source (c d : Chart) (γ : Gamma) (p : overlapSet c d γ) :
    chartCoordinates c (branchPoint c d γ p) = sourceParams (overlapMatrix c d γ) p.val :=
  chartCoordinates_apply c (branchSource c d γ p)

theorem chartCoordinates_branch_target (c d : Chart) (γ : Gamma) (p : overlapSet c d γ) :
    chartCoordinates d (branchPoint c d γ p) = targetParams (overlapMatrix c d γ) p.val := by
  change chartCoordinates d ((c.domain.restrict (quotientCoordinates c.base) ∘ branchSource c d γ) p) = _
  rw [branch_quotient_eq]
  exact chartCoordinates_apply d (branchTarget c d γ p)

/-- Moving the center along the leaf leaves the same arithmetic branch in
force; the arithmetic matrix is independent of the leaf parameter. -/
theorem sourceParams_add_leaf (g : G) (p : GroupRightDomain g × Leaf) (u : Leaf) :
    sourceParams g (p.1,p.2+u) = leafShift (sourceParams g p) u := by
  apply splitCoordinates.injective
  simp only [sourceParams,leafShift,Homeomorph.apply_symm_apply]
  exact Prod.ext rfl (add_comm _ _)

theorem targetParams_add_leaf (g : G) (p : GroupRightDomain g × Leaf) (u : Leaf) :
    targetParams g (p.1,p.2+u) = leafShift (targetParams g p) u := by
  apply splitCoordinates.injective
  simp only [targetParams,leafShift,Homeomorph.apply_symm_apply,transition]
  apply Prod.ext
  · rfl
  · dsimp only
    abel

/-- A common safe centered set is contained in both actual branch sections.
This is the geometric fact needed to restrict the kernel identity to a common
ball, even when the two charts have different transverse domains. -/
theorem common_set_mem_sections (c d : Chart) (γ : Gamma) (p : overlapSet c d γ)
    {B : Set Leaf}
    (hc : ∀ u ∈ B, leafShift (sourceParams (overlapMatrix c d γ) p.val) u ∈ c.domain)
    (hd : ∀ u ∈ B, leafShift (targetParams (overlapMatrix c d γ) p.val) u ∈ d.domain) :
    (fun v : Leaf => v-p.val.2) ⁻¹' B ⊆
        Prod.mk (groupTransverseBase p.val.1) ⁻¹' sourceSet c d γ ∧
      (fun v : Leaf => v-(p.val.2+groupRightLeafShift (overlapMatrix c d γ) p.val.1)) ⁻¹' B ⊆
        Prod.mk (groupRightTransverse (overlapMatrix c d γ) p.val.1) ⁻¹' targetSet c d γ := by
  have hm (u : Leaf) (hu : u ∈ B) : (p.val.1,p.val.2+u) ∈ overlapSet c d γ := by
    change sourceParams _ _ ∈ c.domain ∧ targetParams _ _ ∈ d.domain
    rw [sourceParams_add_leaf,targetParams_add_leaf]
    exact ⟨hc u hu,hd u hu⟩
  constructor
  · intro v hv
    refine ⟨⟨(p.val.1,p.val.2+(v-p.val.2)),hm _ hv⟩,?_⟩
    change splitCoordinates (sourceParams _ _) = _
    simp only [sourceParams,Homeomorph.apply_symm_apply]
    apply Prod.ext
    · rfl
    · dsimp only
      abel
  · intro v hv
    let u := v-(p.val.2+groupRightLeafShift (overlapMatrix c d γ) p.val.1)
    refine ⟨⟨(p.val.1,p.val.2+u),hm u hv⟩,?_⟩
    change splitCoordinates (targetParams _ _) = _
    simp only [targetParams,Homeomorph.apply_symm_apply,transition]
    apply Prod.ext
    · rfl
    · dsimp [u]
      abel

theorem localLeafKernel_eq_splitMeasure (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    localLeafKernel μ c = (splitMeasure μ c).condKernel := by
  unfold localLeafKernel leafKernel
  exact (condKernel_congr (splitMeasure_eq μ c)).symm

theorem localMeasure_branch_source (μ : Measure X) [IsFiniteMeasure μ]
    (c d : Chart) (γ : Gamma) (p : overlapSet c d γ) :
    localMeasure μ c (branchPoint c d γ p) =
      ((splitMeasure μ c).condKernel (groupTransverseBase p.val.1)).map (fun v => v-p.val.2) := by
  unfold localMeasure
  rw [chartCoordinates_branch_source]
  simp only [sourceParams,Homeomorph.apply_symm_apply,centeredLeafKernel_apply]
  rw [localLeafKernel_eq_splitMeasure]

theorem localMeasure_branch_target (μ : Measure X) [IsFiniteMeasure μ]
    (c d : Chart) (γ : Gamma) (p : overlapSet c d γ) :
    localMeasure μ d (branchPoint c d γ p) =
      ((splitMeasure μ d).condKernel (groupRightTransverse (overlapMatrix c d γ) p.val.1)).map
        (fun v => v-(p.val.2+groupRightLeafShift (overlapMatrix c d γ) p.val.1)) := by
  unfold localMeasure
  rw [chartCoordinates_branch_target]
  simp only [targetParams,Homeomorph.apply_symm_apply,centeredLeafKernel_apply,transition]
  rw [localLeafKernel_eq_splitMeasure]

end VV.BBEKOverlapDescent



