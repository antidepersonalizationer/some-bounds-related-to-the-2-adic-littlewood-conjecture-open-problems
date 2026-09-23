import VV.BBEKChartMeasureOverlap
import VV.BBEKLocalRootFamily

/-! Disintegration compatibility for the two actual pullbacks of a quotient
measure on each arithmetic overlap branch. No compatibility premise is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKActualKernelOverlap
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKGaussTransition
  BBEKLeafwiseKernel BBEKLeafwiseChart BBEKLeafwiseOverlap BBEKLeafwiseAtlas
  BBEKChartMeasureOverlap BBEKLocalRootFamily

private theorem map_comap_map_comp {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) {f : A → B} {g : C → A}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g) :
    (μ.comap g).map (f ∘ g) = (μ.map f).restrict (range (f ∘ g)) := by
  have hpre : f ⁻¹' range (f ∘ g) = range g := by
    ext a
    constructor
    · rintro ⟨z,hz⟩
      exact ⟨z,hf.injective hz⟩
    · rintro ⟨z,rfl⟩
      exact ⟨z,rfl⟩
  rw [← Measure.map_map hf.measurable hg.measurable,hg.map_comap,hf.restrict_map,hpre]

def splitEmbedding (c : Chart) : c.domain → Transverse × Leaf :=
  splitCoordinates ∘ Subtype.val

theorem splitEmbedding_measurableEmbedding (c : Chart) :
    MeasurableEmbedding (splitEmbedding c) :=
  splitCoordinates.measurableEmbedding.comp
    (MeasurableEmbedding.subtype_coe c.isOpen_domain.measurableSet)

def splitMeasure (μ : Measure X) (c : Chart) : Measure (Transverse × Leaf) :=
  (μ.comap (c.domain.restrict (quotientCoordinates c.base))).map (splitEmbedding c)

theorem splitMeasure_eq (μ : Measure X) (c : Chart) :
    splitMeasure μ c = coordinateMeasure (coordinateMeasureOf μ c) := by
  unfold splitMeasure coordinateMeasure coordinateMeasureOf localCoordinateMeasure splitEmbedding
  rw [Measure.map_map splitCoordinates.measurable measurable_subtype_coe]

instance splitMeasure_finite (μ : Measure X) [IsFiniteMeasure μ] (c : Chart) :
    IsFiniteMeasure (splitMeasure μ c) := by
  rw [splitMeasure_eq]
  infer_instance

def branchMeasure (μ : Measure X) (c d : Chart) (γ : Gamma) :
    Measure (GroupRightDomain (overlapMatrix c d γ) × Leaf) :=
  ((μ.comap (c.domain.restrict (quotientCoordinates c.base))).comap
    (branchSource c d γ)).map Subtype.val

instance branchMeasure_finite (μ : Measure X) [IsFiniteMeasure μ] (c d : Chart) (γ : Gamma) :
    IsFiniteMeasure (branchMeasure μ c d γ) := by
  let e := c.domain.restrict (quotientCoordinates c.base) ∘ branchSource c d γ
  have he : MeasurableEmbedding e := c.embedding.measurableEmbedding.comp
    (branchSource_embedding c d γ)
  have hf : IsFiniteMeasure (μ.comap e) := by
    constructor
    rw [he.comap_apply]
    exact (measure_mono (subset_univ _)).trans_lt (measure_lt_top μ univ)
  have hcomp : (μ.comap (c.domain.restrict (quotientCoordinates c.base))).comap
      (branchSource c d γ) = μ.comap e :=
    Measure.comap_comap (fun _ hs => (branchSource_embedding c d γ).measurableSet_image' hs)
      c.embedding.injective (fun _ hs => c.embedding.measurableEmbedding.measurableSet_image' hs) μ
  unfold branchMeasure
  rw [hcomp]
  infer_instance

def sourceSet (c d : Chart) (γ : Gamma) : Set (Transverse × Leaf) :=
  range (splitEmbedding c ∘ branchSource c d γ)

def targetSet (c d : Chart) (γ : Gamma) : Set (Transverse × Leaf) :=
  range (splitEmbedding d ∘ branchTarget c d γ)

theorem measurableSet_sourceSet (c d : Chart) (γ : Gamma) :
    MeasurableSet (sourceSet c d γ) :=
  ((splitEmbedding_measurableEmbedding c).comp (branchSource_embedding c d γ)).measurableSet_range

theorem measurableSet_targetSet (c d : Chart) (γ : Gamma) :
    MeasurableSet (targetSet c d γ) :=
  ((splitEmbedding_measurableEmbedding d).comp (branchTarget_embedding c d γ)).measurableSet_range

/-- The source-coordinate image is the restriction of the actual chart measure. -/
theorem map_branch_source (μ : Measure X) (c d : Chart) (γ : Gamma) :
    (branchMeasure μ c d γ).map (Prod.map (@groupTransverseBase (overlapMatrix c d γ)) id) =
      (splitMeasure μ c).restrict (sourceSet c d γ) := by
  unfold branchMeasure
  rw [Measure.map_map ((groupTransverseBase_embedding _).measurable.prodMap measurable_id)
    measurable_subtype_coe]
  have he : (Prod.map (@groupTransverseBase (overlapMatrix c d γ)) id) ∘
      (Subtype.val : overlapSet c d γ → _) = splitEmbedding c ∘ branchSource c d γ := by
    funext p
    simp only [Function.comp_apply,splitEmbedding,branchSource,sourceParams]
    exact (splitCoordinates.apply_symm_apply _).symm
  rw [he]
  exact map_comap_map_comp _ (splitEmbedding_measurableEmbedding c) (branchSource_embedding c d γ)

/-- The target-coordinate image is likewise the restriction of the original
quotient measure in the second chart. -/
theorem map_branch_target (μ : Measure X) (c d : Chart) (γ : Gamma) :
    (branchMeasure μ c d γ).map (transition (overlapMatrix c d γ)) =
      (splitMeasure μ d).restrict (targetSet c d γ) := by
  unfold branchMeasure
  rw [branch_pullbacks_eq,Measure.map_map (measurable_transition _) measurable_subtype_coe]
  have he : transition (overlapMatrix c d γ) ∘
      (Subtype.val : overlapSet c d γ → _) = splitEmbedding d ∘ branchTarget c d γ := by
    funext p
    simp only [Function.comp_apply,splitEmbedding,branchTarget,targetParams]
    exact (splitCoordinates.apply_symm_apply _).symm
  rw [he]
  exact map_comap_map_comp _ (splitEmbedding_measurableEmbedding d) (branchTarget_embedding c d γ)

/-- The normalized restrictions of the two genuine chart conditional kernels
coincide after the explicit arithmetic leaf translation, almost everywhere on
the actual branch measure. This is derived, not supplied as projective data. -/
theorem actual_condKernel_overlap (μ : Measure X) [IsFiniteMeasure μ]
    (c d : Chart) (γ : Gamma) :
    let g := overlapMatrix c d γ
    let ρ := branchMeasure μ c d γ
    ∀ᵐ b ∂ρ.fst,
      ((fiberCondition (splitMeasure μ c).condKernel (measurableSet_sourceSet c d γ))
          (groupTransverseBase b)).map (fun u => u + groupRightLeafShift g b) =
        (fiberCondition (splitMeasure μ d).condKernel (measurableSet_targetSet c d γ))
          (groupRightTransverse g b) := by
  dsimp only
  let g := overlapMatrix c d γ
  let ρ := branchMeasure μ c d γ
  have hs := condKernel_fiberRestriction (splitMeasure μ c) (measurableSet_sourceSet c d γ)
  have hsfst : ((splitMeasure μ c).restrict (sourceSet c d γ)).fst =
      ρ.fst.map (@groupTransverseBase g) := by
    rw [← map_branch_source]
    exact fst_map_base ρ (groupTransverseBase_embedding g).measurable
  rw [hsfst] at hs
  have hs' := ae_of_ae_map (groupTransverseBase_embedding g).measurable.aemeasurable hs
  have ht := condKernel_fiberRestriction (splitMeasure μ d) (measurableSet_targetSet c d γ)
  have htfst : ((splitMeasure μ d).restrict (targetSet c d γ)).fst =
      ρ.fst.map (groupRightTransverse g) := by
    rw [← map_branch_target]
    change (ρ.map (transition g)).fst = ρ.fst.map (groupRightTransverse g)
    simp only [Measure.fst, Measure.map_map measurable_fst (measurable_transition g),
      Measure.map_map (groupRightTransverse_embedding g).measurable measurable_fst]
    rfl
  rw [htfst] at ht
  have ht' := ae_of_ae_map (groupRightTransverse_embedding g).measurable.aemeasurable ht
  have hsource := condKernel_sourceEmbedding g ρ
  have htarget := condKernel_transition g ρ
  rw [condKernel_congr (map_branch_source μ c d γ)] at hsource
  rw [condKernel_congr (map_branch_target μ c d γ)] at htarget
  filter_upwards [hs',ht',hsource,htarget] with b hs ht hsource htarget
  change _ = (fiberCondition (splitMeasure μ d).condKernel
    (measurableSet_targetSet c d γ) (groupRightTransverse g b))
  change (fiberCondition (splitMeasure μ c).condKernel
    (measurableSet_sourceSet c d γ) (groupTransverseBase b)).map _ = _
  change ((splitMeasure μ c).restrict (sourceSet c d γ)).condKernel _ =
    fiberCondition (splitMeasure μ c).condKernel (measurableSet_sourceSet c d γ) _ at hs
  change ((splitMeasure μ d).restrict (targetSet c d γ)).condKernel _ =
    fiberCondition (splitMeasure μ d).condKernel (measurableSet_targetSet c d γ) _ at ht
  rw [← hs,← ht,hsource,htarget]

end VV.BBEKActualKernelOverlap


