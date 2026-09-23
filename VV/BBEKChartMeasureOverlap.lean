import VV.BBEKLeafwiseAtlas

/-! Actual quotient-measure pullbacks agree across every arithmetic Gauss
overlap branch. The measure identity is proved from the two injective charts. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKChartMeasureOverlap
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKGaussTransition
  BBEKLeafwiseKernel BBEKLeafwiseChart BBEKLeafwiseOverlap BBEKLeafwiseAtlas

theorem embedding_of_comp {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] {f : A → B} {g : B → C}
    (hg : MeasurableEmbedding g) (hgf : MeasurableEmbedding (g ∘ f)) :
    MeasurableEmbedding f where
  injective := hgf.injective.of_comp
  measurable := hg.measurable_comp_iff.mp hgf.measurable
  measurableSet_image' := by
    intro s hs
    apply hg.measurableSet_image.mp
    simpa only [← image_comp] using hgf.measurableSet_image' hs

def sourceParams (g : G) (p : GroupRightDomain g × Leaf) : GroupParams :=
  splitCoordinates.symm (groupTransverseBase p.1,p.2)
def targetParams (g : G) (p : GroupRightDomain g × Leaf) : GroupParams :=
  splitCoordinates.symm (transition g p)

theorem sourceParams_embedding (g : G) : MeasurableEmbedding (sourceParams g) :=
  splitCoordinates.symm.measurableEmbedding.comp
    ((groupTransverseBase_embedding g).prodMap MeasurableEmbedding.id)
theorem targetParams_measurable (g : G) : Measurable (targetParams g) :=
  splitCoordinates.symm.measurable.comp (measurable_transition g)

def overlapMatrix (c d : Chart) (γ : Gamma) : G := c.base*(γ:G)*d.base⁻¹
def overlapSet (c d : Chart) (γ : Gamma) : Set (GroupRightDomain (overlapMatrix c d γ) × Leaf) :=
  (sourceParams (overlapMatrix c d γ) ⁻¹' c.domain) ∩
    (targetParams (overlapMatrix c d γ) ⁻¹' d.domain)

theorem measurableSet_overlap (c d : Chart) (γ : Gamma) : MeasurableSet (overlapSet c d γ) :=
  ((sourceParams_embedding _).measurable c.isOpen_domain.measurableSet).inter
    (targetParams_measurable _ d.isOpen_domain.measurableSet)

def branchSource (c d : Chart) (γ : Gamma) (p : overlapSet c d γ) : c.domain :=
  ⟨sourceParams (overlapMatrix c d γ) p.val,p.property.1⟩
def branchTarget (c d : Chart) (γ : Gamma) (p : overlapSet c d γ) : d.domain :=
  ⟨targetParams (overlapMatrix c d γ) p.val,p.property.2⟩

theorem branchSource_embedding (c d : Chart) (γ : Gamma) :
    MeasurableEmbedding (branchSource c d γ) :=
  embedding_of_comp (MeasurableEmbedding.subtype_coe c.isOpen_domain.measurableSet)
    ((sourceParams_embedding _).comp (MeasurableEmbedding.subtype_coe (measurableSet_overlap c d γ)))

theorem branch_quotient_eq (c d : Chart) (γ : Gamma) :
    c.domain.restrict (quotientCoordinates c.base) ∘ branchSource c d γ =
      d.domain.restrict (quotientCoordinates d.base) ∘ branchTarget c d γ := by
  funext p
  exact (quotient_transition c.base d.base γ p.val.1 p.val.2).symm

theorem branchTarget_embedding (c d : Chart) (γ : Gamma) :
    MeasurableEmbedding (branchTarget c d γ) := by
  apply embedding_of_comp d.embedding.measurableEmbedding
  rw [← branch_quotient_eq]
  exact c.embedding.measurableEmbedding.comp (branchSource_embedding c d γ)

/-- On each actual branch, the two genuine chart pullbacks coincide before any
conditional kernels are taken. -/
theorem branch_pullbacks_eq (μ : Measure X) (c d : Chart) (γ : Gamma) :
    (μ.comap (c.domain.restrict (quotientCoordinates c.base))).comap (branchSource c d γ) =
      (μ.comap (d.domain.restrict (quotientCoordinates d.base))).comap (branchTarget c d γ) := by
  rw [Measure.comap_comap (fun _ hs => (branchSource_embedding c d γ).measurableSet_image' hs)
      c.embedding.injective (fun _ hs => c.embedding.measurableEmbedding.measurableSet_image' hs),
    Measure.comap_comap (fun _ hs => (branchTarget_embedding c d γ).measurableSet_image' hs)
      d.embedding.injective (fun _ hs => d.embedding.measurableEmbedding.measurableSet_image' hs),
    branch_quotient_eq]

/-- Transporting the actual source pullback through the branch gives exactly
the actual target pullback restricted to that branch image. -/
theorem branch_measure_transport (μ : Measure X) (c d : Chart) (γ : Gamma) :
    ((μ.comap (c.domain.restrict (quotientCoordinates c.base))).comap
        (branchSource c d γ)).map (branchTarget c d γ) =
      (μ.comap (d.domain.restrict (quotientCoordinates d.base))).restrict
        (range (branchTarget c d γ)) := by
  rw [branch_pullbacks_eq, (branchTarget_embedding c d γ).map_comap]

end VV.BBEKChartMeasureOverlap
