import VV.BBEKOneRootGeometry

/-! Actual arithmetic-overlap disintegrations for each one-dimensional root.
The same original quotient measure supplies both chart kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKOneRootOverlap
open BBEKDynamics BBEKQuotient BBEKGaussChart BBEKGaussTransition
  BBEKLeafwiseKernel BBEKLeafwiseChart BBEKLeafwiseAtlas BBEKLeafwiseOverlap
  BBEKChartMeasureOverlap BBEKLocalRootFamily BBEKActualKernelOverlap
  BBEKRootLeafKernel BBEKOneRootGeometry
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem map_comap_map_comp {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) {f : A → B} {g : C → A}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g) :
    (μ.comap g).map (f ∘ g) = (μ.map f).restrict (range (f ∘ g)) := by
  have hpre : f ⁻¹' range (f ∘ g)=range g := by
    ext a
    constructor
    · rintro ⟨z,hz⟩; exact ⟨z,hf.injective hz⟩
    · rintro ⟨z,rfl⟩; exact ⟨z,rfl⟩
  rw [← Measure.map_map hf.measurable hg.measurable,hg.map_comap,hf.restrict_map,hpre]

section SplitMeasure
variable {B U : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]

def splitEmbeddingWith (s : GroupParams ≃ₜ B × U) (c : Chart) : c.domain → B × U :=
  s ∘ Subtype.val

theorem splitEmbeddingWith_measurableEmbedding (s : GroupParams ≃ₜ B × U) (c : Chart) :
    MeasurableEmbedding (splitEmbeddingWith s c) :=
  s.measurableEmbedding.comp (MeasurableEmbedding.subtype_coe c.isOpen_domain.measurableSet)

def splitMeasureWith (s : GroupParams ≃ₜ B × U) (μ : Measure X) (c : Chart) : Measure (B × U) :=
  (μ.comap (c.domain.restrict (quotientCoordinates c.base))).map (splitEmbeddingWith s c)

theorem splitMeasureWith_eq (s : GroupParams ≃ₜ B × U) (μ : Measure X) (c : Chart) :
    splitMeasureWith s μ c=(coordinateMeasureOf μ c).map s := by
  unfold splitMeasureWith coordinateMeasureOf localCoordinateMeasure splitEmbeddingWith
  rw [Measure.map_map s.measurable measurable_subtype_coe]

instance splitMeasureWith_finite (s : GroupParams ≃ₜ B × U) (μ : Measure X)
    [IsFiniteMeasure μ] (c : Chart) : IsFiniteMeasure (splitMeasureWith s μ c) := by
  rw [splitMeasureWith_eq]
  infer_instance

def sourceSetWith (s : GroupParams ≃ₜ B × U) (c d : Chart) (γ : Gamma) : Set (B × U) :=
  range (splitEmbeddingWith s c ∘ branchSource c d γ)

def targetSetWith (s : GroupParams ≃ₜ B × U) (c d : Chart) (γ : Gamma) : Set (B × U) :=
  range (splitEmbeddingWith s d ∘ branchTarget c d γ)

theorem measurableSet_sourceSetWith (s : GroupParams ≃ₜ B × U) (c d : Chart) (γ : Gamma) :
    MeasurableSet (sourceSetWith s c d γ) :=
  ((splitEmbeddingWith_measurableEmbedding s c).comp
    (branchSource_embedding c d γ)).measurableSet_range

theorem measurableSet_targetSetWith (s : GroupParams ≃ₜ B × U) (c d : Chart) (γ : Gamma) :
    MeasurableSet (targetSetWith s c d γ) :=
  ((splitEmbeddingWith_measurableEmbedding s d).comp
    (branchTarget_embedding c d γ)).measurableSet_range
end SplitMeasure

section Branch
variable {B U D : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]
  [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D]

variable (s : GroupParams ≃ₜ B × U) (μ : Measure X) (c d : Chart) (γ : Gamma)
  (e : GroupRightDomain (overlapMatrix c d γ) × Leaf ≃ₜ D × U)

theorem map_branch_sourceWith {f : D → B} (hf : MeasurableEmbedding f)
    (hsource : ∀p, s (sourceParams (overlapMatrix c d γ) p)=Prod.map f id (e p)) :
    ((branchMeasure μ c d γ).map e).map (Prod.map f id)=
      (splitMeasureWith s μ c).restrict (sourceSetWith s c d γ) := by
  unfold branchMeasure
  rw [Measure.map_map (hf.measurable.prodMap measurable_id) e.measurable,
    Measure.map_map ((hf.measurable.prodMap measurable_id).comp e.measurable) measurable_subtype_coe]
  have he : ((Prod.map f id) ∘ e) ∘ (Subtype.val : overlapSet c d γ → _)=
      splitEmbeddingWith s c ∘ branchSource c d γ := by
    funext p
    exact (hsource p.val).symm
  rw [he]
  exact map_comap_map_comp _ (splitEmbeddingWith_measurableEmbedding s c)
    (branchSource_embedding c d γ)

theorem map_branch_targetWith {f : D → B} (hf : MeasurableEmbedding f)
    (a : D → U) (ha : Measurable a)
    (htarget : ∀p, s (targetParams (overlapMatrix c d γ) p)=((f (e p).1),(e p).2+a (e p).1)) :
    ((branchMeasure μ c d γ).map e).map (fun p => (f p.1,p.2+a p.1))=
      (splitMeasureWith s μ d).restrict (targetSetWith s c d γ) := by
  have hm : Measurable (fun p : D × U => (f p.1,p.2+a p.1)) :=
    (hf.measurable.comp measurable_fst).prodMk (measurable_snd.add (ha.comp measurable_fst))
  unfold branchMeasure
  rw [Measure.map_map hm e.measurable,branch_pullbacks_eq,
    Measure.map_map (hm.comp e.measurable) measurable_subtype_coe]
  have he : ((fun p : D × U => (f p.1,p.2+a p.1)) ∘ e) ∘
      (Subtype.val : overlapSet c d γ → _)=splitEmbeddingWith s d ∘ branchTarget c d γ := by
    funext p
    exact (htarget p.val).symm
  rw [he]
  exact map_comap_map_comp _ (splitEmbeddingWith_measurableEmbedding s d)
    (branchTarget_embedding c d γ)

theorem actual_condKernel_overlapWith [IsFiniteMeasure μ]
    {f h : D → B} (hf : MeasurableEmbedding f) (hh : MeasurableEmbedding h)
    (a : D → U) (ha : Measurable a)
    (hsource : ∀p, s (sourceParams (overlapMatrix c d γ) p)=Prod.map f id (e p))
    (htarget : ∀p, s (targetParams (overlapMatrix c d γ) p)=((h (e p).1),(e p).2+a (e p).1)) :
    ∀ᵐ b ∂((branchMeasure μ c d γ).map e).fst,
      ((fiberCondition (splitMeasureWith s μ c).condKernel (measurableSet_sourceSetWith s c d γ))
        (f b)).map (fun u => u+a b)=
      (fiberCondition (splitMeasureWith s μ d).condKernel (measurableSet_targetSetWith s c d γ)) (h b) := by
  let ρ := (branchMeasure μ c d γ).map e
  let T : D × U → B × U := fun p => (h p.1,p.2+a p.1)
  have hm : Measurable T :=
    (hh.measurable.comp measurable_fst).prodMk (measurable_snd.add (ha.comp measurable_fst))
  have hsmap := map_branch_sourceWith s μ c d γ e hf hsource
  have htmap := map_branch_targetWith s μ c d γ e hh a ha htarget
  have hs := condKernel_fiberRestriction (splitMeasureWith s μ c) (measurableSet_sourceSetWith s c d γ)
  have hsbase : ((splitMeasureWith s μ c).restrict (sourceSetWith s c d γ)).fst=ρ.fst.map f := by
    rw [← hsmap]
    exact fst_map_base ρ hf.measurable
  rw [hsbase] at hs
  have hs' := ae_of_ae_map hf.measurable.aemeasurable hs
  have ht := condKernel_fiberRestriction (splitMeasureWith s μ d) (measurableSet_targetSetWith s c d γ)
  have htbase : ((splitMeasureWith s μ d).restrict (targetSetWith s c d γ)).fst=ρ.fst.map h := by
    rw [← htmap]
    change (ρ.map T).fst=ρ.fst.map h
    simp only [Measure.fst,Measure.map_map measurable_fst hm,
      Measure.map_map hh.measurable measurable_fst]
    rfl
  rw [htbase] at ht
  have ht' := ae_of_ae_map hh.measurable.aemeasurable ht
  have hsource' := condKernel_map_embedding ρ hf
  have htarget' := condKernel_map_skew_embedding ρ hh (fun p => p.2+a p.1)
    (measurable_snd.add (ha.comp measurable_fst))
  rw [condKernel_congr hsmap] at hsource'
  rw [condKernel_congr htmap] at htarget'
  filter_upwards [hs',ht',hsource',htarget'] with b hs ht hsource' htarget'
  change (fiberCondition (splitMeasureWith s μ c).condKernel
      (measurableSet_sourceSetWith s c d γ) (f b)).map _=
    fiberCondition (splitMeasureWith s μ d).condKernel (measurableSet_targetSetWith s c d γ) (h b)
  change ((splitMeasureWith s μ c).restrict (sourceSetWith s c d γ)).condKernel (f b)=
    fiberCondition (splitMeasureWith s μ c).condKernel
      (measurableSet_sourceSetWith s c d γ) (f b) at hs
  change ((splitMeasureWith s μ d).restrict (targetSetWith s c d γ)).condKernel (h b)=
    fiberCondition (splitMeasureWith s μ d).condKernel
      (measurableSet_targetSetWith s c d γ) (h b) at ht
  rw [← hs,← ht,hsource',htarget']
end Branch

theorem actual_real_condKernel_overlap (μ : Measure X) [IsFiniteMeasure μ]
    (c d : Chart) (γ : Gamma) :
    let g := overlapMatrix c d γ
    ∀ᵐ b ∂((branchMeasure μ c d γ).map (realBranchSplit g)).fst,
      ((fiberCondition (splitMeasureWith realSplit μ c).condKernel
        (measurableSet_sourceSetWith realSplit c d γ)) (realBaseSource g b)).map
          (fun u => u+realBranchShift g b)=
      (fiberCondition (splitMeasureWith realSplit μ d).condKernel
        (measurableSet_targetSetWith realSplit c d γ)) (realBaseTarget g b) :=
  actual_condKernel_overlapWith realSplit μ c d γ (realBranchSplit _)
    (realBaseSource_embedding _) (realBaseTarget_embedding _)
    (realBranchShift _) (measurable_realBranchShift _)
    (real_source_identity _) (real_target_identity _)

theorem actual_padic_condKernel_overlap (μ : Measure X) [IsFiniteMeasure μ]
    (c d : Chart) (γ : Gamma) :
    let g := overlapMatrix c d γ
    ∀ᵐ b ∂((branchMeasure μ c d γ).map (padicBranchSplit g)).fst,
      ((fiberCondition (splitMeasureWith padicSplit μ c).condKernel
        (measurableSet_sourceSetWith padicSplit c d γ)) (padicBaseSource g b)).map
          (fun u => u+padicBranchShift g b)=
      (fiberCondition (splitMeasureWith padicSplit μ d).condKernel
        (measurableSet_targetSetWith padicSplit c d γ)) (padicBaseTarget g b) :=
  actual_condKernel_overlapWith padicSplit μ c d γ (padicBranchSplit _)
    (padicBaseSource_embedding _) (padicBaseTarget_embedding _)
    (padicBranchShift _) (measurable_padicBranchShift _)
    (padic_source_identity _) (padic_target_identity _)

end VV.BBEKOneRootOverlap
