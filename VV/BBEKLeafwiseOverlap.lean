import VV.BBEKGaussTransition
import VV.BBEKKernelEmbedding

/-! Canonical conditional-measure compatibility for the actual Gauss branches
of quotient-chart overlaps. The transverse embedding and the leaf translation
are constructed from the real/2-adic matrices, not supplied as hypotheses. -/
noncomputable section
open Set Matrix MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixGroups ENNReal ProbabilityTheory
namespace VV.BBEKLeafwiseOverlap
open BBEKDynamics BBEKGaussChart BBEKGaussTransition BBEKLeafwiseKernel
  BBEKLeafwiseChart BBEKQuotient
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

instance real_rightDomain_borel (M : SL(2,ℝ)) : BorelSpace (rightDomain M) :=
  Subtype.borelSpace (rightDomain M)
instance padic_rightDomain_borel (M : SL(2,Q2)) : BorelSpace (rightDomain M) :=
  Subtype.borelSpace (rightDomain M)

theorem groupTransverseBase_embedding (g : G) :
    MeasurableEmbedding (@groupTransverseBase g) :=
  (isOpen_rightDomain g.1).isOpenEmbedding_subtypeVal.measurableEmbedding.prodMap
    (isOpen_rightDomain g.2).isOpenEmbedding_subtypeVal.measurableEmbedding

theorem groupRightTransverse_embedding (g : G) :
    MeasurableEmbedding (groupRightTransverse g) := by
  have hr : IsOpenEmbedding (rightTransverse g.1) :=
    ((isOpen_rightDomain g.1⁻¹).isOpenEmbedding_subtypeVal).comp
      (rightTransverseHomeomorph g.1).isOpenEmbedding
  have hp : IsOpenEmbedding (rightTransverse g.2) :=
    ((isOpen_rightDomain g.2⁻¹).isOpenEmbedding_subtypeVal).comp
      (rightTransverseHomeomorph g.2).isOpenEmbedding
  exact hr.measurableEmbedding.prodMap hp.measurableEmbedding

theorem continuous_groupRightLeafShift (g : G) : Continuous (groupRightLeafShift g) :=
  ((continuous_rightLeafShift g.1).comp continuous_fst).prodMk
    ((continuous_rightLeafShift g.2).comp continuous_snd)

def transition (g : G) (p : GroupRightDomain g × Leaf) : Transverse × Leaf :=
  (groupRightTransverse g p.1,p.2 + groupRightLeafShift g p.1)

theorem measurable_transition (g : G) : Measurable (transition g) :=
  ((groupRightTransverse_embedding g).measurable.comp measurable_fst).prodMk
    (measurable_snd.add ((continuous_groupRightLeafShift g).measurable.comp measurable_fst))

/-- Actual canonical-kernel covariance on one arithmetic overlap branch. -/
theorem condKernel_transition (g : G) (ρ : Measure (GroupRightDomain g × Leaf))
    [IsFiniteMeasure ρ] :
    ∀ᵐ b ∂ρ.fst, (ρ.map (transition g)).condKernel (groupRightTransverse g b) =
      (ρ.condKernel b).map (fun u => u + groupRightLeafShift g b) :=
  condKernel_map_skew_embedding ρ (groupRightTransverse_embedding g)
    (fun p => p.2 + groupRightLeafShift g p.1)
    (measurable_snd.add ((continuous_groupRightLeafShift g).measurable.comp measurable_fst))

theorem condKernel_sourceEmbedding (g : G) (ρ : Measure (GroupRightDomain g × Leaf))
    [IsFiniteMeasure ρ] :
    ∀ᵐ b ∂ρ.fst,
      (ρ.map (Prod.map (@groupTransverseBase g) id)).condKernel (groupTransverseBase b) =
        ρ.condKernel b :=
  condKernel_map_embedding ρ (groupTransverseBase_embedding g)

/-- Both coordinate descriptions push to precisely the same actual quotient measure. -/
theorem quotient_map_transition (g h : G) (γ : Gamma)
    (ρ : Measure (GroupRightDomain (g*(γ:G)*h⁻¹) × Leaf)) :
    (ρ.map (transition (g*(γ:G)*h⁻¹))).map
        (fun p => plaquePoint (mk h) p.1 p.2) =
      ρ.map (fun p => plaquePoint (mk g) (groupTransverseBase p.1) p.2) := by
  have hpoint : (fun p : Transverse × Leaf => plaquePoint (mk h) p.1 p.2) =
      quotientCoordinates h ∘ splitCoordinates.symm := rfl
  rw [hpoint,Measure.map_map ((continuous_quotientCoordinates h).measurable.comp
    splitCoordinates.symm.measurable) (measurable_transition _)]
  congr 1
  funext p
  exact quotient_transition g h γ p.1 p.2

end VV.BBEKLeafwiseOverlap
