import VV.BBEKLeafwiseKernel
import VV.BBEKLocalChart

/-! Genuine local disintegrations of a quotient measure in lower-unipotent Gauss plaques. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory
namespace VV.BBEKLeafwiseChart
open BBEKDynamics BBEKQuotient BBEKTopology BBEKGaussChart BBEKLocalChart BBEKLeafwiseKernel
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def quotientCoordinates (g : G) (p : GroupParams) : X := mk (groupMatrixOf p * g)

theorem continuous_quotientCoordinates (g : G) : Continuous (quotientCoordinates g) :=
  continuous_mk.comp (continuous_groupMatrixOf.mul continuous_const)

theorem groupMatrixOf_isOpenEmbedding : IsOpenEmbedding groupMatrixOf :=
  isOpen_productDomain.isOpenEmbedding_subtypeVal.comp groupChart.symm.isOpenEmbedding

theorem quotientCoordinates_isOpenMap (g : G) : IsOpenMap (quotientCoordinates g) :=
  isOpenMap_mk.comp ((Homeomorph.mulRight g).isOpenMap.comp groupMatrixOf_isOpenEmbedding.isOpenMap)

/-- Every Gauss point has a real open injective quotient chart; no chart hypothesis is assumed. -/
theorem exists_open_quotientCoordinates (g : G) (p : GroupParams) :
    ∃ V : Set GroupParams, IsOpen V ∧ p ∈ V ∧ IsOpenEmbedding (V.restrict (quotientCoordinates g)) := by
  obtain ⟨W,hW,hp,hW_inj⟩ := exists_open_injOn_mk (groupMatrixOf p * g)
  let V : Set GroupParams := (fun z => groupMatrixOf z * g) ⁻¹' W
  have hV : IsOpen V := hW.preimage (continuous_groupMatrixOf.mul continuous_const)
  refine ⟨V,hV,hp,IsOpenEmbedding.of_continuous_injective_isOpenMap
    ((continuous_quotientCoordinates g).comp continuous_subtype_val) ?_
      ((quotientCoordinates_isOpenMap g).restrict hV)⟩
  intro a b hab
  apply Subtype.ext
  apply groupMatrixOf_injective
  exact mul_right_cancel (hW_inj a.property b.property hab)

/-- Pull a genuine quotient measure back to an injective open Gauss box, then extend by zero
to the full coordinate space. -/
def localCoordinateMeasure (μ : Measure X) (g : G) (V : Set GroupParams) : Measure GroupParams :=
  (μ.comap (V.restrict (quotientCoordinates g))).map Subtype.val

theorem localCoordinateMeasure_finite (μ : Measure X) [IsFiniteMeasure μ]
    (g : G) {V : Set GroupParams} (hV : IsOpen V)
    (he : IsOpenEmbedding (V.restrict (quotientCoordinates g))) :
    IsFiniteMeasure (localCoordinateMeasure μ g V) := by
  have hf := he.measurableEmbedding
  haveI : IsFiniteMeasure (μ.comap (V.restrict (quotientCoordinates g))) := by
    refine ⟨lt_of_le_of_lt ?_ (measure_lt_top μ univ)⟩
    rw [hf.comap_apply]
    exact measure_mono (subset_univ _)
  unfold localCoordinateMeasure
  infer_instance

/-- This identifies the constructed coordinate measure with the original quotient measure
on the chart image, rather than merely assigning a kernel to unrelated parameters. -/
theorem map_localCoordinateMeasure (μ : Measure X) (g : G) {V : Set GroupParams}
    (hV : IsOpen V) (he : IsOpenEmbedding (V.restrict (quotientCoordinates g))) :
    (localCoordinateMeasure μ g V).map (quotientCoordinates g) =
      μ.restrict ((quotientCoordinates g) '' V) := by
  unfold localCoordinateMeasure
  rw [Measure.map_map (continuous_quotientCoordinates g).measurable measurable_subtype_coe]
  change (μ.comap (V.restrict (quotientCoordinates g))).map (V.restrict (quotientCoordinates g)) = _
  rw [he.measurableEmbedding.map_comap, Set.range_restrict]

/-- Exact reconstruction of the original local quotient measure by transverse integration
of the actual lower-unipotent conditional kernel. -/
theorem disintegrate_local_quotient (μ : Measure X) [IsFiniteMeasure μ]
    (g : G) {V : Set GroupParams} (hV : IsOpen V)
    (he : IsOpenEmbedding (V.restrict (quotientCoordinates g))) :
    letI := localCoordinateMeasure_finite μ g hV he
    ((coordinateMeasure (localCoordinateMeasure μ g V)).fst ⊗ₘ
        leafKernel (localCoordinateMeasure μ g V)).map
      (fun p : Transverse × Leaf => plaquePoint (mk g) p.1 p.2) =
        μ.restrict ((quotientCoordinates g) '' V) := by
  letI := localCoordinateMeasure_finite μ g hV he
  rw [leafKernel, Measure.disintegrate]
  unfold coordinateMeasure
  have hpoint : (fun p : Transverse × Leaf => plaquePoint (mk g) p.1 p.2) =
      quotientCoordinates g ∘ splitCoordinates.symm := rfl
  rw [hpoint, Measure.map_map ((continuous_quotientCoordinates g).measurable.comp
    splitCoordinates.symm.measurable) splitCoordinates.measurable]
  have hid : (quotientCoordinates g ∘ splitCoordinates.symm) ∘ splitCoordinates =
      quotientCoordinates g := by funext p; simp
  rw [hid]
  exact map_localCoordinateMeasure μ g hV he

end VV.BBEKLeafwiseChart
