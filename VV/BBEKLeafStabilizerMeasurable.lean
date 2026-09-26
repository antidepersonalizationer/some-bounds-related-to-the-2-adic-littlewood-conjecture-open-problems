import VV.BBEKLeafMeasureTests
import VV.BBEKCompactZeroHit

/-! Hit-open measurability for translation stabilizers of actual measurable
Radon measure families. The compact-zero projection theorem is applied to
literal countable determining integral tests, not to an assumed Fell field. -/
noncomputable section
open Set MeasureTheory Filter Metric Function TopologicalSpace
open scoped Topology ENNReal
namespace VV.BBEKLeafStabilizerMeasurable
open BBEKLeafMeasureTests BBEKLeafwiseStabilizer
variable {U Z : Type*} [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [ProperSpace U] [SecondCountableTopology U] [MeasurableSpace Z]

/-- The translation discrepancy for the fixed, measure-independent tests. -/
def testDifference (η : Z → Measure U) (j : ℕ) (z : Z) (u : U) : ℝ :=
  (∫ x, testFunction (U := U) j (u+x) ∂η z) - ∫ x, testFunction (U := U) j x ∂η z

theorem measurable_testDifference (η : Z → Measure U) (hη : Measurable η)
    (j : ℕ) (u : U) : Measurable (fun z => testDifference η j z u) := by
  exact (measurable_integral_family η hη
    ((testFunction j).comp ⟨fun x => u+x,continuous_const.add continuous_id⟩)).sub
      (measurable_integral_family η hη (testFunction j))

theorem continuous_testDifference (η : Z → Measure U) (j : ℕ) (z : Z)
    [IsFiniteMeasureOnCompacts (η z)] : Continuous (testDifference η j z) :=
  (continuous_integral_translate (η z) (testFunction j) (testFunction_compact j)).sub continuous_const

/-- Vanishing of the actual countable tests is precisely stabilizer membership. -/
theorem mem_stabilizer_iff_tests (η : Z → Measure U) (z : Z) [(η z).Regular] (u : U) :
    u ∈ translationStabilizer (η z) ↔ ∀ j : ℕ, testDifference η j z u = 0 := by
  have hmap (j : ℕ) : (∫ x, testFunction (U := U) j x ∂translate u (η z)) =
      ∫ x, testFunction (U := U) j (u+x) ∂η z :=
    (Homeomorph.addLeft u).measurableEmbedding.integral_map _
  constructor
  · intro hu j
    change _ - _ = 0
    rw [← hmap j,(mem_translationStabilizer (η z) u).mp hu,sub_self]
  · intro ht
    apply (mem_translationStabilizer (η z) u).mpr
    haveI : (translate u (η z)).Regular := Measure.Regular.map (Homeomorph.addLeft u)
    apply ext_of_test_integrals
    intro j
    rw [hmap]
    exact sub_eq_zero.mp (ht j)

/-- A measurable family of Radon measures has a measurable event of its exact
translation stabilizer hitting any prescribed open set. -/
theorem measurableSet_stabilizer_hit (η : Z → Measure U) (hη : Measurable η)
    [∀ z, (η z).Regular] {O : Set U} (hO : IsOpen O) :
    MeasurableSet {z | ∃ u ∈ translationStabilizer (η z), u ∈ O} := by
  have hh := BBEKCompactZeroHit.measurableSet_exists_zero_on_open hO
    (testDifference η) (fun j u => measurable_testDifference η hη j u)
    (fun j z => continuous_testDifference η j z)
  convert hh using 1
  ext z
  constructor
  · rintro ⟨u,hu,hO⟩
    exact ⟨u,hO,(mem_stabilizer_iff_tests η z u).mp hu⟩
  · rintro ⟨u,hO,hu⟩
    exact ⟨u,(mem_stabilizer_iff_tests η z u).mpr hu,hO⟩

end VV.BBEKLeafStabilizerMeasurable
