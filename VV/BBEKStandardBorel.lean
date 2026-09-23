import VV.BBEKTopology
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Completion

/-! The actual quotient is a standard Borel space.  We embed its compatible
metric in its completion.  Sigma compactness makes the image Borel, so this
argument does not presume that an arbitrary compatible metric is complete. -/

noncomputable section
open MeasureTheory Set TopologicalSpace UniformSpace

namespace VV.BBEKStandardBorel

theorem standardBorel_of_measurableEquiv {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [StandardBorelSpace F]
    (e : E ≃ᵐ F) : StandardBorelSpace E := by
  letI := upgradeStandardBorel F
  letI : TopologicalSpace E := TopologicalSpace.induced e inferInstance
  letI : PolishSpace E := e.toEquiv.polishSpace_induced
  letI : BorelSpace E := e.measurableEmbedding.borelSpace ⟨rfl⟩
  infer_instance

theorem standardBorel_of_metrizable_sigmaCompact {E : Type*}
    [TopologicalSpace E] [MetrizableSpace E] [SecondCountableTopology E]
    [SigmaCompactSpace E] [MeasurableSpace E] [BorelSpace E] :
    StandardBorelSpace E := by
  letI : MetricSpace E := metrizableSpaceMetric E
  letI : MeasurableSpace (Completion E) := borel (Completion E)
  letI : BorelSpace (Completion E) := ⟨rfl⟩
  have he : Topology.IsEmbedding ((↑) : E → Completion E) :=
    Completion.coe_isometry.isEmbedding
  have hr : MeasurableSet (Set.range ((↑) : E → Completion E)) := by
    obtain ⟨K,hK,hcover⟩ := isSigmaCompact_range he.continuous
    rw [← hcover]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  letI : StandardBorelSpace (Set.range ((↑) : E → Completion E)) := hr.standardBorel
  exact standardBorel_of_measurableEquiv he.toHomeomorph.toMeasurableEquiv

open BBEKDynamics BBEKQuotient BBEKTopology BBEKDiscrete

instance quotient_standardBorel : StandardBorelSpace X :=
  standardBorel_of_metrizable_sigmaCompact

end VV.BBEKStandardBorel
