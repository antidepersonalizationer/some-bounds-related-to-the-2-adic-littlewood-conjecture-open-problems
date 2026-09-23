import VV.BBEKDiscrete
import Mathlib.Topology.Metrizable.Urysohn

/-! Countability and Borel structures for the concrete homogeneous space. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace VV.BBEKTopology
open BBEKDynamics BBEKQuotient BBEKDiscrete
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

instance sl2_secondCountable {F : Type*} [CommRing F] [TopologicalSpace F]
    [SecondCountableTopology F] : SecondCountableTopology SL(2,F) := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  exact TopologicalSpace.Subtype.secondCountableTopology {M : Matrix (Fin 2) (Fin 2) F | M.det = 1}

instance group_secondCountable : SecondCountableTopology G := inferInstance

instance quotient_secondCountable : SecondCountableTopology X :=
  inferInstanceAs (SecondCountableTopology (G ⧸ Gamma))

instance group_measurableSpace : MeasurableSpace G := borel G
instance group_borelSpace : BorelSpace G := ⟨rfl⟩
instance quotient_measurableSpace : MeasurableSpace X := borel X
instance quotient_borelSpace : BorelSpace X := ⟨rfl⟩

instance quotient_metrizableSpace : TopologicalSpace.MetrizableSpace X := inferInstance

end VV.BBEKTopology
