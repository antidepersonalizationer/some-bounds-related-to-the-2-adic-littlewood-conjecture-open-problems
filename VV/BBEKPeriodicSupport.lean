import VV.BBEKPeriodicEntropy
import VV.BBEKHomogeneousErgodic

/-! A closed diagonal orbit carrying an invariant Radon probability that
is concentrated on a compact ambient set is itself compact. Thus the compact
support available in BBEK suffices for the genuine zero-entropy orbit branch. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Topology
namespace VV.BBEKPeriodicOrbit
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKHomogeneousErgodic
open ErgodicTheory.Entropy
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

theorem closed_A_orbit_compact_of_compact_full_mass
    (q : X) (hq : IsClosed (MulAction.orbit A q))
    (μ : Measure (MulAction.orbit A q)) [IsProbabilityMeasure μ] [μ.InnerRegular]
    [SMulInvariantMeasure A (MulAction.orbit A q) μ]
    {C : Set X} (hC : IsCompact C)
    (hfull : μ (((↑) : MulAction.orbit A q → X) ⁻¹' C) = 1) :
    IsCompact (MulAction.orbit A q) := by
  letI : IsOpenPosMeasure μ := isOpenPosMeasure_of_pretransitive (H:=A) μ
  have heq : ((↑) : MulAction.orbit A q → X) ⁻¹' C = univ :=
    (hC.isClosed.preimage continuous_subtype_val).measure_eq_one_iff_eq_univ.mp hfull
  have hrange : IsClosed (range ((↑) : MulAction.orbit A q → X)) := by simpa using hq
  have hc : IsCompact (((↑) : MulAction.orbit A q → X) ⁻¹' C) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage hrange hC
  rw [heq] at hc
  have hi := hc.image (continuous_subtype_val : Continuous ((↑) : MulAction.orbit A q → X))
  simpa using hi

theorem closed_A_orbit_ksEntropy_zero_of_compact_full_mass
    (q : X) (hq : IsClosed (MulAction.orbit A q))
    (μ : Measure (MulAction.orbit A q)) [IsProbabilityMeasure μ] [μ.InnerRegular]
    [SMulInvariantMeasure A (MulAction.orbit A q) μ]
    {C : Set X} (hC : IsCompact C)
    (hfull : μ (((↑) : MulAction.orbit A q → X) ⁻¹' C) = 1)
    (t : ℝ) (n : ℤ) :
    ksEntropy (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ) = 0 := by
  exact compact_A_orbit_ksEntropy_zero q
    (closed_A_orbit_compact_of_compact_full_mass q hq μ hC hfull) t n μ
    (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ)

end VV.BBEKPeriodicOrbit

