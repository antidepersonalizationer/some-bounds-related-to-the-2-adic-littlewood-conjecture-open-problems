import VV.BBEKPeriodicSupport
import VV.Entropy.EmbeddingEntropy

/-! The periodic diagonal-orbit exclusion expressed for a measure on the
actual ambient arithmetic quotient, using a proved restriction/lift. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure Function
open scoped Topology
namespace VV.BBEKPeriodicOrbit
open BBEKDynamics BBEKQuotient BBEKDiagonal
open ErgodicTheory.Entropy
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

theorem closed_A_orbit_entropy_zero_on_quotient
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (q : X) (hq : IsClosed (MulAction.orbit A q))
    (hO : μ (MulAction.orbit A q)=1)
    {C : Set X} (hC : IsCompact C) (hfull : μ C=1) (t : ℝ) (n : ℤ) :
    ksEntropy (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ)=0 := by
  let O := MulAction.orbit A q
  let ν : Measure O := μ.comap Subtype.val
  have hf : MeasurableEmbedding ((↑) : O → X) := .subtype_coe hq.measurableSet
  letI : IsProbabilityMeasure ν := ⟨by
    change (μ.comap ((↑) : O → X)) univ=1
    rw [comap_subtype_coe_apply hq.measurableSet]
    simpa only [image_univ,Subtype.range_coe] using hO⟩
  have hmap : ν.map ((↑) : O → X) = μ := by
    rw [map_comap_subtype_coe hq.measurableSet]
    exact restrict_eq_self_of_ae_mem ((mem_ae_iff_prob_eq_one hq.measurableSet).mpr hO)
  have hνμ : MeasurePreserving ((↑) : O → X) ν μ := ⟨measurable_subtype_coe,hmap⟩
  letI : SMulInvariantMeasure A O ν := by
    constructor
    intro a s hs
    have he : Measure.map ((↑) : O → X) (ν.map (fun y : O => a • y))=μ := by
      calc
        _ = ν.map (((↑) : O → X) ∘ (fun y : O => a • y)) :=
          Measure.map_map measurable_subtype_coe (measurable_const_smul a)
        _ = ν.map ((fun y : X => a • y) ∘ ((↑) : O → X)) := rfl
        _ = (ν.map ((↑) : O → X)).map (fun y : X => a • y) :=
          (Measure.map_map (measurable_const_smul a) measurable_subtype_coe).symm
        _ = μ := by rw [hmap,(measurePreserving_smul a μ).map_eq]
    have he' := congrArg (Measure.comap ((↑) : O → X)) he
    rw [hf.comap_map] at he'
    change ν.map (fun y : O => a • y)=ν at he'
    rw [← Measure.map_apply (measurable_const_smul a) hs,he']
  letI : SigmaCompactSpace O := hq.sigmaCompactSpace
  letI : Measure.InnerRegular ν := inferInstance
  have hνfull : ν (((↑) : O → X) ⁻¹' C)=1 := by
    rw [hνμ.measure_preimage hC.measurableSet.nullMeasurableSet,hfull]
  have hzero := closed_A_orbit_ksEntropy_zero_of_compact_full_mass q hq ν hC hνfull t n
  have he := ksEntropy_eq_of_embedding
    (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) ν)
    (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ) hf hνμ rfl
  exact he.symm.trans hzero

/-- Ergodicity selects one of a countable family of closed diagonal orbits.
Thus a compactly supported positive-entropy measure cannot be carried even
by a countable union of such periodic orbits. -/
theorem countable_closed_A_orbits_entropy_zero_on_quotient
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul A X μ]
    {ι : Type*} [Countable ι] (q : ι → X)
    (hq : ∀ i, IsClosed (MulAction.orbit A (q i)))
    (hO : μ (⋃ i, MulAction.orbit A (q i))=1)
    {C : Set X} (hC : IsCompact C) (hfull : μ C=1) (t : ℝ) (n : ℤ) :
    ksEntropy (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ)=0 := by
  obtain ⟨i,hi⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (show μ (⋃ i, MulAction.orbit A (q i)) ≠ 0 by rw [hO]; exact one_ne_zero)
  have hconst := aeconst_of_forall_smul_ae_eq A (μ:=μ) (hq i).measurableSet.nullMeasurableSet
    (fun a => Filter.EventuallyEq.of_eq (MulAction.smul_orbit a (q i)))
  have hmass : μ (MulAction.orbit A (q i))=1 := by
    rcases Filter.eventuallyConst_set'.mp hconst with he | he
    · have hz : μ (MulAction.orbit A (q i))=0 := by simpa using measure_congr he
      exact (hi.ne' hz).elim
    · simpa using measure_congr he
  exact closed_A_orbit_entropy_zero_on_quotient μ (q i) (hq i) hmass hC hfull t n

end VV.BBEKPeriodicOrbit

