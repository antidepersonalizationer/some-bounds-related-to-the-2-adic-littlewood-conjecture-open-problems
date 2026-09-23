import VV.BBEKNormalizerOrbit
import VV.BBEKInvariantSupport

/-! The compact-support periodic-orbit exclusion for every subgroup of the
actual diagonal normalizer, not just the normalizer or torus itself. -/
noncomputable section
open Set MulAction MeasureTheory MeasureTheory.Measure
open scoped Topology
namespace VV.BBEKNormalizerExclusion
open BBEKDynamics BBEKDiagonal BBEKQuotient BBEKNormalizerOrbit BBEKInvariantSupport

local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

theorem compact_N_orbit_of_compact_invariant_subset (q : X)
    {Y : Set X} (hY : IsCompact Y) (hne : Y.Nonempty) (hsub : Y ⊆ orbit N q)
    (hinv : ∀ a : A, MapsTo (fun y : X => a • y) Y Y) : IsCompact (orbit N q) := by
  obtain ⟨x,hx⟩ := hne
  have hox : orbit N x = orbit N q := orbit_eq_iff.mpr (hsub hx)
  have he : orbit N q = ⋃ b : Bool × Bool, (fun y : X => weylPair b • y) '' Y := by
    ext z
    constructor
    · intro hz
      rw [← hox,orbit_N_eq] at hz
      obtain ⟨b,a,ha⟩ := mem_iUnion.mp hz
      have hw : weylPair b ∈ A.normalizer := by
        rw [← N_eq_normalizer]
        exact weylPair_mem b
      have hc : (weylPair b)⁻¹ * a.val * weylPair b ∈ A :=
        (Subgroup.mem_normalizer_iff''.mp hw a.val).mp a.property
      let c : A := ⟨(weylPair b)⁻¹ * a.val * weylPair b,hc⟩
      refine mem_iUnion.mpr ⟨b,c • x,hinv c hx,?_⟩
      change weylPair b • (((weylPair b)⁻¹*a.val*weylPair b) • x)=z
      rw [← MulAction.mul_smul]
      simpa only [mul_assoc,mul_inv_cancel_left,MulAction.mul_smul] using ha
    · intro hz
      obtain ⟨b,y,hy,rfl⟩ := mem_iUnion.mp hz
      exact mapsTo_smul_orbit (⟨weylPair b,weylPair_mem b⟩ : N) q (hsub hy)
  rw [he]
  exact isCompact_iUnion (fun b => hY.image (continuous_const_smul (weylPair b)))

/-- Compact support plus invariance upgrades a closed full-mass subset of a
normalizer orbit to compactness of the entire normalizer orbit. -/
theorem compact_N_orbit_of_closed_full_subset
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    (q : X) {S : Set X} (hS : IsClosed S) (hSN : S ⊆ orbit N q) (hμS : μ S=1)
    {C : Set X} (hC : IsCompact C) (hμC : μ C=1) : IsCompact (orbit N q) := by
  exact compact_N_orbit_of_compact_invariant_subset q
    (positiveSupport_isCompact μ hC hμC) (positiveSupport_nonempty μ)
    ((positiveSupport_subset_of_closed_full μ hS hμS).trans hSN)
    (smul_positiveSupport μ)

/-- Actual closed orbits of *any* subgroup of N are excluded by positive
entropy. No A-containment in that subgroup, closedness of N's orbit, or
compactness of the periodic orbit is assumed. -/
theorem closed_subgroup_orbit_entropy_zero
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul A X μ]
    (L : Subgroup G) (hLN : L ≤ N) (q : X) (hq : IsClosed (orbit L q))
    (hO : μ (orbit L q)=1) {C : Set X} (hC : IsCompact C) (hfull : μ C=1)
    (t : ℝ) (n : ℤ) :
    ErgodicTheory.Entropy.ksEntropy
      (measurePreserving_smul (⟨psi t n,psi_mem_A t n⟩ : A) μ)=0 := by
  have hsub : orbit L q ⊆ orbit N q := by
    rintro y ⟨l,hl⟩
    exact ⟨⟨l.val,hLN l.property⟩,hl⟩
  have hcompact := compact_N_orbit_of_closed_full_subset μ q hq hsub hO hC hfull
  have hmass : μ (orbit N q)=1 := le_antisymm prob_le_one
    (hO ▸ measure_mono hsub)
  exact closed_N_orbit_entropy_zero_on_quotient μ q hcompact.isClosed hmass hC hfull t n

end VV.BBEKNormalizerExclusion

