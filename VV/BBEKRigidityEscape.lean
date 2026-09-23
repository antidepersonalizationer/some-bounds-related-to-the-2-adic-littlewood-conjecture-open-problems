import VV.BBEKMeasureStabilizer

/-!
# Elementary endgame for the specialized BBEK rigidity argument

Once the low-entropy argument produces both opposite root directions in either local factor, the
remaining contradiction with compact Mahler support is elementary.  This file records that exact
interface so the analytic leafwise proof has a small, concrete target.
-/

noncomputable section
open MeasureTheory

namespace VV.BBEKRigidityEscape
open BBEKDynamics BBEKQuotient BBEKDiagonal BBEKFactorEscape BBEKMeasureStabilizer

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Invariance under either complete local factor contradicts full mass on a positive Mahler
compact set. -/
theorem no_supported_of_localFactor_dichotomy
    (μ : Measure X) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (BBEKOrbit.K δ) = 1)
    (hlocal : realFactor ≤ measureStabilizer μ ∨
      padicFactor ≤ measureStabilizer μ) : False := by
  rcases hlocal with hreal | hpadic
  · exact no_subgroup_invariant_probability_supported_K_of_realFactor
      (measureStabilizer μ) μ hreal hδ hmass
  · exact no_subgroup_invariant_probability_supported_K_of_padicFactor
      (measureStabilizer μ) μ hpadic hδ hmass

/-- It is enough for the leafwise argument to produce one nonzero stabilizing element in each
opposite real root direction. -/
theorem no_supported_of_nonzero_real_opposite_roots
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (BBEKOrbit.K δ) = 1)
    {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hlo : x u 0 ∈ measureStabilizer μ)
    (hup : BBEKMautner.upperPoint v 0 ∈ measureStabilizer μ) : False :=
  no_nonzero_opposite_real_roots_supported_K μ hu hv hlo hup hδ hmass

/-- The analogous concrete endpoint in the `2`-adic factor. -/
theorem no_supported_of_nonzero_padic_opposite_roots
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (BBEKOrbit.K δ) = 1)
    {u v : Q2} (hu : u ≠ 0) (hv : v ≠ 0)
    (hlo : x 0 u ∈ measureStabilizer μ)
    (hup : BBEKMautner.upperPoint 0 v ∈ measureStabilizer μ) : False :=
  no_nonzero_opposite_padic_roots_supported_K μ hu hv hlo hup hδ hmass

/-- Disjunctive target matching the two possible active local factors in the entropy argument. -/
theorem no_supported_of_opposite_root_pair
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (BBEKOrbit.K δ) = 1)
    (hroots :
      (∃ u v : ℝ, u ≠ 0 ∧ v ≠ 0 ∧
        x u 0 ∈ measureStabilizer μ ∧
        BBEKMautner.upperPoint v 0 ∈ measureStabilizer μ) ∨
      (∃ u v : Q2, u ≠ 0 ∧ v ≠ 0 ∧
        x 0 u ∈ measureStabilizer μ ∧
        BBEKMautner.upperPoint 0 v ∈ measureStabilizer μ)) : False := by
  rcases hroots with ⟨u,v,hu,hv,hlo,hup⟩ | ⟨u,v,hu,hv,hlo,hup⟩
  · exact no_supported_of_nonzero_real_opposite_roots μ hδ hmass hu hv hlo hup
  · exact no_supported_of_nonzero_padic_opposite_roots μ hδ hmass hu hv hlo hup

end VV.BBEKRigidityEscape
