import VV.BBEKFactorEscape
import VV.BBEKMautner
import VV.BBEKRootSubgroups
import VV.BBEKUpperRootSubgroups

/-!
The actual subgroup of `G` preserving a measure on the BBEK quotient.
This packages elementwise root invariance into the subgroup language used by
the low-entropy argument and closes the elementary generation step from both
opposite root groups to a complete local `SL₂` factor.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped MatrixGroups

namespace VV.BBEKMeasureStabilizer
open BBEKDynamics BBEKQuotient BBEKTopology BBEKMautner BBEKFactorEscape
open BBEKDiagonal BBEKRootSubgroups BBEKUpperRootSubgroups

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The literal subgroup of elements whose action pushes `μ` to itself. -/
def measureStabilizer (μ : Measure X) : Subgroup G where
  carrier := {g | Measure.map (g • ·) μ = μ}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change Measure.map ((g * h) • ·) μ = μ
    rw [show ((g * h) • ·) = (g • ·) ∘ (h • ·) by
      funext x; exact mul_smul g h x]
    rw [← Measure.map_map (measurable_const_smul g) (measurable_const_smul h), hh, hg]
  inv_mem' := by
    intro g hg
    change Measure.map (g⁻¹ • ·) μ = μ
    have h := congrArg (Measure.map (g⁻¹ • ·)) hg
    rw [Measure.map_map (measurable_const_smul g⁻¹) (measurable_const_smul g)] at h
    rw [show (g⁻¹ • ·) ∘ (g • ·) = id by
      funext x; exact inv_smul_smul g x] at h
    simpa only [Measure.map_id] using h.symm

@[simp] theorem mem_measureStabilizer (μ : Measure X) (g : G) :
    g ∈ measureStabilizer μ ↔ Measure.map (g • ·) μ = μ := Iff.rfl

/-- By construction, the measure is invariant under its full stabilizer. -/
instance measureStabilizer_invariant (μ : Measure X) :
    SMulInvariantMeasure (measureStabilizer μ) X μ where
  measure_preimage_smul g s hs := by
    exact Measure.measure_preimage_of_map_eq_self g.property hs.nullMeasurableSet

theorem mem_measureStabilizer_iff_measurePreserving (μ : Measure X) (g : G) :
    g ∈ measureStabilizer μ ↔ MeasurePreserving (g • ·) μ μ := by
  constructor
  · intro h
    exact ⟨measurable_const_smul g, h⟩
  · exact fun h => h.map_eq

/-- An invariant action is literally contained in the pushforward stabilizer. -/
theorem A_le_measureStabilizer (μ : Measure X) [SMulInvariantMeasure A X μ] :
    A ≤ measureStabilizer μ := by
  intro a ha
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_const_smul (a : G)) hs]
  let aa : A := ⟨a, ha⟩
  have hA : μ ((fun x : X => aa • x) ⁻¹' s) = μ s :=
    SMulInvariantMeasure.measure_preimage_smul (M := A) aa hs
  simpa only [aa] using hA

/-- In particular, full diagonal invariance normalizes the measure stabilizer. -/
theorem A_le_measureStabilizer_normalizer (μ : Measure X)
    [SMulInvariantMeasure A X μ] : A ≤ (measureStabilizer μ).normalizer :=
  (A_le_measureStabilizer μ).trans (measureStabilizer μ).le_normalizer

theorem all_real_lower_mem_of_nonzero (μ : Measure X)
    [SMulInvariantMeasure A X μ] {u : ℝ} (hu0 : u ≠ 0)
    (hu : x u 0 ∈ measureStabilizer μ) :
    ∀ v : ℝ, x v 0 ∈ measureStabilizer μ :=
  all_real_lower_mem (measureStabilizer μ)
    (A_le_measureStabilizer_normalizer μ) hu0 hu

theorem all_padic_lower_mem_of_nonzero (μ : Measure X)
    [SMulInvariantMeasure A X μ] {u : Q2} (hu0 : u ≠ 0)
    (hu : x 0 u ∈ measureStabilizer μ) :
    ∀ v : Q2, x 0 v ∈ measureStabilizer μ :=
  all_padic_lower_mem (measureStabilizer μ)
    (A_le_measureStabilizer_normalizer μ) hu0 hu

theorem all_real_upper_mem_of_nonzero (μ : Measure X)
    [SMulInvariantMeasure A X μ] {u : ℝ} (hu0 : u ≠ 0)
    (hu : upperPoint u 0 ∈ measureStabilizer μ) :
    ∀ v : ℝ, upperPoint v 0 ∈ measureStabilizer μ :=
  all_real_upper_mem (measureStabilizer μ)
    (A_le_measureStabilizer_normalizer μ) hu0 hu

theorem all_padic_upper_mem_of_nonzero (μ : Measure X)
    [SMulInvariantMeasure A X μ] {u : Q2} (hu0 : u ≠ 0)
    (hu : upperPoint 0 u ∈ measureStabilizer μ) :
    ∀ v : Q2, upperPoint 0 v ∈ measureStabilizer μ :=
  all_padic_upper_mem (measureStabilizer μ)
    (A_le_measureStabilizer_normalizer μ) hu0 hu

/-- Invariance under the real upper and lower root groups generates the entire
real local factor, by explicit two-by-two elimination. -/
theorem realFactor_le_of_opposite_roots (μ : Measure X)
    (hlower : ∀ u : ℝ, x u 0 ∈ measureStabilizer μ)
    (hupper : ∀ u : ℝ, upperPoint u 0 ∈ measureStabilizer μ) :
    realFactor ≤ measureStabilizer μ := by
  let H : Subgroup SL(2, ℝ) :=
    (measureStabilizer μ).comap (MonoidHom.inl SL(2, ℝ) SL(2, Q2))
  have htop : H = ⊤ := sl_subgroup_eq_top_of_unipotents H
    (fun u => by
      dsimp [H]
      simpa only [MonoidHom.inl_apply, upperPoint,
        BBEKFiniteQuotients.upper_zero] using hupper u)
    (fun u => by
      dsimp [H]
      simpa only [MonoidHom.inl_apply, x, BBEKDynamics.lower_zero] using hlower u)
  intro g hg
  change g.2 = 1 at hg
  have hmem : g.1 ∈ H := by rw [htop]; trivial
  change (g.1, g.2) ∈ measureStabilizer μ
  simpa only [hg] using hmem

/-- The analogous generation statement for the 2-adic local factor. -/
theorem padicFactor_le_of_opposite_roots (μ : Measure X)
    (hlower : ∀ u : Q2, x 0 u ∈ measureStabilizer μ)
    (hupper : ∀ u : Q2, upperPoint 0 u ∈ measureStabilizer μ) :
    padicFactor ≤ measureStabilizer μ := by
  let H : Subgroup SL(2, Q2) :=
    (measureStabilizer μ).comap (MonoidHom.inr SL(2, ℝ) SL(2, Q2))
  have htop : H = ⊤ := sl_subgroup_eq_top_of_unipotents H
    (fun u => by
      dsimp [H]
      simpa only [MonoidHom.inr_apply, upperPoint,
        BBEKFiniteQuotients.upper_zero] using hupper u)
    (fun u => by
      dsimp [H]
      simpa only [MonoidHom.inr_apply, x, BBEKDynamics.lower_zero] using hlower u)
  intro g hg
  change g.1 = 1 at hg
  have hmem : g.2 ∈ H := by rw [htop]; trivial
  change (g.1, g.2) ∈ measureStabilizer μ
  simpa only [hg] using hmem

/-- Both real root directions are incompatible with compact Mahler support. -/
theorem no_opposite_real_roots_supported_K
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hlower : ∀ u : ℝ, x u 0 ∈ measureStabilizer μ)
    (hupper : ∀ u : ℝ, upperPoint u 0 ∈ measureStabilizer μ)
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (BBEKOrbit.K δ) = 1) : False :=
  no_subgroup_invariant_probability_supported_K_of_realFactor
    (measureStabilizer μ) μ (realFactor_le_of_opposite_roots μ hlower hupper) hδ hmass

/-- Both 2-adic root directions are incompatible with compact Mahler support. -/
theorem no_opposite_padic_roots_supported_K
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hlower : ∀ u : Q2, x 0 u ∈ measureStabilizer μ)
    (hupper : ∀ u : Q2, upperPoint 0 u ∈ measureStabilizer μ)
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (BBEKOrbit.K δ) = 1) : False :=
  no_subgroup_invariant_probability_supported_K_of_padicFactor
    (measureStabilizer μ) μ (padicFactor_le_of_opposite_roots μ hlower hupper) hδ hmass

/-- Under the already available full-diagonal invariance, one nonzero element
in each real root direction is enough: diagonal conjugation fills both roots,
then they generate the complete real local factor. -/
theorem no_nonzero_opposite_real_roots_supported_K
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {u v : ℝ} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hlower : x u 0 ∈ measureStabilizer μ)
    (hupper : upperPoint v 0 ∈ measureStabilizer μ)
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (BBEKOrbit.K δ) = 1) : False :=
  no_opposite_real_roots_supported_K μ
    (all_real_lower_mem_of_nonzero μ hu0 hlower)
    (all_real_upper_mem_of_nonzero μ hv0 hupper) hδ hmass

/-- The identical endpoint for the two 2-adic root directions. -/
theorem no_nonzero_opposite_padic_roots_supported_K
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure A X μ]
    {u v : Q2} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hlower : x 0 u ∈ measureStabilizer μ)
    (hupper : upperPoint 0 v ∈ measureStabilizer μ)
    {δ : ℝ} (hδ : 0 < δ) (hmass : μ (BBEKOrbit.K δ) = 1) : False :=
  no_opposite_padic_roots_supported_K μ
    (all_padic_lower_mem_of_nonzero μ hu0 hlower)
    (all_padic_upper_mem_of_nonzero μ hv0 hupper) hδ hmass

end VV.BBEKMeasureStabilizer
