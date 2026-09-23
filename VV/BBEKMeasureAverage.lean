import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Dynamics.Ergodic.Action.OfMinimal
import Mathlib.Tactic

/-!
Actual averaging of measures for the compact-group averaging step in BBEK 5.2.
The average is a pushforward of a product measure under the actual action,
not a measure postulated to have the desired invariance properties.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Function Filter
open scoped ENNReal Topology

namespace VV.BBEKMeasureAverage

variable {K X : Type*} [Group K] [MeasurableSpace K] [MeasurableSpace X]
  [MulAction K X] [MeasurableSMul₂ K X]

def average (ν : Measure K) (μ : Measure X) : Measure X :=
  Measure.map (fun p : K × X => p.1 • p.2) (ν.prod μ)

theorem average_apply (ν : Measure K) (μ : Measure X) [SFinite μ]
    {s : Set X} (hs : MeasurableSet s) :
    average ν μ s = ∫⁻ k, μ ((k • ·) ⁻¹' s) ∂ν := by
  rw [average, Measure.map_apply (measurable_fst.smul measurable_snd) hs,
    Measure.prod_apply (hs.preimage (measurable_fst.smul measurable_snd))]
  rfl

instance average_isProbabilityMeasure (ν : Measure K) (μ : Measure X)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (average ν μ) :=
  isProbabilityMeasure_map (measurable_fst.smul measurable_snd).aemeasurable

theorem map_average_smul (ν : Measure K) (μ : Measure X)
    [SFinite ν] [SFinite μ] [MeasurableMul K] [ν.IsMulLeftInvariant] (k : K) :
    Measure.map (k • ·) (average ν μ) = average ν μ := by
  have hp := (measurePreserving_mul_left ν k).prod (MeasurePreserving.id μ)
  unfold average
  rw [Measure.map_map (measurable_const_smul k) (measurable_fst.smul measurable_snd)]
  have he : (fun x : X => k • x) ∘ (fun p : K × X => p.1 • p.2) =
      (fun p : K × X => p.1 • p.2) ∘ Prod.map (k * ·) id := by
    funext p
    simp [mul_smul]
  rw [he, ← Measure.map_map (measurable_fst.smul measurable_snd) hp.measurable, hp.map_eq]

instance average_smulInvariantMeasure (ν : Measure K) (μ : Measure X)
    [SFinite ν] [SFinite μ] [MeasurableMul K] [ν.IsMulLeftInvariant] :
    SMulInvariantMeasure K X (average ν μ) where
  measure_preimage_smul k s hs := by
    rw [← Measure.map_apply (measurable_const_smul k) hs,
      map_average_smul ν μ k]

theorem map_average_commuting {H : Type*} [Monoid H] [MeasurableSpace H]
    [MulAction H X] [MeasurableSMul H X] [SMulCommClass H K X]
    (ν : Measure K) (μ : Measure X) [SFinite ν] [SFinite μ]
    [SMulInvariantMeasure H X μ] (h : H) :
    Measure.map (h • ·) (average ν μ) = average ν μ := by
  have hp := (MeasurePreserving.id ν).prod (measurePreserving_smul h μ)
  unfold average
  rw [Measure.map_map (measurable_const_smul h) (measurable_fst.smul measurable_snd)]
  have he : (fun x : X => h • x) ∘ (fun p : K × X => p.1 • p.2) =
      (fun p : K × X => p.1 • p.2) ∘ Prod.map id (h • ·) := by
    funext p
    exact smul_comm h p.1 p.2
  rw [he, ← Measure.map_map (measurable_fst.smul measurable_snd) hp.measurable, hp.map_eq]

theorem commuting_smulInvariantMeasure {H : Type*} [Monoid H] [MeasurableSpace H]
    [MulAction H X] [MeasurableSMul H X] [SMulCommClass H K X]
    (ν : Measure K) (μ : Measure X) [SFinite ν] [SFinite μ]
    [SMulInvariantMeasure H X μ] : SMulInvariantMeasure H X (average ν μ) where
  measure_preimage_smul h s hs := by
    rw [← Measure.map_apply (measurable_const_smul h) hs,
      map_average_commuting ν μ h]

theorem average_apply_of_invariant_set (ν : Measure K) (μ : Measure X)
    [IsProbabilityMeasure ν] [SFinite μ] {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ k : K, (k • ·) ⁻¹' s = s) : average ν μ s = μ s := by
  rw [average_apply ν μ hs]
  simp only [hinv, lintegral_const, measure_univ, mul_one]




/-- A measurable invariant section has probability zero or one. -/
lemma measure_zero_or_one_of_eventuallyConst {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {s : Set Y}
    (h : EventuallyConst s (ae μ)) : μ s = 0 ∨ μ s = 1 := by
  rcases eventuallyConst_set'.mp h with h | h
  · exact Or.inl ((measure_congr h).trans (measure_empty))
  · exact Or.inr ((measure_congr h).trans (measure_univ))

/-- Fubini is applied before the countable intersection of exceptional null sets.
This avoids exchanging an uncountable `∀ h` with almost everywhere. -/
theorem section_zero_or_one {H : Type*} [Group H] [Countable H] [MeasurableSpace H]
    [MulAction H X] [MeasurableSMul H X] [SMulCommClass H K X]
    (ν : Measure K) (μ : Measure X) [SFinite ν] [IsProbabilityMeasure μ]
    [ErgodicSMul H X μ] {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ h : H, (h • ·) ⁻¹' s =ᵐ[average ν μ] s) :
    ∀ᵐ k ∂ν, μ ((k • ·) ⁻¹' s) = 0 ∨ μ ((k • ·) ⁻¹' s) = 1 := by
  have hall : ∀ h : H, ∀ᵐ k ∂ν,
      (h • ·) ⁻¹' ((k • ·) ⁻¹' s) =ᵐ[μ] (k • ·) ⁻¹' s := by
    intro h
    have hp : ∀ᵐ p : K × X ∂ν.prod μ,
        h • (p.1 • p.2) ∈ s ↔ p.1 • p.2 ∈ s :=
      ae_of_ae_map (measurable_fst.smul measurable_snd).aemeasurable (hinv h).mem_iff
    filter_upwards [ae_ae_of_ae_prod hp] with k hk
    filter_upwards [hk] with x hx
    exact propext (by simpa only [mem_preimage, smul_comm h k x] using hx)
  filter_upwards [ae_all_iff.mpr hall] with k hk
  exact measure_zero_or_one_of_eventuallyConst μ
    (aeconst_of_forall_preimage_smul_ae_eq H
      (hs.preimage (measurable_const_smul k)).nullMeasurableSet hk)

/-- Invariance of the averaged measure's event under the compact direction
makes its section probabilities almost everywhere left invariant on that group. -/
theorem section_mass_invariant (ν : Measure K) (μ : Measure X)
    [SFinite ν] [SFinite μ] {s : Set X} (k₀ : K)
    (hinv : (k₀ • ·) ⁻¹' s =ᵐ[average ν μ] s) :
    ∀ᵐ k ∂ν, μ (((k₀ * k) • ·) ⁻¹' s) = μ ((k • ·) ⁻¹' s) := by
  have hp : ∀ᵐ p : K × X ∂ν.prod μ,
      k₀ • (p.1 • p.2) ∈ s ↔ p.1 • p.2 ∈ s :=
    ae_of_ae_map (measurable_fst.smul measurable_snd).aemeasurable hinv.mem_iff
  filter_upwards [ae_ae_of_ae_prod hp] with k hk
  apply measure_congr
  filter_upwards [hk] with x hx
  exact propext (by simpa only [mem_preimage, mul_smul] using hx)

/-- Averaging an ergodic probability under a commuting compact direction
is jointly ergodic. The countable group here can be a dense subgroup of a
continuous real action; no uncountable almost-everywhere intersection is used. -/
theorem joint_aeconst {H : Type*} [Group H] [Countable H] [MeasurableSpace H]
    [MulAction H X] [MeasurableSMul H X] [SMulCommClass H K X]
    [MeasurableMul₂ K] [MeasurableInv K]
    (ν : Measure K) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    [ν.IsMulLeftInvariant] [ErgodicSMul H X μ]
    {s : Set X} (hs : MeasurableSet s)
    (hH : ∀ h : H, (h • ·) ⁻¹' s =ᵐ[average ν μ] s)
    (hK : ∀ k : K, (k • ·) ⁻¹' s =ᵐ[average ν μ] s) :
    EventuallyConst s (ae (average ν μ)) := by
  let p : K → ℝ≥0∞ := fun k => μ ((k • ·) ⁻¹' s)
  have hp : Measurable p :=
    measurable_measure_prodMk_left (hs.preimage (measurable_fst.smul measurable_snd))
  let u : Set K := {k | p k = 1}
  have hu : MeasurableSet u := hp (measurableSet_singleton 1)
  have hi : ∀ k₀ : K, (k₀ • ·) ⁻¹' u =ᵐ[ν] u := by
    intro k₀
    filter_upwards [section_mass_invariant ν μ k₀ (hK k₀)] with k hk
    exact propext (by change μ (((k₀ * k) • ·) ⁻¹' s) = 1 ↔ μ ((k • ·) ⁻¹' s) = 1; rw [hk])
  have hc := aeconst_of_forall_preimage_smul_ae_eq K hu.nullMeasurableSet hi
  have h01 := section_zero_or_one ν μ hs hH
  rcases eventuallyConst_set.mp hc with h1 | h0
  · have hm : average ν μ s = 1 := by
      rw [average_apply ν μ hs]
      calc
        (∫⁻ k, p k ∂ν) = ∫⁻ _ : K, (1 : ℝ≥0∞) ∂ν := lintegral_congr_ae h1
        _ = 1 := by simp
    apply eventuallyConst_set'.mpr
    right
    exact (ae_eq_univ_iff_measure_eq hs.nullMeasurableSet).mpr (by simpa using hm)
  · have hm : average ν μ s = 0 := by
      rw [average_apply ν μ hs]
      calc
        (∫⁻ k, p k ∂ν) = ∫⁻ _ : K, (0 : ℝ≥0∞) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [h01, h0] with k hk hk0
          exact hk.resolve_right hk0
        _ = 0 := by simp
    exact eventuallyConst_set'.mpr (Or.inl (ae_eq_empty.mpr hm))

section CompactHaar
variable [TopologicalSpace K] [IsTopologicalGroup K] [BorelSpace K]
  [CompactSpace K] [T2Space K]

/-- Haar probability normalized on the whole compact group. -/
def haarProbability : Measure K :=
  haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)

instance haarProbability_isProbabilityMeasure :
    IsProbabilityMeasure (haarProbability (K := K)) where
  measure_univ := by
    simpa [haarProbability] using
      (haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K)))

instance haarProbability_leftInvariant : (haarProbability (K := K)).IsMulLeftInvariant :=
  inferInstanceAs (haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)).IsMulLeftInvariant
end CompactHaar





/-- The continuous-action version uses a countable dense set of parameters,
then extends almost-everywhere invariance by continuity in measure. -/
theorem section_zero_or_one_continuous {H : Type*} [Group H]
    [MeasurableSpace H] [TopologicalSpace H] [TopologicalSpace.SeparableSpace H]
    [TopologicalSpace X] [R1Space X] [BorelSpace X]
    [MulAction H X] [MeasurableSMul H X] [ContinuousSMul H X] [SMulCommClass H K X]
    (ν : Measure K) (μ : Measure X) [SFinite ν] [IsProbabilityMeasure μ]
    [μ.InnerRegular] [ErgodicSMul H X μ] {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ h : H, (h • ·) ⁻¹' s =ᵐ[average ν μ] s) :
    ∀ᵐ k ∂ν, μ ((k • ·) ⁻¹' s) = 0 ∨ μ ((k • ·) ⁻¹' s) = 1 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense H
  letI : Countable D := hDc.to_subtype
  have hall : ∀ h : D, ∀ᵐ k ∂ν,
      (h.val • ·) ⁻¹' ((k • ·) ⁻¹' s) =ᵐ[μ] (k • ·) ⁻¹' s := by
    intro h
    have hp : ∀ᵐ p : K × X ∂ν.prod μ,
        h.val • (p.1 • p.2) ∈ s ↔ p.1 • p.2 ∈ s :=
      ae_of_ae_map (measurable_fst.smul measurable_snd).aemeasurable (hinv h.val).mem_iff
    filter_upwards [ae_ae_of_ae_prod hp] with k hk
    filter_upwards [hk] with x hx
    exact propext (by simpa only [mem_preimage, smul_comm h.val k x] using hx)
  filter_upwards [ae_all_iff.mpr hall] with k hk
  apply measure_zero_or_one_of_eventuallyConst μ
  apply aeconst_of_dense_setOf_preimage_smul_ae (M := H)
    (hs.preimage (measurable_const_smul k)).nullMeasurableSet
  exact hDd.mono (fun h hh => hk ⟨h, hh⟩)

/-- Joint ergodicity for the actual average under a separable continuous
commuting ergodic action. In particular, an uncountable real parameter group
is allowed; the proof uses only countable intersections of null sets. -/
theorem joint_aeconst_continuous {H : Type*} [Group H]
    [MeasurableSpace H] [TopologicalSpace H] [TopologicalSpace.SeparableSpace H]
    [TopologicalSpace X] [R1Space X] [BorelSpace X]
    [MulAction H X] [MeasurableSMul H X] [ContinuousSMul H X] [SMulCommClass H K X]
    [MeasurableMul₂ K] [MeasurableInv K]
    (ν : Measure K) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    [ν.IsMulLeftInvariant] [μ.InnerRegular] [ErgodicSMul H X μ]
    {s : Set X} (hs : MeasurableSet s)
    (hH : ∀ h : H, (h • ·) ⁻¹' s =ᵐ[average ν μ] s)
    (hK : ∀ k : K, (k • ·) ⁻¹' s =ᵐ[average ν μ] s) :
    EventuallyConst s (ae (average ν μ)) := by
  let p : K → ℝ≥0∞ := fun k => μ ((k • ·) ⁻¹' s)
  have hp : Measurable p :=
    measurable_measure_prodMk_left (hs.preimage (measurable_fst.smul measurable_snd))
  let u : Set K := {k | p k = 1}
  have hu : MeasurableSet u := hp (measurableSet_singleton 1)
  have hi : ∀ k₀ : K, (k₀ • ·) ⁻¹' u =ᵐ[ν] u := by
    intro k₀
    filter_upwards [section_mass_invariant ν μ k₀ (hK k₀)] with k hk
    exact propext (by change μ (((k₀ * k) • ·) ⁻¹' s) = 1 ↔ μ ((k • ·) ⁻¹' s) = 1; rw [hk])
  have hc := aeconst_of_forall_preimage_smul_ae_eq K hu.nullMeasurableSet hi
  have h01 := section_zero_or_one_continuous ν μ hs hH
  rcases eventuallyConst_set.mp hc with h1 | h0
  · have hm : average ν μ s = 1 := by
      rw [average_apply ν μ hs]
      calc
        (∫⁻ k, p k ∂ν) = ∫⁻ _ : K, (1 : ℝ≥0∞) ∂ν := lintegral_congr_ae h1
        _ = 1 := by simp
    apply eventuallyConst_set'.mpr
    right
    exact (ae_eq_univ_iff_measure_eq hs.nullMeasurableSet).mpr (by simpa using hm)
  · have hm : average ν μ s = 0 := by
      rw [average_apply ν μ hs]
      calc
        (∫⁻ k, p k ∂ν) = ∫⁻ _ : K, (0 : ℝ≥0∞) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [h01, h0] with k hk hk0
          exact hk.resolve_right hk0
        _ = 0 := by simp
    exact eventuallyConst_set'.mpr (Or.inl (ae_eq_empty.mpr hm))

end VV.BBEKMeasureAverage

