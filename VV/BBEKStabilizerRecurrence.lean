import VV.BBEKRootStabilizer

/-! Recurrence excludes nonzero finite measurable scales that transform by
a strict contraction.  This is the scalar-observable part of the argument
that rules out discrete leafwise stabilizers. -/

noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology

namespace VV.BBEKLeafwiseStabilizer

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  {T : X → X}

/-- A measurable observable covariant under a dynamics whose every orbit
converges to one point must equal that point almost surely in a finite
measure-preserving system.  The returning subsequence is obtained from
Poincaré recurrence, not supplied as an assumption. -/
theorem ae_eq_of_contracting_covariance
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [FirstCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (hT : MeasurePreserving T μ μ) {f : X → Y} (hf : Measurable f)
    {σ : Y → Y} {z : Y}
    (hcontract : ∀ y, Tendsto (fun n : ℕ => (σ^[n]) y) atTop (𝓝 z))
    (hcov : ∀ᵐ x ∂μ, f (T x) = σ (f x)) : ∀ᵐ x ∂μ, f x = z := by
  have hcovAll : ∀ᵐ x ∂μ, ∀ n : ℕ,
      f (T ((T^[n]) x)) = σ (f ((T^[n]) x)) := by
    apply ae_all_iff.mpr
    intro n
    exact (hT.iterate n).quasiMeasurePreserving.ae hcov
  filter_upwards [ae_observable_recurrent_subseq hT hf,hcovAll] with x hx hxcov
  obtain ⟨n,hn,hlim⟩ := hx
  have hiter (k : ℕ) : f ((T^[k]) x) = (σ^[k]) (f x) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',hxcov k,ih,Function.iterate_succ_apply']
  have hzero : Tendsto (fun j => f ((T^[n j]) x)) atTop (𝓝 z) := by
    simpa only [hiter] using (hcontract (f x)).comp hn.tendsto_atTop
  exact tendsto_nhds_unique hlim hzero

theorem ae_eq_zero_of_scalar_covariance
    {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    (hT : MeasurePreserving T μ μ) {f : X → F} (hf : Measurable f)
    {a : F} (ha : a ≠ 0) (hsmall : ‖a‖ < 1)
    (hcov : ∀ᵐ x ∂μ, f (T x) = a * f x) : ∀ᵐ x ∂μ, f x = 0 := by
  exact ae_eq_of_contracting_covariance hT hf (rootDilation_contracts ha hsmall) hcov

end VV.BBEKLeafwiseStabilizer
