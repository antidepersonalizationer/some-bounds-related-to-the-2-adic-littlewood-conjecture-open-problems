import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Exponentially thin boundaries for subordinate root partitions

For a finite measure and a measurable real observable, almost every cutting
level has summable masses of geometrically shrinking boundary strips. Applied
to distance from a chart center, this supplies the Borel--Cantelli boundary
control needed to keep inverse iterates inside local root plaques.

The cutting level is constructed by integrating the actual strip masses over
Lebesgue measure; zero mass of the boundary alone is not used as a substitute.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace VV.BBEKLeafEntropyBoundary

variable {Z : Type*} [MeasurableSpace Z]

/-- Points whose observable lies within ε of the proposed cutting level. -/
def boundaryTube (f : Z → ℝ) (r ε : ℝ) : Set Z := {x | |f x-r| ≤ ε}

theorem measurableSet_boundaryTube {f : Z → ℝ} (hf : Measurable f) (r ε : ℝ) :
    MeasurableSet (boundaryTube f r ε) :=
  measurableSet_le (continuous_abs.measurable.comp (hf.sub_const r)) measurable_const

theorem measurable_boundaryTube_mass (μ : Measure Z) [IsFiniteMeasure μ]
    {f : Z → ℝ} (hf : Measurable f) (ε : ℝ) :
    Measurable (fun r : ℝ => μ (boundaryTube f r ε)) := by
  have hs : MeasurableSet {p : ℝ × Z | |f p.2-p.1| ≤ ε} :=
    measurableSet_le (continuous_abs.measurable.comp ((hf.comp measurable_snd).sub measurable_fst)) measurable_const
  exact measurable_measure_prodMk_left hs

/-- Fubini computes the exact average mass of the boundary strip. -/
theorem lintegral_boundaryTube_mass (μ : Measure Z) [IsFiniteMeasure μ]
    {f : Z → ℝ} (hf : Measurable f) (ε : ℝ) :
    (∫⁻ r : ℝ, μ (boundaryTube f r ε)) = ENNReal.ofReal (2*ε) * μ univ := by
  let S : Set (ℝ × Z) := {p | |f p.2-p.1| ≤ ε}
  have hS : MeasurableSet S :=
    measurableSet_le (continuous_abs.measurable.comp ((hf.comp measurable_snd).sub measurable_fst)) measurable_const
  have hslice (x : Z) : (fun r : ℝ => (r,x)) ⁻¹' S = Icc (f x-ε) (f x+ε) := by
    ext r
    simp only [S, mem_preimage, mem_setOf_eq, mem_Icc, abs_le]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  calc
    _ = (volume.prod μ) S := (Measure.prod_apply hS).symm
    _ = ∫⁻ x, volume ((fun r : ℝ => (r,x)) ⁻¹' S) ∂μ := Measure.prod_apply_symm hS
    _ = _ := by
      simp_rw [hslice, Real.volume_Icc, show ∀ x : Z, (f x+ε)-(f x-ε)=2*ε by intro x; ring]
      exact lintegral_const _

/-- The entire geometric boundary sum has finite integral over cutting levels. -/
theorem lintegral_geometric_boundary_sum_lt_top
    (μ : Measure Z) [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {c θ : ℝ} (hc : 0 ≤ c) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (∫⁻ r : ℝ, ∑' n : ℕ, μ (boundaryTube f r (c*θ^n))) < ∞ := by
  rw [lintegral_tsum (fun n => (measurable_boundaryTube_mass μ hf (c*θ^n)).aemeasurable)]
  simp_rw [lintegral_boundaryTube_mass μ hf,
    show ∀ n : ℕ, 2*(c*θ^n)=(2*c)*θ^n by intro n; ring,
    ENNReal.ofReal_mul (show 0 ≤ 2*c by positivity), ENNReal.ofReal_pow hθ0]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  apply ENNReal.mul_lt_top
  · apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    apply ENNReal.inv_lt_top.mpr
    exact tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr hθ1)
  · exact measure_lt_top _ _

/-- Almost every cutting level has a summable geometric boundary sequence. -/
theorem ae_geometric_boundary_sum_lt_top
    (μ : Measure Z) [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {c θ : ℝ} (hc : 0 ≤ c) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∀ᵐ r : ℝ, (∑' n : ℕ, μ (boundaryTube f r (c*θ^n))) < ∞ :=
  ae_lt_top (Measurable.ennreal_tsum (fun n => measurable_boundaryTube_mass μ hf (c*θ^n)))
    (lintegral_geometric_boundary_sum_lt_top μ hf hc hθ0 hθ1).ne

/-- Every nonempty open interval contains a cutting level with summable
boundary masses and almost-surely only finitely many boundary encounters. -/
theorem exists_geometric_boundary_cut
    (μ : Measure Z) [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {a b c θ : ℝ} (hab : a < b) (hc : 0 ≤ c) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ r ∈ Ioo a b,
      (∑' n : ℕ, μ (boundaryTube f r (c*θ^n))) < ∞ ∧
      (∀ᵐ x ∂μ, {n : ℕ | x ∈ boundaryTube f r (c*θ^n)}.Finite) ∧
      (∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, c*θ^n < |f x-r|) := by
  have hinterval : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  obtain ⟨r,hr,hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hinterval
    (ae_restrict_of_ae (ae_geometric_boundary_sum_lt_top μ hf hc hθ0 hθ1))
  refine ⟨r,hr,hs,ae_finite_setOf_mem hs.ne,?_⟩
  simpa only [boundaryTube, mem_setOf_eq, not_le] using ae_eventually_notMem hs.ne

/-- Invariance converts the same summable boundary estimate into avoidance
along the actual iterates. The radius is not allowed to depend on the iterate. -/
theorem ae_orbit_eventually_away
    (μ : Measure Z) [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {T : Z → Z} (hT : MeasurePreserving T μ μ) {r c θ : ℝ}
    (hs : (∑' n : ℕ, μ (boundaryTube f r (c*θ^n))) < ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, c*θ^n < |f ((T^[n]) x)-r| := by
  have hm : (fun n : ℕ => μ ((T^[n]) ⁻¹' boundaryTube f r (c*θ^n))) =
      (fun n : ℕ => μ (boundaryTube f r (c*θ^n))) := by
    funext n
    exact (hT.iterate n).measure_preimage (measurableSet_boundaryTube hf _ _).nullMeasurableSet
  have ha := ae_eventually_notMem (s := fun n : ℕ => (T^[n]) ⁻¹' boundaryTube f r (c*θ^n))
    (by rw [hm]; exact hs.ne)
  simpa only [mem_preimage, boundaryTube, mem_setOf_eq, not_le] using ha

/-- A summable nonnegative boundary sequence includes a null cutting level. -/
theorem measure_level_eq_zero
    (μ : Measure Z) [IsFiniteMeasure μ] {f : Z → ℝ} {r c θ : ℝ}
    (hc : 0 ≤ c) (hθ : 0 ≤ θ)
    (hs : (∑' n : ℕ, μ (boundaryTube f r (c*θ^n))) < ∞) :
    μ {x | f x = r} = 0 := by
  have ha : ∀ᵐ x ∂μ, f x ≠ r := by
    filter_upwards [ae_eventually_notMem hs.ne] with x hx
    intro he
    obtain ⟨n,hn⟩ := hx.exists
    apply hn
    change |f x-r| ≤ c*θ^n
    rw [he, sub_self, abs_zero]
    exact mul_nonneg hc (pow_nonneg hθ n)
  simpa only [ae_iff, not_not] using ha

section Metric
variable [PseudoMetricSpace Z] [OpensMeasurableSpace Z]

/-- The distance observable gives actual metric ball boundaries, at every
prescribed geometric shrinking rate and inside any chosen radius interval. -/
theorem exists_geometric_ball_boundary_cut
    (μ : Measure Z) [IsFiniteMeasure μ] (z : Z)
    {a b c θ : ℝ} (hab : a < b) (hc : 0 ≤ c) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ r ∈ Ioo a b,
      (∑' n : ℕ, μ {x | |dist x z-r| ≤ c*θ^n}) < ∞ ∧
      (∀ᵐ x ∂μ, {n : ℕ | |dist x z-r| ≤ c*θ^n}.Finite) ∧
      (∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, c*θ^n < |dist x z-r|) :=
  exists_geometric_boundary_cut μ (continuous_id.dist continuous_const).measurable
    hab hc hθ0 hθ1

end Metric
end VV.BBEKLeafEntropyBoundary
