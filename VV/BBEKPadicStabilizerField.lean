import VV.BBEKBoundedStabilizerField
import Mathlib.NumberTheory.Padics.RingHoms

/-! The p-adic root-group recurrence step.  A closed unbounded additive
subgroup of Q_p is all of Q_p: closedness extends integer multiples to
Z_p multiples, and an arbitrarily large subgroup element spans any fixed
target point over Z_p.  No algebraic-connectedness convention is needed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace VV.BBEKLeafwiseStabilizer

variable {p : ℕ} [Fact p.Prime]

theorem padic_closed_subgroup_padicInt_mul_mem (S : AddSubgroup ℚ_[p])
    (hclosed : IsClosed (S : Set ℚ_[p])) {u : ℚ_[p]} (hu : u ∈ S) (z : ℤ_[p]) :
    (z : ℚ_[p])*u ∈ S := by
  refine PadicInt.denseRange_natCast.induction_on z ?_ ?_
  · exact hclosed.preimage (continuous_subtype_val.mul continuous_const)
  · intro n
    simpa only [PadicInt.coe_natCast,nsmul_eq_mul] using S.nsmul_mem hu n

theorem padic_closed_subgroup_eq_top_of_unbounded (S : AddSubgroup ℚ_[p])
    (hclosed : IsClosed (S : Set ℚ_[p])) (hunbounded : ¬ BddAbove (subgroupNorms S)) :
    S = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨r,⟨u,hu,rfl⟩,hvu⟩ := not_bddAbove_iff.mp hunbounded ‖v‖
  have hu0 : u ≠ 0 := by
    intro hz
    simp only [hz,norm_zero] at hvu
    exact not_lt_of_ge (norm_nonneg v) hvu
  let z : ℤ_[p] := ⟨v/u,by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hu0)).mpr hvu.le⟩
  have h := padic_closed_subgroup_padicInt_mul_mem S hclosed hu z
  simpa only [z,div_mul_cancel₀ v hu0] using h

theorem ae_padic_subgroup_bot_or_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (S : X → AddSubgroup ℚ_[p])
    (hhit : ∀ O : Set ℚ_[p], IsOpen O → MeasurableSet {x | ∃ u ∈ S x, u ∈ O})
    (hclosed : ∀ᵐ x ∂μ, IsClosed (S x : Set ℚ_[p]))
    {a : ℚ_[p]} (ha : a ≠ 0) (ha1 : ‖a‖ < 1)
    (hcov : ∀ᵐ x ∂μ, S (T x) = (S x).map (rootDilation a ha).toAddMonoidHom) :
    ∀ᵐ x ∂μ, S x = ⊥ ∨ S x = ⊤ := by
  filter_upwards [ae_subgroup_bot_or_unbounded hT S hhit ha ha1 hcov,hclosed] with x hx hc
  exact hx.imp_right (padic_closed_subgroup_eq_top_of_unbounded (S x) hc)

theorem ae_padic_translationStabilizer_bot_or_top
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] [SecondCountableTopology ℚ_[p]]
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (η : X → Measure ℚ_[p])
    (hhit : ∀ O : Set ℚ_[p], IsOpen O →
      MeasurableSet {x | ∃ u ∈ translationStabilizer (η x), u ∈ O})
    (hregular : ∀ᵐ x ∂μ, (η x).OuterRegular)
    (hnorm : ∀ᵐ x ∂μ, η x (Metric.ball (0 : ℚ_[p]) 1) = 1)
    {a : ℚ_[p]} (ha : a ≠ 0) (ha1 : ‖a‖ < 1)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0, η (T x) = d • Measure.map (a * ·) (η x)) :
    ∀ᵐ x ∂μ, translationStabilizer (η x) = ⊥ ∨ translationStabilizer (η x) = ⊤ := by
  filter_upwards [ae_translationStabilizer_bot_or_unbounded hT η hhit hnorm ha ha1 hcov,hregular]
    with x hx hc
  letI := hc
  exact hx.imp_right (padic_closed_subgroup_eq_top_of_unbounded _
    (isClosed_translationStabilizer (η x)))

theorem ae_padic_projectiveTranslationStabilizer_bot_or_top
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] [SecondCountableTopology ℚ_[p]]
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (η : X → Measure ℚ_[p])
    (hhit : ∀ O : Set ℚ_[p], IsOpen O →
      MeasurableSet {x | ∃ u ∈ translationStabilizer (η x), u ∈ O})
    (hregular : ∀ᵐ x ∂μ, (η x).OuterRegular)
    (hmass : Measurable (fun x => η x (Metric.ball (0 : ℚ_[p]) 2)))
    (hnorm : ∀ᵐ x ∂μ, η x (Metric.ball (0 : ℚ_[p]) 1) = 1)
    (hfinite : ∀ᵐ x ∂μ, η x (Metric.ball (0 : ℚ_[p]) 2) ≠ ⊤)
    {a : ℚ_[p]} (ha : a ≠ 0) (ha1 : ‖a‖ < 1)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0, η (T x) = d • Measure.map (a * ·) (η x)) :
    ∀ᵐ x ∂μ, projectiveTranslationStabilizer (η x) = ⊥ ∨
      projectiveTranslationStabilizer (η x) = ⊤ := by
  have heq := ae_projectiveTranslationStabilizer_eq hT η hmass hnorm hfinite
    (rootDilation a ha) (measurable_const.mul measurable_id) (rootDilation_contracts ha ha1) hcov
  filter_upwards [heq,ae_padic_translationStabilizer_bot_or_top hT η hhit hregular hnorm ha ha1 hcov]
    with x hx hc
  simpa only [hx] using hc

end VV.BBEKLeafwiseStabilizer
