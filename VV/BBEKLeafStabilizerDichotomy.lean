import VV.BBEKLeafStabilizerMeasurable
import VV.BBEKRadonModification
import VV.BBEKRealStabilizerField
import VV.BBEKPadicStabilizerField

/-! The actual measurable Radon-family hypotheses imply the hit measurability
needed for the recurrent real and p-adic subgroup dichotomies. A null-set
modification is used only inside the proof, and the conclusion concerns the
original family. The original normalization radius is retained. -/
noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped Topology ENNReal NNReal
namespace VV.BBEKLeafStabilizerDichotomy
open BBEKLeafwiseStabilizer BBEKLeafStabilizerMeasurable BBEKRadonModification

section General
variable {Z U : Type*} [MeasurableSpace Z]
  [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
  [ProperSpace U] [SecondCountableTopology U]
  {μ : Measure Z} [IsFiniteMeasure μ] {T : Z → Z}

/-- A measurable everywhere-Radon version gives an actual measurable hit
field, and agrees with the original canonical family almost everywhere. -/
theorem exists_regular_hit_version (η : Z → Measure U) (hη : Measurable η)
    (hreg : ∀ᵐ q ∂μ, (η q).Regular) :
    ∃ θ : Z → Measure U, Measurable θ ∧ θ =ᵐ[μ] η ∧
      (∀ q, (θ q).Regular) ∧
      ∀ O : Set U, IsOpen O →
        MeasurableSet {q | ∃ u ∈ translationStabilizer (θ q), u ∈ O} := by
  obtain ⟨θ,hθ,heq,hθreg⟩ := exists_everywhere_good_ae_eq μ η hη
    (fun ν : Measure U => ν.Regular) hreg 0 inferInstance
  letI : ∀ q, (θ q).Regular := hθreg
  exact ⟨θ,hθ,heq,hθreg,fun _ hO => measurableSet_stabilizer_hit θ hθ hO⟩

/-- Projective covariance with the literal radius-r normalization gives
subgroup covariance. The normalization is only used to prove d is nonzero. -/
theorem stabilizer_covariance_of_ae_eq
    (hT : MeasurePreserving T μ μ) (η θ : Z → Measure U)
    (heq : θ =ᵐ[μ] η) {r : ℝ}
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    (σ : U ≃+ U) (hσ : Measurable σ) (hσi : Measurable σ.symm)
    (hcov : ∀ᵐ q ∂μ, ∃ d : ℝ≥0, η (T q) = d • (η q).map σ) :
    ∀ᵐ q ∂μ, translationStabilizer (θ (T q)) =
      (translationStabilizer (θ q)).map σ.toAddMonoidHom := by
  filter_upwards [heq,hT.quasiMeasurePreserving.ae heq,hcov,
    hT.quasiMeasurePreserving.ae hnorm] with q he heT hc hn
  obtain ⟨d,hd⟩ := hc
  have hd0 : d ≠ 0 := by
    intro hz
    simp only [hz,zero_smul] at hd
    simp only [hd,Measure.coe_zero,Pi.zero_apply] at hn
    exact zero_ne_one hn
  rw [heT,he,hd]
  exact translationStabilizer_projective_map σ hσ hσi (η q) hd0
end General

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [IsFiniteMeasure μ] {T : Z → Z}

/-- A measurable real leaf family under one strict contraction has only
trivial or full exact stabilizers almost everywhere. No hit assumption is supplied. -/
theorem ae_real_stabilizer_bot_or_top
    (hT : MeasurePreserving T μ μ) (η : Z → Measure ℝ) (hη : Measurable η)
    (hreg : ∀ᵐ q ∂μ, (η q).Regular) {r : ℝ}
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hcov : ∀ᵐ q ∂μ, ∃ d : ℝ≥0, η (T q) = d • (η q).map (a * ·)) :
    ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊥ ∨ translationStabilizer (η q) = ⊤ := by
  obtain ⟨θ,hθ,heq,hθreg,hhit⟩ := exists_regular_hit_version η hη hreg
  letI : ∀ q, (θ q).Regular := hθreg
  have hc := stabilizer_covariance_of_ae_eq hT η θ heq hnorm (rootDilation a ha.ne')
    (measurable_const.mul measurable_id) (measurable_const.mul measurable_id) hcov
  have hd := ae_real_subgroup_bot_or_top hT (fun q => translationStabilizer (θ q)) hhit
    (ae_of_all _ fun q => isClosed_translationStabilizer (θ q)) ha ha1 hc
  filter_upwards [heq,hd] with q he hq
  simpa only [he] using hq

/-- The corresponding theorem for Q_p, again retaining the family's actual
normalization radius rather than requiring unit-ball normalization. -/
theorem ae_padic_stabilizer_bot_or_top {p : ℕ} [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (hT : MeasurePreserving T μ μ) (η : Z → Measure ℚ_[p]) (hη : Measurable η)
    (hreg : ∀ᵐ q ∂μ, (η q).Regular) {r : ℝ}
    (hnorm : ∀ᵐ q ∂μ, η q (ball 0 r) = 1)
    {a : ℚ_[p]} (ha : a ≠ 0) (ha1 : ‖a‖ < 1)
    (hcov : ∀ᵐ q ∂μ, ∃ d : ℝ≥0, η (T q) = d • (η q).map (a * ·)) :
    ∀ᵐ q ∂μ, translationStabilizer (η q) = ⊥ ∨ translationStabilizer (η q) = ⊤ := by
  obtain ⟨θ,hθ,heq,hθreg,hhit⟩ := exists_regular_hit_version η hη hreg
  letI : ∀ q, (θ q).Regular := hθreg
  have hc := stabilizer_covariance_of_ae_eq hT η θ heq hnorm (rootDilation a ha)
    (measurable_const.mul measurable_id) (measurable_const.mul measurable_id) hcov
  have hd := ae_padic_subgroup_bot_or_top hT (fun q => translationStabilizer (θ q)) hhit
    (ae_of_all _ fun q => isClosed_translationStabilizer (θ q)) ha ha1 hc
  filter_upwards [heq,hd] with q he hq
  simpa only [he] using hq

end VV.BBEKLeafStabilizerDichotomy

