import VV.BBEKStabilizerRecurrence
import Mathlib.Data.Real.Pointwise

/-! A recurrent measurable field of closed real root subgroups cannot have
discrete nonzero fibres under a strict diagonal contraction.  Measurability
is expressed by the usual hit-open-set condition on closed-set fields. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise NNReal ENNReal

namespace VV.BBEKLeafwiseStabilizer

def realPositiveElements (S : AddSubgroup ℝ) : Set ℝ := {u | u ∈ S ∧ 0 < u}

def realPeriod (S : AddSubgroup ℝ) : ℝ := sInf (realPositiveElements S)

theorem realPositiveElements_bddBelow (S : AddSubgroup ℝ) :
    BddBelow (realPositiveElements S) := ⟨0,fun _ hu => hu.2.le⟩

theorem realPositiveElements_nonempty (S : AddSubgroup ℝ) (hS : S ≠ ⊥) :
    (realPositiveElements S).Nonempty := by
  obtain ⟨u,hu,hupos⟩ := real_subgroup_pos_of_ne_bot S hS
  exact ⟨u,hu,hupos⟩

@[simp] theorem realPeriod_bot : realPeriod (⊥ : AddSubgroup ℝ) = 0 := by
  have h : realPositiveElements (⊥ : AddSubgroup ℝ) = ∅ := by
    ext u
    simp only [realPositiveElements,mem_setOf_eq,AddSubgroup.mem_bot,mem_empty_iff_false,
      iff_false,not_and]
    rintro rfl
    exact lt_irrefl 0
  rw [realPeriod,h,Real.sInf_empty]

theorem realPeriod_nonneg (S : AddSubgroup ℝ) : 0 ≤ realPeriod S := by
  by_cases hS : S = ⊥
  · simp [hS]
  · exact le_csInf (realPositiveElements_nonempty S hS) (fun _ hu => hu.2.le)

theorem realPeriod_zero_iff_of_isClosed (S : AddSubgroup ℝ)
    (hclosed : IsClosed (S : Set ℝ)) : realPeriod S = 0 ↔ S = ⊥ ∨ S = ⊤ := by
  constructor
  · intro hp
    by_cases hS : S = ⊥
    · exact Or.inl hS
    right
    have hdense : Dense (S : Set ℝ) := S.dense_of_not_isolated_zero (by
      intro ε hε
      obtain ⟨u,hu,huε⟩ := (csInf_lt_iff (realPositiveElements_bddBelow S)
        (realPositiveElements_nonempty S hS)).mp (by
          change realPeriod S < ε
          simpa only [hp] using hε)
      exact ⟨u,hu.1,hu.2,huε⟩)
    exact SetLike.coe_injective (hclosed.closure_eq ▸ hdense.closure_eq)
  · rintro (rfl | rfl)
    · exact realPeriod_bot
    apply le_antisymm _ (realPeriod_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [zero_add] using
      (csInf_le (realPositiveElements_bddBelow ⊤) (show ε ∈ realPositiveElements ⊤ from ⟨by trivial,hε⟩))

theorem realPositiveElements_map {a : ℝ} (ha : 0 < a) (S : AddSubgroup ℝ) :
    realPositiveElements (S.map (rootDilation a ha.ne').toAddMonoidHom) =
      a • realPositiveElements S := by
  ext y
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hpos⟩
    exact ⟨x,⟨hx,(mul_pos_iff_of_pos_left ha).mp hpos⟩,rfl⟩
  · rintro ⟨x,⟨hx,hpos⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,mul_pos ha hpos⟩

theorem realPeriod_map {a : ℝ} (ha : 0 < a) (S : AddSubgroup ℝ) :
    realPeriod (S.map (rootDilation a ha.ne').toAddMonoidHom) = a * realPeriod S := by
  rw [realPeriod,realPositiveElements_map ha,Real.sInf_smul_of_nonneg ha.le]
  rfl

/-- Hit-open measurability is the standard measurable closed-set-field
condition.  The period is constructed from the actual subgroup, and its
measurability is proved rather than postulated. -/
theorem measurable_realPeriod {X : Type*} [MeasurableSpace X]
    (S : X → AddSubgroup ℝ)
    (hhit : ∀ O : Set ℝ, IsOpen O → MeasurableSet {x | ∃ u ∈ S x, u ∈ O}) :
    Measurable (fun x => realPeriod (S x)) := by
  classical
  have hbot : MeasurableSet {x | S x = ⊥} := by
    have he : {x | S x = ⊥} = {x | ∃ u ∈ S x, u ∈ Ioi (0 : ℝ)}ᶜ := by
      ext x
      simp only [mem_setOf_eq,mem_compl_iff,mem_Ioi,not_exists,not_and]
      constructor
      · intro hx u hu
        rw [hx] at hu
        simp only [AddSubgroup.mem_bot] at hu
        simp [hu]
      · intro h
        by_contra hn
        obtain ⟨u,hu,hupos⟩ := real_subgroup_pos_of_ne_bot (S x) hn
        exact h u hu hupos
    rw [he]
    exact (hhit _ isOpen_Ioi).compl
  apply measurable_of_Iio
  intro r
  by_cases hr : 0 < r
  · have he : (fun x => realPeriod (S x)) ⁻¹' Iio r =
        {x | S x = ⊥} ∪ {x | ∃ u ∈ S x, u ∈ Ioo 0 r} := by
      ext x
      simp only [mem_preimage,mem_Iio,mem_union,mem_setOf_eq,mem_Ioo]
      by_cases hS : S x = ⊥
      · simp [hS,hr]
      · rw [or_iff_right hS]
        exact (csInf_lt_iff (realPositiveElements_bddBelow (S x))
          (realPositiveElements_nonempty (S x) hS)).trans (by
            simp only [realPositiveElements,mem_setOf_eq,and_assoc,exists_prop])
    rw [he]
    exact hbot.union (hhit _ isOpen_Ioo)
  · have he : (fun x => realPeriod (S x)) ⁻¹' Iio r = ∅ := by
      ext x
      simp only [mem_preimage,mem_Iio,mem_empty_iff_false,iff_false,not_lt]
      exact (le_of_not_gt hr).trans (realPeriod_nonneg _)
    rw [he]
    exact MeasurableSet.empty

/-- Actual Poincaré recurrence forces an equivariant measurable field of
closed subgroups of R to consist almost surely of only 0 and R.  In
particular diagonal normalization at a fixed point is not assumed. -/
theorem ae_real_subgroup_bot_or_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (S : X → AddSubgroup ℝ)
    (hhit : ∀ O : Set ℝ, IsOpen O → MeasurableSet {x | ∃ u ∈ S x, u ∈ O})
    (hclosed : ∀ᵐ x ∂μ, IsClosed (S x : Set ℝ))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hcov : ∀ᵐ x ∂μ, S (T x) = (S x).map (rootDilation a ha.ne').toAddMonoidHom) :
    ∀ᵐ x ∂μ, S x = ⊥ ∨ S x = ⊤ := by
  have hp : ∀ᵐ x ∂μ, realPeriod (S (T x)) = a * realPeriod (S x) := by
    filter_upwards [hcov] with x hx
    rw [hx,realPeriod_map ha]
  have hz := ae_eq_zero_of_scalar_covariance hT (measurable_realPeriod S hhit)
    ha.ne' (by simpa only [Real.norm_eq_abs,abs_of_pos ha] using ha1) hp
  filter_upwards [hz,hclosed] with x hx hc
  exact (realPeriod_zero_iff_of_isClosed (S x) hc).mp hx

/-- Specialization to the exact stabilizers of an actual normalized family
of real leaf measures.  Positive projective normalization factors are
deduced from the unit-ball normalization at Tx. -/
theorem ae_real_translationStabilizer_bot_or_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (η : X → Measure ℝ)
    (hhit : ∀ O : Set ℝ, IsOpen O →
      MeasurableSet {x | ∃ u ∈ translationStabilizer (η x), u ∈ O})
    (hregular : ∀ᵐ x ∂μ, (η x).OuterRegular)
    (hnorm : ∀ᵐ x ∂μ, η x (Metric.ball (0 : ℝ) 1) = 1)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0, η (T x) = d • Measure.map (a * ·) (η x)) :
    ∀ᵐ x ∂μ, translationStabilizer (η x) = ⊥ ∨ translationStabilizer (η x) = ⊤ := by
  refine ae_real_subgroup_bot_or_top hT (fun x => translationStabilizer (η x)) hhit
    ?_ ha ha1 ?_
  · filter_upwards [hregular] with x hx
    letI := hx
    exact isClosed_translationStabilizer (η x)
  · filter_upwards [hcov,hT.quasiMeasurePreserving.ae hnorm] with x hx hn
    obtain ⟨d,hd⟩ := hx
    have hd0 : d ≠ 0 := by
      intro hz
      simp only [hz,zero_smul] at hd
      simp only [hd,Measure.coe_zero,Pi.zero_apply] at hn
      exact zero_ne_one hn
    rw [hd]
    exact translationStabilizer_projective_map (rootDilation a ha.ne')
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id) (η x) hd0

/-- The projective stabilizer is also either trivial or the full real root
group.  The multiplier-one recurrence theorem is applied before the
closed-subgroup-field recurrence theorem. -/
theorem ae_real_projectiveTranslationStabilizer_bot_or_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (η : X → Measure ℝ)
    (hhit : ∀ O : Set ℝ, IsOpen O →
      MeasurableSet {x | ∃ u ∈ translationStabilizer (η x), u ∈ O})
    (hregular : ∀ᵐ x ∂μ, (η x).OuterRegular)
    (hmass : Measurable (fun x => η x (Metric.ball (0 : ℝ) 2)))
    (hnorm : ∀ᵐ x ∂μ, η x (Metric.ball (0 : ℝ) 1) = 1)
    (hfinite : ∀ᵐ x ∂μ, η x (Metric.ball (0 : ℝ) 2) ≠ ⊤)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0, η (T x) = d • Measure.map (a * ·) (η x)) :
    ∀ᵐ x ∂μ, projectiveTranslationStabilizer (η x) = ⊥ ∨
      projectiveTranslationStabilizer (η x) = ⊤ := by
  have heq := ae_projectiveTranslationStabilizer_eq hT η hmass hnorm hfinite
    (rootDilation a ha.ne') (measurable_const.mul measurable_id)
    (rootDilation_contracts ha.ne' (by simpa [Real.norm_eq_abs,abs_of_pos ha] using ha1)) hcov
  filter_upwards [heq,ae_real_translationStabilizer_bot_or_top hT η hhit hregular hnorm ha ha1 hcov]
    with x hx hc
  simpa only [hx] using hc

end VV.BBEKLeafwiseStabilizer
