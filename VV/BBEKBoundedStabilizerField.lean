import VV.BBEKStabilizerRecurrence
import Mathlib.Data.Real.Pointwise

/-! Measurable contracting fields of additive subgroups cannot have a
nonzero bounded fibre.  The size is the actual supremum of the subgroup's
norms, with the real conditional supremum's default zero when unbounded. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise NNReal ENNReal

namespace VV.BBEKLeafwiseStabilizer

variable {F : Type*} [NormedField F]

def subgroupNorms (S : AddSubgroup F) : Set ℝ := norm '' (S : Set F)

def subgroupSize (S : AddSubgroup F) : ℝ := sSup (subgroupNorms S)

theorem zero_mem_subgroupNorms (S : AddSubgroup F) : 0 ∈ subgroupNorms S :=
  ⟨0,S.zero_mem,norm_zero⟩

theorem subgroupSize_nonneg (S : AddSubgroup F) : 0 ≤ subgroupSize S := by
  by_cases hb : BddAbove (subgroupNorms S)
  · exact le_csSup hb (zero_mem_subgroupNorms S)
  · simp only [subgroupSize,Real.sSup_of_not_bddAbove hb,le_refl]

theorem subgroupSize_zero_iff (S : AddSubgroup F) :
    subgroupSize S = 0 ↔ S = ⊥ ∨ ¬ BddAbove (subgroupNorms S) := by
  constructor
  · intro hz
    by_cases hb : BddAbove (subgroupNorms S)
    · left
      apply bot_unique
      intro u hu
      change u = 0
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg u)
      exact (le_csSup hb (show ‖u‖ ∈ subgroupNorms S from ⟨u,hu,rfl⟩)).trans hz.le
    · exact Or.inr hb
  · rintro (rfl | hb)
    · have he : subgroupNorms (⊥ : AddSubgroup F) = {0} := by
        ext r
        simp [subgroupNorms]
      simp [subgroupSize,he]
    · exact Real.sSup_of_not_bddAbove hb

theorem subgroupNorms_map {a : F} (ha : a ≠ 0) (S : AddSubgroup F) :
    subgroupNorms (S.map (rootDilation a ha).toAddMonoidHom) = ‖a‖ • subgroupNorms S := by
  ext r
  constructor
  · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨‖u‖,⟨u,hu,rfl⟩,(norm_mul a u).symm⟩
  · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨a*u,⟨u,hu,rfl⟩,norm_mul a u⟩

theorem subgroupSize_map {a : F} (ha : a ≠ 0) (S : AddSubgroup F) :
    subgroupSize (S.map (rootDilation a ha).toAddMonoidHom) = ‖a‖ * subgroupSize S := by
  rw [subgroupSize,subgroupNorms_map ha,Real.sSup_smul_of_nonneg (norm_nonneg a)]
  rfl

theorem measurable_subgroupSize {X : Type*} [MeasurableSpace X]
    (S : X → AddSubgroup F)
    (hhit : ∀ O : Set F, IsOpen O → MeasurableSet {x | ∃ u ∈ S x, u ∈ O}) :
    Measurable (fun x => subgroupSize (S x)) := by
  classical
  have hnorm (r : ℝ) : MeasurableSet {x | ∃ u ∈ S x, r < ‖u‖} :=
    hhit _ (isOpen_lt continuous_const continuous_norm)
  have hbound : MeasurableSet {x | BddAbove (subgroupNorms (S x))} := by
    have he : {x | BddAbove (subgroupNorms (S x))} =
        ⋃ N : ℕ, {x | ∃ u ∈ S x, (N : ℝ) < ‖u‖}ᶜ := by
      ext x
      simp only [mem_setOf_eq,mem_iUnion,mem_compl_iff,not_exists,not_and,not_lt]
      constructor
      · rintro ⟨r,hr⟩
        obtain ⟨N,hN⟩ := exists_nat_ge r
        exact ⟨N,fun u hu => (hr ⟨u,hu,rfl⟩).trans hN⟩
      · rintro ⟨N,hN⟩
        exact ⟨N,fun r ⟨u,hu,he⟩ => he ▸ hN u hu⟩
    rw [he]
    exact MeasurableSet.iUnion fun N => (hnorm N).compl
  apply measurable_of_Ioi
  intro r
  by_cases hr : r < 0
  · have he : (fun x => subgroupSize (S x)) ⁻¹' Ioi r = univ := by
      ext x
      simp only [mem_preimage,mem_Ioi,mem_univ,iff_true]
      exact hr.trans_le (subgroupSize_nonneg _)
    rw [he]
    exact MeasurableSet.univ
  · have he : (fun x => subgroupSize (S x)) ⁻¹' Ioi r =
        {x | BddAbove (subgroupNorms (S x))} ∩ {x | ∃ u ∈ S x, r < ‖u‖} := by
      ext x
      simp only [mem_preimage,mem_Ioi,mem_inter_iff,mem_setOf_eq]
      by_cases hb : BddAbove (subgroupNorms (S x))
      · simp only [hb,true_and,subgroupSize]
        rw [lt_csSup_iff hb ⟨0,zero_mem_subgroupNorms _⟩]
        simp only [subgroupNorms,mem_image,exists_exists_and_eq_and]
        rfl
      · simp only [hb,false_and,subgroupSize,Real.sSup_of_not_bddAbove hb,hr]
    rw [he]
    exact hbound.inter (hnorm r)

/-- Every nonzero fibre is unbounded almost surely.  The proof derives
recurrence from finite measure preservation and excludes a measurable
positive finite scale, rather than assuming stabilizers at x and Tx agree. -/
theorem ae_subgroup_bot_or_unbounded
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (S : X → AddSubgroup F)
    (hhit : ∀ O : Set F, IsOpen O → MeasurableSet {x | ∃ u ∈ S x, u ∈ O})
    {a : F} (ha : a ≠ 0) (ha1 : ‖a‖ < 1)
    (hcov : ∀ᵐ x ∂μ, S (T x) = (S x).map (rootDilation a ha).toAddMonoidHom) :
    ∀ᵐ x ∂μ, S x = ⊥ ∨ ¬ BddAbove (subgroupNorms (S x)) := by
  have hp : ∀ᵐ x ∂μ, subgroupSize (S (T x)) = ‖a‖ * subgroupSize (S x) := by
    filter_upwards [hcov] with x hx
    rw [hx,subgroupSize_map ha]
  have hz := ae_eq_zero_of_scalar_covariance hT (measurable_subgroupSize S hhit)
    (norm_ne_zero_iff.mpr ha) (by simpa only [Real.norm_eq_abs,abs_norm] using ha1) hp
  exact hz.mono fun x hx => (subgroupSize_zero_iff (S x)).mp hx

theorem ae_translationStabilizer_bot_or_unbounded
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (η : X → Measure F)
    (hhit : ∀ O : Set F, IsOpen O →
      MeasurableSet {x | ∃ u ∈ translationStabilizer (η x), u ∈ O})
    (hnorm : ∀ᵐ x ∂μ, η x (Metric.ball (0 : F) 1) = 1)
    {a : F} (ha : a ≠ 0) (ha1 : ‖a‖ < 1)
    (hcov : ∀ᵐ x ∂μ, ∃ d : ℝ≥0, η (T x) = d • Measure.map (a * ·) (η x)) :
    ∀ᵐ x ∂μ, translationStabilizer (η x) = ⊥ ∨
      ¬ BddAbove (subgroupNorms (translationStabilizer (η x))) := by
  apply ae_subgroup_bot_or_unbounded hT (fun x => translationStabilizer (η x)) hhit ha ha1
  filter_upwards [hcov,hT.quasiMeasurePreserving.ae hnorm] with x hx hn
  obtain ⟨d,hd⟩ := hx
  have hd0 : d ≠ 0 := by
    intro hz
    simp only [hz,zero_smul] at hd
    simp only [hd,Measure.coe_zero,Pi.zero_apply] at hn
    exact zero_ne_one hn
  rw [hd]
  exact translationStabilizer_projective_map (rootDilation a ha)
    (measurable_const.mul measurable_id) (measurable_const.mul measurable_id) (η x) hd0

end VV.BBEKLeafwiseStabilizer
