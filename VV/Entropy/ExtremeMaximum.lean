import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Topology.Semicontinuous

/-! An upper semicontinuous affine functional on a compact set attains
its maximum at an extreme point. The proof uses closed upper level sets,
so no continuity or ergodic decomposition is silently assumed. -/

noncomputable section
open Set

namespace ErgodicTheory.Entropy

variable {E : Type*} [TopologicalSpace E] {C : Set E} {f : E → ℝ}

theorem exists_max_of_compact_upper_levels (hC : IsCompact C) (hne : C.Nonempty)
    (hclosed : ∀ r : ℝ, IsClosed {x | x ∈ C ∧ r ≤ f x}) :
    ∃ x ∈ C, ∀ y ∈ C, f y ≤ f x := by
  classical
  let U : C → Set E := fun y => {x | x ∈ C ∧ f y ≤ f x}
  have hfinite : ∀ s : Finset C, (C ∩ ⋂ y ∈ s, U y).Nonempty := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hne
    | @insert y s hy ih =>
      obtain ⟨x,hxC,hxs⟩ := ih
      by_cases hxy : f y ≤ f x
      · refine ⟨x,hxC,?_⟩
        simp only [Finset.mem_insert, mem_iInter] at hxs ⊢
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨hxC,hxy⟩
        · exact hxs z hz
      · refine ⟨y,y.property,?_⟩
        simp only [Finset.mem_insert,mem_iInter] at hxs ⊢
        intro z hz
        refine ⟨y.property,?_⟩
        rcases hz with rfl | hz
        · exact le_rfl
        · exact (hxs z hz).2.trans (le_of_not_ge hxy)
  obtain ⟨x,hxC,hx⟩ := hC.inter_iInter_nonempty U
    (fun y => hclosed (f y)) hfinite
  exact ⟨x,hxC,fun y hy => (mem_iInter.mp hx ⟨y,hy⟩).2⟩

variable [AddCommGroup E] [Module ℝ E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

theorem exists_extreme_max_of_compact_upper_levels
    (hC : IsCompact C) (hne : C.Nonempty)
    (hclosed : ∀ r : ℝ, IsClosed {x | x ∈ C ∧ r ≤ f x})
    (haff : ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      a • x + b • y ∈ C →
      f (a • x + b • y) = a * f x + b * f y) :
    ∃ x ∈ extremePoints ℝ C, ∀ y ∈ C, f y ≤ f x := by
  obtain ⟨x,hxC,hmax⟩ := exists_max_of_compact_upper_levels hC hne hclosed
  let M : Set E := {y | y ∈ C ∧ f x ≤ f y}
  have hMC : M ⊆ C := fun _ hy => hy.1
  have hM : IsCompact M := hC.of_isClosed_subset (hclosed (f x)) hMC
  have hface : IsExtreme ℝ C M := by
    refine ⟨hMC,?_⟩
    rintro u hu v hv z hz ⟨a,b,ha,hb,hab,rfl⟩
    have heq := haff u hu v hv a b ha hb hab hz.1
    have hu' := hmax u hu
    have hv' := hmax v hv
    have hz' : f x ≤ a * f u + b * f v := heq ▸ hz.2
    have hid : a * f x + b * f x = f x := by rw [← add_mul,hab,one_mul]
    refine ⟨⟨hu,?_⟩,⟨hv,?_⟩⟩
    · by_contra hh
      have hp := mul_pos ha (sub_pos.mpr (lt_of_not_ge hh))
      have hn := mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hv')
      nlinarith
    · by_contra hh
      have hp := mul_pos hb (sub_pos.mpr (lt_of_not_ge hh))
      have hn := mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hu')
      nlinarith
  obtain ⟨z,hz⟩ := hM.extremePoints_nonempty ⟨x,hxC,le_rfl⟩
  exact ⟨z,hface.extremePoints_subset_extremePoints hz,
    fun y hy => (hmax y hy).trans hz.1.2⟩

/-- A compact parametrization is enough; its inverse need not be extended
continuously off the compact image. -/
theorem exists_extreme_max_of_compact_param
    {P : Type*} [TopologicalSpace P] [CompactSpace P] [Nonempty P]
    (σ : P → E) (hσ : Continuous σ) (hσinj : Function.Injective σ)
    (h : P → ℝ) (hclosed : ∀ r : ℝ, IsClosed {x | r ≤ h x})
    (haff : ∀ x y z : P, ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      σ z = a • σ x + b • σ y → h z = a * h x + b * h y) :
    ∃ x : P, σ x ∈ extremePoints ℝ (range σ) ∧ ∀ y : P, h y ≤ h x := by
  classical
  let f : E → ℝ := fun z => h (Function.invFun σ z)
  have hval (x : P) : f (σ x) = h x := by
    exact congrArg h (Function.leftInverse_invFun hσinj x)
  have hlevels (r : ℝ) : {x | x ∈ range σ ∧ r ≤ f x} = σ '' {x | r ≤ h x} := by
    ext z
    constructor
    · rintro ⟨⟨x,rfl⟩,hx⟩
      exact ⟨x,by rwa [hval] at hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨mem_range_self x,by rwa [hval]⟩
  obtain ⟨z,hz,hmax⟩ := exists_extreme_max_of_compact_upper_levels
    (isCompact_range hσ) (range_nonempty σ)
    (fun r => by rw [hlevels]; exact ((hclosed r).isCompact.image hσ).isClosed)
    (fun u hu v hv a b ha hb hab hz => by
      obtain ⟨x,rfl⟩ := hu
      obtain ⟨y,rfl⟩ := hv
      obtain ⟨z,hz⟩ := hz
      rw [← hz,hval,hval,hval]
      exact haff x y z a b ha hb hab hz)
  obtain ⟨x,rfl⟩ := hz.1
  exact ⟨x,hz,fun y => by simpa only [hval] using hmax (σ y) (mem_range_self y)⟩

end ErgodicTheory.Entropy
