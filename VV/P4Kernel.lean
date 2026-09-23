import VV.Problem4
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max

/-!
# The actual two-branch linear obstruction

Two successful Hurwitz branches need not have complementary states at every
input: both can halve a digit. The correct hypothesis is that they never both
double it. This module proves the stronger obstruction under that hypothesis,
and permits several input variables to merge in zero cleanup.
-/

namespace VV.Problem4
open scoped BigOperators

noncomputable def scale (b : Bool) : ℝ := if b then 2 else 1/2

theorem no_positive_two_branch_permutations {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ τ : Equiv.Perm ι) (a b : ι → Bool) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hno : ∀ i, ¬(a i = true ∧ b i = true))
    (hσ : ∀ i, w (σ i) = scale (a i) * w i)
    (hτ : ∀ i, w (τ i) = scale (b i) * w i) : False := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  have ha : a i = false := by
    cases h : a i
    · rfl
    · have hs := hσ i
      have hm := hmax (σ i) (Finset.mem_univ _)
      simp [scale, h] at hs
      linarith [hw i]
  have hb : b i = false := by
    cases h : b i
    · rfl
    · have hs := hτ i
      have hm := hmax (τ i) (Finset.mem_univ _)
      simp [scale, h] at hs
      linarith [hw i]
  have hle (j : ι) : w (σ j) * w (τ j) ≤ (w j) ^ 2 := by
    rw [hσ, hτ]
    have hj := hno j
    cases ha : a j <;> cases hb : b j <;> simp [ha, hb] at hj <;>
      simp [scale] <;> nlinarith [sq_nonneg (w j)]
  have hstrict : w (σ i) * w (τ i) < (w i) ^ 2 := by
    rw [hσ, hτ, ha, hb]
    simp only [scale, Bool.false_eq_true, ↓reduceIte]
    nlinarith [sq_pos_of_pos (hw i)]
  have hp := Finset.prod_lt_prod
    (fun j (_ : j ∈ Finset.univ) => mul_pos (hw (σ j)) (hw (τ j)))
    (fun j (_ : j ∈ Finset.univ) => hle j)
    ⟨i, Finset.mem_univ i, hstrict⟩
  have heq : (∏ j, w (σ j) * w (τ j)) = ∏ j, (w j) ^ 2 := by
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ w, Equiv.prod_comp τ w]
    simp only [pow_two, Finset.prod_mul_distrib]
  exact (ne_of_lt hp) heq

/-- Push every input contribution into one output coordinate. Zero cleanup can
merge contributions, so `f` is deliberately not assumed injective. -/
noncomputable def push {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ι) (c w : ι → ℝ) (j : ι) : ℝ :=
  ∑ i, if f i = j then c i * w i else 0

/-- A fixed vector forces a permutation on its nonzero support, even when the
ambient source-to-output map allows collisions and cancellation. -/
theorem support_permutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ι) (c w : ι → ℝ) (hfix : ∀ j, w j = push f c w j) :
    ∃ e : Equiv.Perm {i : ι // w i ≠ 0},
      ∀ i, (e i).val = f i.val ∧ w (e i).val = c i.val * w i.val := by
  classical
  let S := {i : ι // w i ≠ 0}
  have hpre (j : S) : ∃ i : S, f i.val = j.val := by
    have hn : push f c w j.val ≠ 0 := by rw [← hfix]; exact j.property
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    by_cases hf : f i = j.val
    · simp only [hf, ↓reduceIte] at hi
      exact ⟨⟨i, (mul_ne_zero_iff.mp hi).2⟩, hf⟩
    · simp [hf] at hi
  let g : S → S := fun j => Classical.choose (hpre j)
  have hg (j : S) : f (g j).val = j.val := Classical.choose_spec (hpre j)
  have hginj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    simpa only [hg] using congrArg (fun k : S => f k.val) hij
  have hgsurj : Function.Surjective g := Finite.surjective_of_injective hginj
  have hclosed (i : S) : w (f i.val) ≠ 0 := by
    obtain ⟨j, rfl⟩ := hgsurj i
    rw [hg]
    exact j.property
  let fs : S → S := fun i => ⟨f i.val, hclosed i⟩
  have hfsurj : Function.Surjective fs := by
    intro j
    exact ⟨g j, Subtype.ext (hg j)⟩
  have hfinj : Function.Injective fs := Finite.injective_iff_surjective.mpr hfsurj
  let e : Equiv.Perm S := Equiv.ofBijective fs ⟨hfinj, hfsurj⟩
  refine ⟨e, fun i => ⟨rfl, ?_⟩⟩
  change w (f i.val) = c i.val * w i.val
  rw [hfix]
  unfold push
  rw [Finset.sum_eq_single i.val]
  · simp
  · intro j hj hji
    by_cases hwj : w j = 0
    · simp [hwj]
    · by_cases hfj : f j = f i.val
      · have heq : fs ⟨j, hwj⟩ = fs i := Subtype.ext hfj
        have hjieq : j = i.val := congrArg Subtype.val (hfinj heq)
        exact False.elim (hji hjieq)
      · simp [hfj]
  · simp

theorem two_branch_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ι) (a b : ι → Bool) (w : ι → ℝ)
    (hno : ∀ i, ¬(a i = true ∧ b i = true))
    (hf : ∀ j, w j = push f (fun i => scale (a i)) w j)
    (hg : ∀ j, w j = push g (fun i => scale (b i)) w j) : ∀ i, w i = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := support_permutation f (fun i => scale (a i)) w hf
  obtain ⟨τ, hτ⟩ := support_permutation g (fun i => scale (b i)) w hg
  intro i
  by_contra hwi
  letI : Nonempty {i : ι // w i ≠ 0} := ⟨⟨i, hwi⟩⟩
  apply no_positive_two_branch_permutations σ τ
    (fun i => a i.val) (fun i => b i.val) (fun i => |w i.val|)
    (fun i => abs_pos.mpr i.property) (fun i => hno i.val)
  · intro i
    rw [(hσ i).2, abs_mul]
    have hp : 0 ≤ scale (a i.val) := by cases a i.val <;> norm_num [scale]
    rw [abs_of_nonneg hp]
  · intro i
    rw [(hτ i).2, abs_mul]
    have hp : 0 ≤ scale (b i.val) := by cases b i.val <;> norm_num [scale]
    rw [abs_of_nonneg hp]

end VV.Problem4
