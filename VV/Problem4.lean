import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Problem 4: verified finite-template consequences

This module supplies algebraic and counting lemmas. The full literal
Hurwitz transducer, corrected kernel allowing column merging, positive
cyclic normalization and actual template encoding are proved in the
`P4Kernel` through `P4Encoding` modules. No Problem 4 proof uses `sorry`.
-/

namespace VV.Problem4
open scoped BigOperators

/-- The explicit digit bound stated in the research conversation. Its validity
for continued-fraction words is not assumed or proved merely by this definition. -/
def digitBound (ℓ : ℕ) : ℕ := 4 + 4 ^ (ℓ + 1) * ℓ * ℓ.factorial

/-- Four digit types; three choices of a pair of successful directions; two
cyclic alignment positions. -/
abbrev Template (ℓ : ℕ) := (Fin ℓ → Fin 4) × Fin 3 × Fin ℓ × Fin ℓ

theorem card_template (ℓ : ℕ) :
    Fintype.card (Template ℓ) = 3 * ℓ ^ 2 * 4 ^ ℓ := by
  simp [Template, Fintype.card_fun]
  ring

/-- A finite-dimensional obstruction, valid without nonnegativity: two
permutations cannot simultaneously double/halve complementary coordinates
of a nonzero vector. -/
theorem doubling_halving_kernel {ι : Type*} [Fintype ι]
    (σ τ : Equiv.Perm ι) (branch : ι → Bool) (w : ι → ℝ)
    (hσ : ∀ i, w (σ i) = if branch i then 2 * w i else w i / 2)
    (hτ : ∀ i, w (τ i) = if branch i then w i / 2 else 2 * w i) :
    ∀ i, w i = 0 := by
  classical
  have hlocal (i : ι) : (w (σ i)) ^ 2 + (w (τ i)) ^ 2 = (17 / 4 : ℝ) * (w i) ^ 2 := by
    rw [hσ, hτ]
    cases branch i <;> norm_num <;> ring
  have hσsum : ∑ i, (w (σ i)) ^ 2 = ∑ i, (w i) ^ 2 := by
    exact Equiv.sum_comp σ (fun i => (w i) ^ 2)
  have hτsum : ∑ i, (w (τ i)) ^ 2 = ∑ i, (w i) ^ 2 := by
    exact Equiv.sum_comp τ (fun i => (w i) ^ 2)
  have hsum := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hlocal)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hσsum, hτsum] at hsum
  have hz : ∑ i, (w i) ^ 2 = 0 := by linarith
  intro i
  have hi : (w i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w j))).mp hz i (Finset.mem_univ i)
  nlinarith [sq_nonneg (w i)]

/-- The same homogeneous obstruction proves uniqueness in an affine system. -/
theorem affine_template_unique {ι : Type*} [Fintype ι]
    (σ τ : Equiv.Perm ι) (branch : ι → Bool) (r s u v : ι → ℝ)
    (huσ : ∀ i, u (σ i) = (if branch i then 2 * u i else u i / 2) + r i)
    (huτ : ∀ i, u (τ i) = (if branch i then u i / 2 else 2 * u i) + s i)
    (hvσ : ∀ i, v (σ i) = (if branch i then 2 * v i else v i / 2) + r i)
    (hvτ : ∀ i, v (τ i) = (if branch i then v i / 2 else 2 * v i) + s i) :
    u = v := by
  have hz := doubling_halving_kernel σ τ branch (fun i => u i - v i)
  have hσ (i : ι) : u (σ i) - v (σ i) =
      if branch i then 2 * (u i - v i) else (u i - v i) / 2 := by
    rw [huσ, hvσ]
    cases branch i <;> simp <;> ring
  have hτ (i : ι) : u (τ i) - v (τ i) =
      if branch i then (u i - v i) / 2 else 2 * (u i - v i) := by
    rw [huτ, hvτ]
    cases branch i <;> simp <;> ring
  funext i
  have := hz hσ hτ i
  linarith

/-- The counting step for an injective encoding of rooted minimal-period
classes. The actual encoding is constructed in `VV.P4Encoding`. -/
theorem class_count_le {ℓ : ℕ} (hℓ : 0 < ℓ) {Class : Type*} [Fintype Class]
    (encode : Class × Fin ℓ → Template ℓ) (hinj : Function.Injective encode) :
    Fintype.card Class ≤ 3 * ℓ * 4 ^ ℓ := by
  have h := Fintype.card_le_of_injective encode hinj
  rw [Fintype.card_prod, Fintype.card_fin, card_template] at h
  have hh : Fintype.card Class * ℓ ≤ (3 * ℓ * 4 ^ ℓ) * ℓ := by
    convert h using 1 <;> ring
  exact Nat.le_of_mul_le_mul_right hh hℓ

end VV.Problem4
