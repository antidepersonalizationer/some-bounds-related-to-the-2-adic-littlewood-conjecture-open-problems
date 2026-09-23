import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# The real-number statements in Vitorino--Vukusic

The zeroth complete quotient is the input. Subsequent complete quotients are
obtained by taking the reciprocal of the fractional part. Only the digits
with index at least one enter the bounds, so the integer part is excluded.
For irrational inputs this recursion never terminates.

`EventualBound x C` is the discrete, finite-bound formulation of `B(x) ≤ C`.
`DigitsFrequentlyAtLeast x C` means that digits at least `C` occur arbitrarily
far out. This avoids a convention for the limsup of the auxiliary sequence
on rational inputs; all target statements explicitly require irrationality.
-/

namespace VV

noncomputable def completeQuotient (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => (Int.fract (completeQuotient x n))⁻¹

noncomputable def partialQuotient (x : ℝ) (n : ℕ) : ℤ :=
  ⌊completeQuotient x n⌋

def EventualBound (x : ℝ) (C : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → partialQuotient x (n + 1) ≤ (C : ℤ)

def DigitsFrequentlyAtLeast (x : ℝ) (C : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (C : ℤ) ≤ partialQuotient x (n + 1)

def BOrbitBound (x : ℝ) (C : ℕ) : Prop :=
  ∀ k : ℕ, EventualBound ((2 : ℝ) ^ k * x) C

def BExceptional : Set ℝ :=
  {x | Irrational x ∧ ∃ C : ℕ, BOrbitBound x C}

def Problem5Statement : Prop :=
  ∀ x : ℝ, Irrational x →
    ∃ k : ℕ, DigitsFrequentlyAtLeast ((2 : ℝ) ^ k * x) 11

theorem not_eventualBound_iff (x : ℝ) (C : ℕ) :
    ¬ EventualBound x C ↔ DigitsFrequentlyAtLeast x (C + 1) := by
  classical
  simp only [EventualBound, DigitsFrequentlyAtLeast, not_exists, not_forall,
    not_le, exists_prop, Nat.cast_add, Nat.cast_one]
  constructor
  · intro h N
    obtain ⟨n, hn, hd⟩ := h N
    exact ⟨n, hn, by omega⟩
  · intro h N
    obtain ⟨n, hn, hd⟩ := h N
    exact ⟨n, hn, by omega⟩

theorem problem5_iff_no_bound_ten :
    Problem5Statement ↔ ∀ x : ℝ, Irrational x → ¬ BOrbitBound x 10 := by
  classical
  simp only [Problem5Statement, BOrbitBound, not_forall,
    not_eventualBound_iff]

theorem eventualBound_mono {x : ℝ} {C D : ℕ}
    (h : EventualBound x C) (hCD : C ≤ D) : EventualBound x D := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => (hN n hn).trans (Int.ofNat_le.mpr hCD)⟩

theorem bOrbitBound_shift {x : ℝ} {C : ℕ} (h : BOrbitBound x C) (j : ℕ) :
    BOrbitBound ((2 : ℝ) ^ j * x) C := by
  intro k
  simpa only [pow_add, mul_assoc] using h (k + j)

end VV
