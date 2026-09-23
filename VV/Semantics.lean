import VV.Definitions
import Mathlib.Data.ENat.Lattice

/-!
The connection between the actual continued-fraction recurrence, its
integer digit bounds, and the extended-natural limsup. No computational
certificate or unproved mathematical hypothesis is used in this module.
-/
namespace VV

theorem completeQuotient_irrational {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Irrational (completeQuotient x n) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    exact (ih.sub_intCast ⌊completeQuotient x n⌋).inv

theorem completeQuotient_fract_ne_zero {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Int.fract (completeQuotient x n) ≠ 0 := by
  have hi := (completeQuotient_irrational hx n).sub_intCast
    ⌊completeQuotient x n⌋
  exact hi.ne_zero

theorem one_lt_completeQuotient_succ {x : ℝ} (hx : Irrational x) (n : ℕ) :
    1 < completeQuotient x (n + 1) := by
  have hp : 0 < Int.fract (completeQuotient x n) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (completeQuotient_fract_ne_zero hx n))
  exact (one_lt_inv₀ hp).mpr (Int.fract_lt_one _)

theorem one_le_partialQuotient_succ {x : ℝ} (hx : Irrational x) (n : ℕ) :
    1 ≤ partialQuotient x (n + 1) := by
  apply Int.le_floor.mpr
  simpa only [Int.cast_one] using (one_lt_completeQuotient_succ hx n).le

theorem irrational_dyadic_mul {x : ℝ} (hx : Irrational x) (k : ℕ) :
    Irrational ((2 : ℝ) ^ k * x) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    hx.natCast_mul (pow_ne_zero k (show (2 : ℕ) ≠ 0 by decide))

/-- The nonnegative tail digit, with index zero corresponding to `a₁`. -/
noncomputable def tailDigit (x : ℝ) (n : ℕ) : ℕ :=
  (partialQuotient x (n + 1)).toNat

theorem tailDigit_le_iff (x : ℝ) (n C : ℕ) :
    tailDigit x n ≤ C ↔ partialQuotient x (n + 1) ≤ (C : ℤ) := by
  exact Int.toNat_le

/-- `B = inf_N sup_{n ≥ N} a_{n+1}`, including the value infinity. -/
noncomputable def B (x : ℝ) : ℕ∞ :=
  ⨅ N : ℕ, ⨆ n : ℕ, ⨆ (_ : N ≤ n), (tailDigit x n : ℕ∞)

theorem B_le_iff (x : ℝ) (C : ℕ) :
    B x ≤ (C : ℕ∞) ↔ EventualBound x C := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := ENat.exists_eq_iInf
      (fun N : ℕ => ⨆ n : ℕ, ⨆ (_ : N ≤ n), (tailDigit x n : ℕ∞))
    refine ⟨N, fun n hn => ?_⟩
    have hbound : (⨆ m : ℕ, ⨆ (_ : N ≤ m), (tailDigit x m : ℕ∞)) ≤ C := by
      rw [hN]
      exact h
    have htail : (tailDigit x n : ℕ∞) ≤ (C : ℕ∞) :=
      (le_iSup₂ (f := fun m (_ : N ≤ m) => (tailDigit x m : ℕ∞)) n hn).trans hbound
    exact (tailDigit_le_iff x n C).mp (by exact_mod_cast htail)
  · rintro ⟨N, hN⟩
    apply (iInf_le _ N).trans
    refine iSup_le fun n => iSup_le fun hn => ?_
    exact_mod_cast (tailDigit_le_iff x n C).mpr (hN n hn)

theorem B_atLeast_succ_iff (x : ℝ) (C : ℕ) :
    ((C + 1 : ℕ) : ℕ∞) ≤ B x ↔ DigitsFrequentlyAtLeast x (C + 1) := by
  rw [← not_eventualBound_iff, ← B_le_iff, not_le]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ENat.add_one_le_iff (show (C : ℕ∞) ≠ ⊤ by simp))

theorem problem5_limsup_iff :
    Problem5Statement ↔ ∀ x : ℝ, Irrational x →
      ∃ k : ℕ, (11 : ℕ∞) ≤ B ((2 : ℝ) ^ k * x) := by
  unfold Problem5Statement
  have h (y : ℝ) : (11 : ℕ∞) ≤ B y ↔ DigitsFrequentlyAtLeast y 11 :=
    B_atLeast_succ_iff y 10
  simp only [h]

theorem eleven_le_iff_not_le_ten (y : ℕ∞) : 11 ≤ y ↔ ¬ y ≤ 10 := by
  rw [not_le]
  exact ENat.add_one_le_iff (by simp : (10 : ℕ∞) ≠ ⊤)

theorem problem5_sup_limsup_iff :
    Problem5Statement ↔ ∀ x : ℝ, Irrational x →
      (11 : ℕ∞) ≤ ⨆ k : ℕ, B ((2 : ℝ) ^ k * x) := by
  rw [problem5_limsup_iff]
  simp only [eleven_le_iff_not_le_ten, iSup_le_iff, not_forall]

theorem bExceptional_iff_sup_finite (x : ℝ) :
    x ∈ BExceptional ↔ Irrational x ∧
      (⨆ k : ℕ, B ((2 : ℝ) ^ k * x)) < ⊤ := by
  change (Irrational x ∧ ∃ C : ℕ, BOrbitBound x C) ↔ _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨C, h⟩
    exact (iSup_le fun k => (B_le_iff _ C).mpr (h k)).trans_lt (ENat.coe_lt_top C)
  · intro h
    obtain ⟨C, hC⟩ := ENat.ne_top_iff_exists.mp h.ne
    refine ⟨C, ?_⟩
    intro k
    apply (B_le_iff ((2 : ℝ) ^ k * x) C).mp
    rw [hC]
    exact le_iSup (fun j : ℕ => B ((2 : ℝ) ^ j * x)) k

end VV
