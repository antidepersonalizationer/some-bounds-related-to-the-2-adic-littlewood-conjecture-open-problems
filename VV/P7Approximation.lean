import VV.P5Period
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

/-! Exact approximation formulas for actual continued fractions. -/

namespace VV.P7Approximation
open P5Period

theorem matrix_det (w : List ℤ) :
    (matrix w).a * (matrix w).d - (matrix w).b * (matrix w).c = (-1 : ℤ) ^ w.length := by
  induction w with
  | nil => norm_num [matrix, identity]
  | cons a w ih =>
    simp only [matrix, prepend, List.length_cons, pow_succ]
    linear_combination -ih

theorem matrix_entries_compare (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a) :
    (matrix w).b ≤ (matrix w).a ∧
      (w ≠ [] → (matrix w).d ≤ (matrix w).c) := by
  induction w with
  | nil => simp [matrix, identity]
  | cons a w ih =>
    have ha := hw a (by simp)
    obtain ⟨hab, hcd⟩ := ih (fun b hb => hw b (by simp [hb]))
    dsimp [matrix, prepend]
    refine ⟨?_, fun _ => hab⟩
    cases w with
    | nil => simpa [matrix, identity] using ha
    | cons b w =>
      have hd := hcd (by simp)
      nlinarith

theorem digitBlock_completeQuotient (x : ℝ) (m n p : ℕ) :
    digitBlock (completeQuotient x m) n p = digitBlock x (m + n) p := by
  induction p generalizing n with
  | zero => rfl
  | succ p ih =>
    simp only [digitBlock, partialQuotient, completeQuotient_add, ih, Nat.add_assoc]

/-- The standard mathlib rational convergent equals the quotient of two
integer entries in the actual digit-prefix matrix. -/
theorem convergent_eq_matrix {x : ℝ} (hx : Irrational x) (n : ℕ) :
    x.convergent n =
      ((matrix (digitBlock x 0 (n + 1))).a : ℚ) /
        ((matrix (digitBlock x 0 (n + 1))).c : ℚ) := by
  induction n generalizing x with
  | zero => simp [Real.convergent, digitBlock, matrix, prepend, identity, partialQuotient,
      completeQuotient]
  | succ n ih =>
    have ht := ih (completeQuotient_irrational hx 1)
    rw [digitBlock_completeQuotient] at ht
    simp only [Nat.add_zero] at ht
    rw [Real.convergent_succ]
    change (⌊x⌋ : ℚ) + (Real.convergent (completeQuotient x 1) n)⁻¹ = _
    rw [ht]
    let M := matrix (digitBlock x 1 (n + 1))
    have hA : (0 : ℚ) < M.a := by
      have h := (matrix_positive _ (digitBlock_positive hx 1 (n + 1) (by omega))).1
      have hi : (0 : ℤ) < M.a := lt_of_lt_of_le (by decide : (0 : ℤ) < 1) h
      exact_mod_cast hi
    change (⌊x⌋ : ℚ) + ((M.a : ℚ) / M.c)⁻¹ =
      ((partialQuotient x 0 * M.a + M.c : ℤ) : ℚ) / M.a
    rw [inv_div]
    simp only [partialQuotient, completeQuotient]
    push_cast
    field_simp

theorem prefix_den_positive {x : ℝ} (hx : Irrational x) (n : ℕ) :
    0 < (matrix (digitBlock x 0 (n + 1))).c := by
  change 0 < (matrix (digitBlock x 1 n)).a
  exact lt_of_lt_of_le (by decide : (0 : ℤ) < 1)
    (matrix_positive _ (digitBlock_positive hx 1 n (by omega))).1

theorem prefix_previous_den_bounds {x : ℝ} (hx : Irrational x) (n : ℕ) :
    0 ≤ (matrix (digitBlock x 0 (n + 1))).d ∧
      (matrix (digitBlock x 0 (n + 1))).d ≤
        (matrix (digitBlock x 0 (n + 1))).c := by
  change 0 ≤ (matrix (digitBlock x 1 n)).b ∧
    (matrix (digitBlock x 1 n)).b ≤ (matrix (digitBlock x 1 n)).a
  exact ⟨(matrix_positive _ (digitBlock_positive hx 1 n (by omega))).2.1,
    (matrix_entries_compare _ (digitBlock_positive hx 1 n (by omega))).1⟩

theorem matrix_first_column_coprime (w : List ℤ) :
    (matrix w).a.natAbs.Coprime (matrix w).c.natAbs := by
  have h := matrix_det w
  have hp : IsCoprime (matrix w).a (matrix w).c := by
    rcases neg_one_pow_eq_or ℤ w.length with he | he
    · refine ⟨(matrix w).d, -(matrix w).b, ?_⟩
      rw [he] at h
      linear_combination h
    · refine ⟨-(matrix w).d, (matrix w).b, ?_⟩
      rw [he] at h
      linear_combination -h
  exact Int.isCoprime_iff_gcd_eq_one.mp hp

theorem convergent_den_eq {x : ℝ} (hx : Irrational x) (n : ℕ) :
    ((x.convergent n).den : ℤ) = (matrix (digitBlock x 0 (n + 1))).c := by
  rw [convergent_eq_matrix hx]
  exact Rat.den_div_eq_of_coprime (prefix_den_positive hx n) (matrix_first_column_coprime _)

theorem convergent_num_eq {x : ℝ} (hx : Irrational x) (n : ℕ) :
    (x.convergent n).num = (matrix (digitBlock x 0 (n + 1))).a := by
  rw [convergent_eq_matrix hx]
  exact Rat.num_div_eq_of_coprime (prefix_den_positive hx n) (matrix_first_column_coprime _)

theorem convergent_error_formula {x : ℝ} (hx : Irrational x) (n : ℕ) :
    let M := matrix (digitBlock x 0 (n + 1))
    |x - (x.convergent n : ℝ)| =
      1 / ((M.c : ℝ) * ((M.c : ℝ) * completeQuotient x (n + 1) + M.d)) := by
  dsimp only
  let M := matrix (digitBlock x 0 (n + 1))
  let t := completeQuotient x (n + 1)
  have hc : (0 : ℝ) < M.c := by exact_mod_cast prefix_den_positive hx n
  have hd : (0 : ℝ) ≤ M.d := by exact_mod_cast (prefix_previous_den_bounds hx n).1
  have ht : 0 < t := lt_trans zero_lt_one (one_lt_completeQuotient_succ hx n)
  have hden : 0 < (M.c : ℝ) * t + M.d := by positivity
  have hr : x * ((M.c : ℝ) * t + M.d) = (M.a : ℝ) * t + M.b := by
    simpa only [Nat.zero_add, show completeQuotient x 0 = x from rfl] using
      P5Period.digitBlock_realizes hx 0 (n + 1)
  have he : x - (M.a : ℝ) / M.c =
      ((M.b : ℝ) * M.c - (M.a : ℝ) * M.d) /
        ((M.c : ℝ) * ((M.c : ℝ) * t + M.d)) := by
    have hv : x = ((M.a : ℝ) * t + M.b) / ((M.c : ℝ) * t + M.d) :=
      (eq_div_iff hden.ne').mpr hr
    rw [hv]
    field_simp
    ring
  have hdet : |(M.b : ℝ) * M.c - (M.a : ℝ) * M.d| = 1 := by
    have h := matrix_det (digitBlock x 0 (n + 1))
    have hcast : (M.a : ℝ) * M.d - (M.b : ℝ) * M.c =
        (-1 : ℝ) ^ (digitBlock x 0 (n + 1)).length := by exact_mod_cast h
    rw [abs_sub_comm, hcast, abs_neg_one_pow]
  rw [convergent_eq_matrix hx]
  push_cast
  change |x - (M.a : ℝ) / M.c| = _
  rw [he, abs_div, hdet, abs_of_pos (mul_pos hc hden)]

/-- The lower approximation bound for every sufficiently late convergent
is independent of the exceptional initial digits. -/
theorem convergent_lower_bound {x : ℝ} (hx : Irrational x) (n C : ℕ)
    (hC : partialQuotient x (n + 1) ≤ (C : ℤ)) :
    1 / ((C : ℝ) + 2) ≤ ((x.convergent n).den : ℝ) ^ 2 *
      |x - (x.convergent n : ℝ)| := by
  let M := matrix (digitBlock x 0 (n + 1))
  let t := completeQuotient x (n + 1)
  have hc : (0 : ℝ) < M.c := by exact_mod_cast prefix_den_positive hx n
  have hd0 : (0 : ℝ) ≤ M.d := by exact_mod_cast (prefix_previous_den_bounds hx n).1
  have hdc : (M.d : ℝ) ≤ M.c := by exact_mod_cast (prefix_previous_den_bounds hx n).2
  have ht0 : 0 < t := lt_trans zero_lt_one (one_lt_completeQuotient_succ hx n)
  have htC : t < (C : ℝ) + 1 := by
    have hf := Int.lt_floor_add_one (completeQuotient x (n + 1))
    have hh : (partialQuotient x (n + 1) : ℝ) ≤ C := by exact_mod_cast hC
    change t < (partialQuotient x (n + 1) : ℝ) + 1 at hf
    linarith
  have hden : 0 < (M.c : ℝ) * ((M.c : ℝ) * t + M.d) := by positivity
  have hupper : (M.c : ℝ) * ((M.c : ℝ) * t + M.d) ≤
      ((C : ℝ) + 2) * (M.c : ℝ) ^ 2 := by nlinarith
  have he := convergent_error_formula hx n
  have hq : ((x.convergent n).den : ℝ) = M.c := by exact_mod_cast convergent_den_eq hx n
  rw [he, hq]
  change _ ≤ (M.c : ℝ) ^ 2 * (1 / ((M.c : ℝ) * ((M.c : ℝ) * t + M.d)))
  have hh := one_div_le_one_div_of_le hden hupper
  have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (M.c : ℝ))
  have hcancel : (M.c : ℝ) ^ 2 * (1 / (((C : ℝ) + 2) * (M.c : ℝ) ^ 2)) =
      1 / ((C : ℝ) + 2) := by field_simp; ring
  rwa [hcancel] at hh'

/-- Each fixed rational approximation is harmless once the unreduced
denominator is large. This also handles rational convergents represented
by arbitrarily large common multiples of numerator and denominator. -/
theorem fixed_rational_eventual_lower_bound {x : ℝ} (hx : Irrational x)
    (r : ℚ) (δ : ℝ) : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      δ ≤ (q : ℝ) ^ 2 * |x - (r : ℝ)| := by
  have he : 0 < |x - (r : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r))
  obtain ⟨Q, hQ⟩ := exists_nat_gt (max 1 (δ / |x - (r : ℝ)|))
  have hQ1 : (1 : ℝ) < Q := (le_max_left _ _).trans_lt hQ
  have hQδ : δ < (Q : ℝ) * |x - (r : ℝ)| :=
    (div_lt_iff₀ he).mp ((le_max_right _ _).trans_lt hQ)
  refine ⟨Q, fun q hq => ?_⟩
  have hqr : (Q : ℝ) ≤ q := by exact_mod_cast hq
  have hsq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  exact hQδ.le.trans (mul_le_mul_of_nonneg_right (hqr.trans hsq) he.le)

/-- Bounded eventual digits give an eventual lower approximation bound
for every integer numerator and every (possibly unreduced) denominator.
The constant depends only on the eventual digit bound. -/
theorem eventual_lower_bound_of_digits {x : ℝ} (hx : Irrational x) (C : ℕ)
    (hC : EventualBound x C) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ p : ℤ,
      1 / ((C : ℝ) + 3) ≤ (q : ℝ) * |(q : ℝ) * x - (p : ℝ)| := by
  classical
  obtain ⟨N, hN⟩ := hC
  let δ : ℝ := 1 / ((C : ℝ) + 3)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) C; linarith)
  have hδC : δ ≤ 1 / ((C : ℝ) + 2) := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  choose cutoff hcutoff using
    (fun i : Fin N => fixed_rational_eventual_lower_bound hx (x.convergent i.val) δ)
  let Q := max 1 (Finset.univ.sup cutoff)
  refine ⟨Q, fun q hq p => ?_⟩
  have hqpos : 0 < q := by have := le_max_left 1 (Finset.univ.sup cutoff); omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  let r : ℚ := (p : ℚ) / q
  have hdenDvd : r.den ∣ q := by
    have h := Rat.den_dvd p (q : ℤ)
    have heq : Rat.divInt p (q : ℤ) = r := by
      rw [Rat.divInt_eq_div]
      simp only [Int.cast_natCast, r]
    rw [heq] at h
    exact_mod_cast h
  have hdenle : r.den ≤ q := Nat.le_of_dvd hqpos hdenDvd
  have hdenr : (r.den : ℝ) ≤ q := by exact_mod_cast hdenle
  have hdenpos : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hid : (q : ℝ) * |(q : ℝ) * x - (p : ℝ)| =
      (q : ℝ) ^ 2 * |x - (r : ℝ)| := by
    have hinner : (q : ℝ) * x - (p : ℝ) = (q : ℝ) * (x - (r : ℝ)) := by
      dsimp [r]
      push_cast
      field_simp
      ring
    rw [hinner, abs_mul, abs_of_pos hqr]
    ring
  rw [hid]
  change δ ≤ _
  apply le_of_not_gt
  intro hsmall
  have hred : (r.den : ℝ) ^ 2 * |x - (r : ℝ)| < 1 / 2 := by
    have hh : (r.den : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith
    exact ((mul_le_mul_of_nonneg_right hh (abs_nonneg _)).trans_lt hsmall).trans_le hδhalf
  have hleg : |x - (r : ℝ)| < 1 / (2 * (r.den : ℝ) ^ 2) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (r.den : ℝ) ^ 2)).mpr
    nlinarith
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent hleg
  by_cases hlate : N ≤ n
  · have hbound := convergent_lower_bound hx n C (hN n hlate)
    rw [← hn] at hbound
    have hh : (r.den : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith
    exact not_lt_of_ge (hδC.trans (hbound.trans
      (mul_le_mul_of_nonneg_right hh (abs_nonneg _)))) hsmall
  · have hi : n < N := by omega
    have hs : cutoff ⟨n, hi⟩ ≤ Q :=
      (Finset.le_sup (f := cutoff) (Finset.mem_univ ⟨n, hi⟩)).trans (le_max_right _ _)
    have hbound := hcutoff ⟨n, hi⟩ q (hs.trans hq)
    rw [← hn] at hbound
    exact not_lt_of_ge hbound hsmall

end VV.P7Approximation
