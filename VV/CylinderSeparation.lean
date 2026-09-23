import VV.CylinderGeometry

/-!
Lower separation estimates for actual continued-fraction cylinders with a
bounded alphabet. This supplies the converse geometric estimate needed when
turning small metric covering numbers into small word dictionaries.
-/

namespace VV.CylinderGeometry

theorem branch_difference (a u v : ℝ) (hu : a + u ≠ 0) (hv : a + v ≠ 0) :
    branch a u - branch a v = (v - u) / ((a + u) * (a + v)) := by
  simp only [branch]
  field_simp

theorem branch_lower_distance (a u v K : ℝ)
    (ha : 1 ≤ a) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hau : a + u ≤ K) (hav : a + v ≤ K) :
    |u - v| / K ^ 2 ≤ |branch a u - branch a v| := by
  have hpu : 0 < a + u := by linarith
  have hpv : 0 < a + v := by linarith
  have hK : 0 < K := lt_of_lt_of_le hpu hau
  have hprod : (a + u) * (a + v) ≤ K ^ 2 := by nlinarith
  rw [branch_difference a u v hpu.ne' hpv.ne', abs_div,
    abs_of_pos (mul_pos hpu hpv), abs_sub_comm v u]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hpu hpv) hprod

theorem tail_lower_bound {x : ℝ} (hx : Irrational x) (n : ℕ) (M : ℕ)
    (hM : partialQuotient x (n + 1) ≤ (M : ℤ)) :
    1 / ((M : ℝ) + 1) ≤ tail x n := by
  have ha : (1 : ℝ) ≤ partialQuotient x (n + 1) := by
    exact_mod_cast one_le_partialQuotient_succ hx n
  have hb : (partialQuotient x (n + 1) : ℝ) ≤ M := by exact_mod_cast hM
  have ht := tail_nonneg x (n + 1)
  have ht1 := tail_lt_one x (n + 1)
  have hp : 0 < (partialQuotient x (n + 1) : ℝ) + tail x (n + 1) := by
    linarith
  rw [tail_rec x n, branch, inv_eq_one_div]
  exact one_div_le_one_div_of_le hp (by linarith)

/-- Distinct next digits are separated if the digits at the next two
positions are bounded. No assertion of separation of unrestricted cylinders
(which would be false at rational endpoints) is used. -/
theorem distinct_next_digit_separation {x y : ℝ}
    (hx : Irrational x) (hy : Irrational y) (n M : ℕ)
    (hxM : ∀ j : ℕ, n ≤ j → partialQuotient x (j + 1) ≤ (M : ℤ))
    (hyM : ∀ j : ℕ, n ≤ j → partialQuotient y (j + 1) ≤ (M : ℤ))
    (hne : partialQuotient x (n + 1) ≠ partialQuotient y (n + 1)) :
    1 / ((M : ℝ) + 1) ^ 3 ≤ |tail x n - tail y n| := by
  have ordered {u v : ℝ} (hu : Irrational u) (hv : Irrational v)
      (huM : ∀ j : ℕ, n ≤ j → partialQuotient u (j + 1) ≤ (M : ℤ))
      (hvM : ∀ j : ℕ, n ≤ j → partialQuotient v (j + 1) ≤ (M : ℤ))
      (hlt : partialQuotient u (n + 1) < partialQuotient v (n + 1)) :
      1 / ((M : ℝ) + 1) ^ 3 ≤ tail u n - tail v n := by
    let a : ℝ := partialQuotient u (n + 1)
    let b : ℝ := partialQuotient v (n + 1)
    let r := tail u (n + 1)
    let s := tail v (n + 1)
    let K : ℝ := (M : ℝ) + 1
    have hK : 0 < K := by dsimp [K]; positivity
    have ha : 1 ≤ a := by dsimp [a]; exact_mod_cast one_le_partialQuotient_succ hu n
    have hb : 1 ≤ b := by dsimp [b]; exact_mod_cast one_le_partialQuotient_succ hv n
    have hab : a + 1 ≤ b := by dsimp [a, b]; exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    have haM : a ≤ M := by dsimp [a]; exact_mod_cast huM n le_rfl
    have hbM : b ≤ M := by dsimp [b]; exact_mod_cast hvM n le_rfl
    have hr0 : 0 ≤ r := tail_nonneg u _
    have hs0 : 0 ≤ s := tail_nonneg v _
    have hr1 : r < 1 := tail_lt_one u _
    have hs1 : s < 1 := tail_lt_one v _
    have hs : 1 / K ≤ s := tail_lower_bound hv (n + 1) M (hvM (n + 1) (by omega))
    have hden1 : 0 < a + r := by linarith
    have hden2 : 0 < b + s := by linarith
    have hprod : (a + r) * (b + s) ≤ K ^ 2 := by dsimp [K]; nlinarith
    have hnum : 1 / K ≤ b + s - (a + r) := by linarith
    have hid : tail u n - tail v n =
        (b + s - (a + r)) / ((a + r) * (b + s)) := by
      rw [tail_rec u n, tail_rec v n]
      change (a + r)⁻¹ - (b + s)⁻¹ = _
      field_simp
    rw [hid]
    calc
      1 / ((M : ℝ) + 1) ^ 3 = (1 / K) / K ^ 2 := by dsimp [K]; field_simp; ring
      _ ≤ (1 / K) / ((a + r) * (b + s)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hden1 hden2) hprod
      _ ≤ (b + s - (a + r)) / ((a + r) * (b + s)) :=
        div_le_div_of_nonneg_right hnum (mul_pos hden1 hden2).le
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (ordered hx hy hxM hyM hlt).trans (le_abs_self _)
  · rw [abs_sub_comm]
    exact (ordered hy hx hyM hxM hgt).trans (le_abs_self _)

/-- A sufficiently small distance forces equality of the next `L` actual
digits, when both remaining alphabets are bounded by `M`. -/
theorem close_tails_same_prefix {x y : ℝ}
    (hx : Irrational x) (hy : Irrational y) (M L n : ℕ)
    (hxM : ∀ j : ℕ, n ≤ j → partialQuotient x (j + 1) ≤ (M : ℤ))
    (hyM : ∀ j : ℕ, n ≤ j → partialQuotient y (j + 1) ≤ (M : ℤ))
    (hclose : |tail x n - tail y n| < 1 / ((M : ℝ) + 1) ^ (2 * L + 1)) :
    ∀ k : ℕ, k < L →
      partialQuotient x (n + k + 1) = partialQuotient y (n + k + 1) := by
  induction L generalizing n with
  | zero => simp
  | succ L ih =>
    have hK : (1 : ℝ) ≤ (M : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) M; linarith
    have hK0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hsmall : 1 / ((M : ℝ) + 1) ^ (2 * (L + 1) + 1) ≤
        1 / ((M : ℝ) + 1) ^ 3 := by
      exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ hK (by omega))
    have hfirst : partialQuotient x (n + 1) = partialQuotient y (n + 1) := by
      classical
      by_cases heq : partialQuotient x (n + 1) = partialQuotient y (n + 1)
      · exact heq
      · have hsep := distinct_next_digit_separation hx hy n M hxM hyM heq
        exact False.elim (not_lt_of_ge hsep (hclose.trans_le hsmall))
    have hdist := branch_lower_distance (partialQuotient x (n + 1))
      (tail x (n + 1)) (tail y (n + 1)) ((M : ℝ) + 1)
      (by exact_mod_cast one_le_partialQuotient_succ hx n)
      (tail_nonneg x _) (tail_nonneg y _)
      (by have hh : (partialQuotient x (n + 1) : ℝ) ≤ M := by
            exact_mod_cast hxM n le_rfl
          have ht := tail_lt_one x (n + 1)
          linarith)
      (by have hh : (partialQuotient x (n + 1) : ℝ) ≤ M := by
            exact_mod_cast hxM n le_rfl
          have ht := tail_lt_one y (n + 1)
          linarith)
    have hrew : |branch (partialQuotient x (n + 1)) (tail x (n + 1)) -
        branch (partialQuotient x (n + 1)) (tail y (n + 1))| =
        |tail x n - tail y n| := by
      conv_rhs => rw [tail_rec x n, tail_rec y n, ← hfirst]
    rw [hrew] at hdist
    have hnext : |tail x (n + 1) - tail y (n + 1)| <
        1 / ((M : ℝ) + 1) ^ (2 * L + 1) := by
      calc
        _ = (|tail x (n + 1) - tail y (n + 1)| / ((M : ℝ) + 1) ^ 2) *
            ((M : ℝ) + 1) ^ 2 := (div_mul_cancel₀ _ (by positivity)).symm
        _ < (1 / ((M : ℝ) + 1) ^ (2 * (L + 1) + 1)) * ((M : ℝ) + 1) ^ 2 :=
          mul_lt_mul_of_pos_right (hdist.trans_lt hclose) (by positivity)
        _ = _ := by
          have he : 2 * (L + 1) + 1 = (2 * L + 1) + 2 := by omega
          rw [he, pow_add]
          field_simp
          ring
    have hrest := ih (n + 1)
      (fun j hj => hxM j (by omega)) (fun j hj => hyM j (by omega)) hnext
    intro k hk
    cases k with
    | zero => simpa using hfirst
    | succ k =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hrest k (by omega))

/-- Uniform separation between different length-`L` words of bounded
continued fractions with the same integer part. -/
theorem different_prefix_separation {x y : ℝ}
    (hx : Irrational x) (hy : Irrational y) (M L : ℕ)
    (hxM : ∀ j : ℕ, partialQuotient x (j + 1) ≤ (M : ℤ))
    (hyM : ∀ j : ℕ, partialQuotient y (j + 1) ≤ (M : ℤ))
    (hzero : partialQuotient x 0 = partialQuotient y 0)
    (hdifferent : ∃ k : ℕ, k < L ∧ partialQuotient x (k + 1) ≠
      partialQuotient y (k + 1)) :
    1 / ((M : ℝ) + 1) ^ (2 * L + 1) ≤ dist x y := by
  by_contra! h
  have hfloor : ⌊x⌋ = ⌊y⌋ := hzero
  have heq : x - y = tail x 0 - tail y 0 := by
    simp only [tail, completeQuotient, Int.fract]
    rw [hfloor]
    ring
  have hc : |tail x 0 - tail y 0| < 1 / ((M : ℝ) + 1) ^ (2 * L + 1) := by
    simpa only [Real.dist_eq, heq] using h
  obtain ⟨k, hk, hne⟩ := hdifferent
  apply hne
  simpa using (close_tails_same_prefix hx hy M L 0
    (fun j _ => hxM j) (fun j _ => hyM j) hc k hk)

/-- A cover by sets smaller than the separation scale bounds the number
of distinct realized words. The points here are actual irrational numbers,
and `hword` ties the words to their actual partial quotients. -/
theorem word_count_le_cover_card (M L : ℕ) (a₀ : ℤ)
    (W : Finset (Fin L → ℤ)) {ι : Type*} [Fintype ι]
    (U : ι → Set ℝ) (point : W → ℝ)
    (hirr : ∀ w, Irrational (point w))
    (hbound : ∀ w j, partialQuotient (point w) (j + 1) ≤ (M : ℤ))
    (hzero : ∀ w, partialQuotient (point w) 0 = a₀)
    (hword : ∀ w (k : Fin L), partialQuotient (point w) (k.val + 1) = w.val k)
    (hcover : ∀ w, ∃ i, point w ∈ U i)
    (hsmall : ∀ i x, x ∈ U i → ∀ y, y ∈ U i →
      dist x y < 1 / ((M : ℝ) + 1) ^ (2 * L + 1)) :
    W.card ≤ Fintype.card ι := by
  classical
  choose label hlabel using hcover
  have hinj : Function.Injective label := by
    intro u v huv
    apply Subtype.ext
    funext k
    by_contra hne
    have hdiff : ∃ j : ℕ, j < L ∧
        partialQuotient (point u) (j + 1) ≠ partialQuotient (point v) (j + 1) := by
      refine ⟨k.val, k.isLt, ?_⟩
      simpa only [hword] using hne
    have hsep := different_prefix_separation (hirr u) (hirr v) M L
      (hbound u) (hbound v) ((hzero u).trans (hzero v).symm) hdiff
    have hv : point v ∈ U (label u) := by rw [huv]; exact hlabel v
    exact not_lt_of_ge hsep (hsmall (label u) (point u) (hlabel u) (point v) hv)
  simpa using Fintype.card_le_of_injective label hinj

end VV.CylinderGeometry
