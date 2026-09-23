import VV.TailEquivalence

namespace VV

theorem tailEquivalent_add_int (x : ℝ) (z : ℤ) : TailEquivalent x (x + z) := by
  apply tailEquivalent_of_completeQuotient_eq (m := 1) (n := 1)
  simp only [completeQuotient, Int.fract_add_intCast]

theorem tailEquivalent_fract (x : ℝ) : TailEquivalent x (Int.fract x) := by
  simpa only [Int.fract, Int.cast_neg, sub_eq_add_neg] using
    tailEquivalent_add_int x (-⌊x⌋)

theorem tailEquivalent_inv_pos {x : ℝ} (hx : Irrational x) (hp : 0 < x) :
    TailEquivalent x x⁻¹ := by
  by_cases hlt : x < 1
  · apply tailEquivalent_of_completeQuotient_eq (m := 1) (n := 0)
    simp only [completeQuotient, Int.fract_eq_self.mpr ⟨hp.le, hlt⟩]
  · have hgt : 1 < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hx.ne_one)
    have hi : Int.fract x⁻¹ = x⁻¹ :=
      Int.fract_eq_self.mpr ⟨(inv_pos.mpr hp).le, inv_lt_one_of_one_lt₀ hgt⟩
    apply tailEquivalent_of_completeQuotient_eq (m := 0) (n := 1)
    simp only [completeQuotient, hi, inv_inv]

/-- Negation is obtained using positive reciprocals and integral shifts.
All intermediate positive quantities are explicit, so no rule about
continued fractions of negative numbers is assumed. -/
theorem tailEquivalent_neg {x : ℝ} (hx : Irrational x) : TailEquivalent x (-x) := by
  let f := Int.fract x
  have hf : Irrational f := hx.sub_intCast ⌊x⌋
  have hf0 : 0 < f := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hf.ne_zero)
  have hf1 : f < 1 := Int.fract_lt_one x
  have ht : Irrational (f⁻¹ - 1) := by simpa using hf.inv.sub_intCast 1
  have ht0 : 0 < f⁻¹ - 1 := sub_pos.mpr ((one_lt_inv₀ hf0).mpr hf1)
  have hcf : Irrational (1-f) := by simpa using hf.intCast_sub 1
  have hcf0 : 0 < 1-f := sub_pos.mpr hf1
  have hshift : TailEquivalent f⁻¹ (f⁻¹ - 1) := by
    simpa using tailEquivalent_add_int f⁻¹ (-1)
  have hshift2 : TailEquivalent (f⁻¹ - 1)⁻¹ ((f⁻¹ - 1)⁻¹ + 1) := by
    simpa using tailEquivalent_add_int (f⁻¹ - 1)⁻¹ 1
  have halg : (f⁻¹ - 1)⁻¹ + 1 = (1-f)⁻¹ := by
    field_simp
  have hmid : TailEquivalent f (1-f) := by
    have h := (tailEquivalent_inv_pos hf hf0).trans hshift
    have h := h.trans (tailEquivalent_inv_pos ht ht0)
    have h := h.trans hshift2
    rw [halg] at h
    exact h.trans (tailEquivalent_inv_pos hcf hcf0).symm
  have hneg : TailEquivalent (-x) (1-f) := by
    simpa only [f, Int.fract_neg (show Int.fract x ≠ 0 from hf.ne_zero)] using
      tailEquivalent_fract (-x)
  exact ((tailEquivalent_fract x).trans hmid).trans hneg.symm

theorem tailEquivalent_inv {x : ℝ} (hx : Irrational x) : TailEquivalent x x⁻¹ := by
  rcases lt_or_gt_of_ne hx.ne_zero with hn | hp
  · have h := (tailEquivalent_neg hx).trans (tailEquivalent_inv_pos hx.neg (neg_pos.mpr hn))
    have h := h.trans (tailEquivalent_neg hx.neg.inv)
    simpa only [inv_neg, neg_neg] using h
  · exact tailEquivalent_inv_pos hx hp

end VV
