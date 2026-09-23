import VV.Problem3

/-!
# Euclidean generation of the unimodular Möbius relation

This proof reduces the lower-left matrix entry by integer Euclidean division.
Consequently a relation invariant under integer translations, inversion, and
negation is invariant under every integer unimodular Möbius transformation.
No continued-fraction theorem is assumed in this purely algebraic module.
-/

namespace VV
open Problem3

theorem relation_of_mobius
    (R : ℝ → ℝ → Prop)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hadd : ∀ {x}, Irrational x → ∀ n : ℤ, R x (x + n))
    (hinv : ∀ {x}, Irrational x → R x x⁻¹)
    (hneg : ∀ {x}, Irrational x → R x (-x))
    {α β : ℝ} (hα : Irrational α) (hm : MobiusEquiv α β) : R α β := by
  suffices aux : ∀ n : ℕ, ∀ {x y : ℝ} {a b c d : ℤ}, c.natAbs = n →
      Irrational x → (a * d - b * c = 1 ∨ a * d - b * c = -1) →
      y * ((c : ℝ) * x + d) = (a : ℝ) * x + b → R x y by
    obtain ⟨a, b, c, d, hd, he⟩ := hm
    exact aux c.natAbs rfl hα hd he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y a b c d hcn hx hd he
    by_cases hc : c = 0
    · have hprod : a.natAbs * d.natAbs = 1 := by
        rw [← Int.natAbs_mul]
        rcases hd with hd | hd <;> simp only [hc, mul_zero, sub_zero] at hd <;>
          rw [hd] <;> norm_num
      have ha := Nat.eq_one_of_mul_eq_one_right hprod
      have hdu := Nat.eq_one_of_mul_eq_one_left hprod
      have ha' := Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr ha)
      have hd' := Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr hdu)
      rcases ha' with ha' | ha' <;> rcases hd' with hd' | hd'
      · have hy : y = x + b := by simp only [hc, ha', hd', Int.cast_zero, Int.cast_one,
          zero_mul, zero_add, mul_one, one_mul] at he; exact he
        rw [hy]
        exact hadd hx b
      · have hy : y = -x + (-b : ℤ) := by
          push_cast
          simp [hc, ha', hd'] at he
          linarith
        rw [hy]
        exact htrans (hneg hx) (hadd hx.neg (-b))
      · have hy : y = -x + b := by
          simp [hc, ha', hd'] at he
          linarith
        rw [hy]
        exact htrans (hneg hx) (hadd hx.neg b)
      · have hy : y = x + (-b : ℤ) := by
          push_cast
          simp [hc, ha', hd'] at he
          linarith
        rw [hy]
        exact hadd hx (-b)
    · let q : ℤ := a / c
      let r : ℤ := a % c
      let s : ℤ := b - q * d
      let y' : ℝ := (y - q)⁻¹
      have hy : Irrational y := irrational_of_mobius hx ⟨a, b, c, d, hd, he⟩
      have hyq : y - (q : ℝ) ≠ 0 := (hy.sub_intCast q).ne_zero
      have hy' : Irrational y' := (hy.sub_intCast q).inv
      have hdiv : r = a - c * q := Int.emod_def a c
      have hdivR : (r : ℝ) = a - c * q := by exact_mod_cast hdiv
      have hlinear : (r : ℝ) * x + s = (y - q) * ((c : ℝ) * x + d) := by
        dsimp [s]
        push_cast
        linear_combination x * hdivR - he
      have he' : y' * ((r : ℝ) * x + s) = (c : ℝ) * x + d := by
        rw [hlinear]
        dsimp [y']
        rw [← mul_assoc, inv_mul_cancel₀ hyq, one_mul]
      have hdcalc : c * s - d * r = -(a * d - b * c) := by
        dsimp [s]
        rw [hdiv]
        ring
      have hd' : c * s - d * r = 1 ∨ c * s - d * r = -1 := by
        rw [hdcalc]
        rcases hd with hd | hd
        · right; omega
        · left; omega
      have hlt : r.natAbs < c.natAbs := by
        have hnonneg : 0 ≤ r := Int.emod_nonneg a hc
        have hlt' : r < (c.natAbs : ℤ) := Int.emod_lt a hc
        have hcast := Int.natAbs_of_nonneg hnonneg
        omega
      have hxy' : R x y' := ih r.natAbs (by omega) rfl hx hd' he'
      have hback : R y' (y - q) := by simpa [y'] using hinv hy'
      have haddback : R (y - q) y := by
        simpa using hadd (hy.sub_intCast q) q
      exact htrans hxy' (htrans hback haddback)

end VV
