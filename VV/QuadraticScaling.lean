import VV.Problem3
import VV.Problem5
import Mathlib.Data.Int.GCD

/-!
# Actual integer quadratic equations under powers-of-two scaling

All coefficients and their gcd normalization are concrete definitions.
There are no admitted finite checks or semantic interfaces in this file.
-/

namespace VV.QuadraticScaling

structure Quadratic where
  A : ℤ
  B : ℤ
  C : ℤ
  deriving DecidableEq

def Quadratic.eval (Q : Quadratic) (x : ℝ) : ℝ :=
  (Q.A : ℝ) * x ^ 2 + Q.B * x + Q.C

def Quadratic.disc (Q : Quadratic) : ℤ := Q.B ^ 2 - 4 * Q.A * Q.C

def Quadratic.content (Q : Quadratic) : ℕ :=
  Nat.gcd Q.A.natAbs (Nat.gcd Q.B.natAbs Q.C.natAbs)

def Quadratic.scale (Q : Quadratic) (j : ℕ) : Quadratic :=
  ⟨Q.A, 2 ^ j * Q.B, 4 ^ j * Q.C⟩

def Quadratic.normalize (Q : Quadratic) : Quadratic :=
  ⟨Q.A / (Q.content : ℤ), Q.B / (Q.content : ℤ), Q.C / (Q.content : ℤ)⟩

def Quadratic.normalizedScale (Q : Quadratic) (j : ℕ) : Quadratic :=
  (Q.scale j).normalize

theorem scale_eval (Q : Quadratic) (x : ℝ) (j : ℕ) :
    (Q.scale j).eval (2 ^ j * x) = 4 ^ j * Q.eval x := by
  have hp : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  simp only [Quadratic.eval, Quadratic.scale, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat]
  rw [mul_pow]
  rw [← hp]
  ring

theorem scale_root (Q : Quadratic) {x : ℝ} (hx : Q.eval x = 0) (j : ℕ) :
    (Q.scale j).eval (2 ^ j * x) = 0 := by
  rw [scale_eval, hx, mul_zero]

theorem content_dvd_A (Q : Quadratic) : (Q.content : ℤ) ∣ Q.A := by
  exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)

theorem content_dvd_B (Q : Quadratic) : (Q.content : ℤ) ∣ Q.B := by
  exact Int.natCast_dvd.mpr ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))

theorem content_dvd_C (Q : Quadratic) : (Q.content : ℤ) ∣ Q.C := by
  exact Int.natCast_dvd.mpr ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))

theorem content_pos (Q : Quadratic) (hA : Q.A ≠ 0) : 0 < Q.content := by
  exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA)

theorem content_mul_normalize_A (Q : Quadratic) :
    (Q.content : ℤ) * Q.normalize.A = Q.A :=
  Int.mul_ediv_cancel' (content_dvd_A Q)

theorem content_mul_normalize_B (Q : Quadratic) :
    (Q.content : ℤ) * Q.normalize.B = Q.B :=
  Int.mul_ediv_cancel' (content_dvd_B Q)

theorem content_mul_normalize_C (Q : Quadratic) :
    (Q.content : ℤ) * Q.normalize.C = Q.C :=
  Int.mul_ediv_cancel' (content_dvd_C Q)

theorem normalize_A_ne_zero (Q : Quadratic) (hA : Q.A ≠ 0) : Q.normalize.A ≠ 0 := by
  intro h
  have := content_mul_normalize_A Q
  rw [h, mul_zero] at this
  exact hA this.symm

theorem content_eval_normalize (Q : Quadratic) (x : ℝ) :
    (Q.content : ℝ) * Q.normalize.eval x = Q.eval x := by
  have ha : (Q.content : ℝ) * (Q.normalize.A : ℝ) = Q.A := by
    exact_mod_cast content_mul_normalize_A Q
  have hb : (Q.content : ℝ) * (Q.normalize.B : ℝ) = Q.B := by
    exact_mod_cast content_mul_normalize_B Q
  have hc : (Q.content : ℝ) * (Q.normalize.C : ℝ) = Q.C := by
    exact_mod_cast content_mul_normalize_C Q
  unfold Quadratic.eval
  linear_combination x ^ 2 * ha + x * hb + hc

theorem normalize_root (Q : Quadratic) (hA : Q.A ≠ 0)
    {x : ℝ} (hx : Q.eval x = 0) : Q.normalize.eval x = 0 := by
  have hg : (Q.content : ℝ) ≠ 0 := by exact_mod_cast (content_pos Q hA).ne'
  have h := content_eval_normalize Q x
  rw [hx] at h
  exact (mul_eq_zero.mp h).resolve_left hg

theorem normalizedScale_root (Q : Quadratic) (hA : Q.A ≠ 0)
    {x : ℝ} (hx : Q.eval x = 0) (j : ℕ) :
    (Q.normalizedScale j).eval (2 ^ j * x) = 0 :=
  normalize_root (Q.scale j) hA (scale_root Q hx j)

/-- Bézout's identity for the gcd of all three coefficients. -/
theorem content_bezout (Q : Quadratic) :
    ∃ u v w : ℤ, (Q.content : ℤ) = u * Q.A + v * Q.B + w * Q.C := by
  let gBC : ℤ := Int.gcd Q.B Q.C
  have hg : (Q.content : ℤ) = Q.A * Int.gcdA Q.A gBC +
      gBC * Int.gcdB Q.A gBC := by
    convert Int.gcd_eq_gcd_ab Q.A gBC using 1
  have hBC : gBC = Q.B * Int.gcdA Q.B Q.C + Q.C * Int.gcdB Q.B Q.C :=
    Int.gcd_eq_gcd_ab Q.B Q.C
  refine ⟨Int.gcdA Q.A gBC,
    Int.gcdB Q.A gBC * Int.gcdA Q.B Q.C,
    Int.gcdB Q.A gBC * Int.gcdB Q.B Q.C, ?_⟩
  rw [hg, hBC]
  ring

/-- Actual gcd normalization yields the same primitive coefficient API
used by Problem 3's irrational-root uniqueness theorem. -/
theorem normalize_primitive (Q : Quadratic) (hA : Q.A ≠ 0) :
    VV.Problem3.PrimitiveTriple Q.normalize.A Q.normalize.B Q.normalize.C := by
  obtain ⟨u, v, w, h⟩ := content_bezout Q
  refine ⟨u, v, w, ?_⟩
  have hg : (Q.content : ℤ) ≠ 0 := by exact_mod_cast (content_pos Q hA).ne'
  apply mul_left_cancel₀ hg
  calc
    (Q.content : ℤ) * (u * Q.normalize.A + v * Q.normalize.B + w * Q.normalize.C) =
        u * ((Q.content : ℤ) * Q.normalize.A) +
        v * ((Q.content : ℤ) * Q.normalize.B) +
        w * ((Q.content : ℤ) * Q.normalize.C) := by ring
    _ = u * Q.A + v * Q.B + w * Q.C := by
      rw [content_mul_normalize_A, content_mul_normalize_B, content_mul_normalize_C]
    _ = (Q.content : ℤ) * 1 := by rw [← h, mul_one]

theorem normalizedScale_primitive (Q : Quadratic) (hA : Q.A ≠ 0) (j : ℕ) :
    VV.Problem3.PrimitiveTriple
      (Q.normalizedScale j).A (Q.normalizedScale j).B (Q.normalizedScale j).C :=
  normalize_primitive (Q.scale j) hA

theorem content_scale (Q : Quadratic) (j : ℕ) :
    (Q.scale j).content =
      VV.Problem5.scaledContent Q.A.natAbs Q.B.natAbs Q.C.natAbs j := by
  simp [Quadratic.content, Quadratic.scale, VV.Problem5.scaledContent,
    Int.natAbs_mul, Int.natAbs_pow]

theorem normalizedScale_discriminant (Q : Quadratic) (j : ℕ) :
    ((Q.scale j).content : ℤ) ^ 2 * (Q.normalizedScale j).disc =
      4 ^ j * Q.disc := by
  exact VV.Problem5.normalized_discriminant_identity Q.A Q.B Q.C
    (Q.normalizedScale j).A (Q.normalizedScale j).B (Q.normalizedScale j).C
    ((Q.scale j).content : ℤ) j
    (content_mul_normalize_A (Q.scale j))
    (content_mul_normalize_B (Q.scale j))
    (content_mul_normalize_C (Q.scale j))

theorem normalizedScale_abs_discriminant (Q : Quadratic) (j : ℕ) :
    VV.Problem5.scaledContent Q.A.natAbs Q.B.natAbs Q.C.natAbs j ^ 2 *
        (Q.normalizedScale j).disc.natAbs = 4 ^ j * Q.disc.natAbs := by
  have h := congrArg Int.natAbs (normalizedScale_discriminant Q j)
  simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
    content_scale] using h

theorem disc_ne_zero_of_irrational_root (Q : Quadratic) {x : ℝ}
    (hA : Q.A ≠ 0) (hx : Irrational x) (hroot : Q.eval x = 0) : Q.disc ≠ 0 := by
  intro hd
  have hd' : (Q.B : ℝ) ^ 2 - 4 * (Q.A : ℝ) * Q.C = 0 := by
    exact_mod_cast hd
  have hs : (2 * (Q.A : ℝ) * x + Q.B) ^ 2 = 0 := by
    dsimp [Quadratic.eval] at hroot
    linear_combination 4 * (Q.A : ℝ) * hroot + hd'
  have hl : (((2 * Q.A : ℤ) : ℝ) * x + Q.B) = 0 := by
    push_cast
    exact pow_eq_zero hs
  have hz := (VV.Problem3.irrational_linear hx hl).1
  exact hA (by omega)

/-- Concrete normalized equations of `2^j x` have unbounded absolute
primitive discriminants. No equation-scaling identity is assumed. -/
theorem normalizedScale_discriminants_unbounded (Q : Quadratic) {x : ℝ}
    (hA : Q.A ≠ 0) (hx : Irrational x) (hroot : Q.eval x = 0) :
    ∀ M, ∃ j, M < (Q.normalizedScale j).disc.natAbs := by
  apply VV.Problem5.quadratic_content_discriminants_unbounded
    (Int.natAbs_pos.mpr hA) Q.B.natAbs Q.C.natAbs Q.disc.natAbs
    (fun j => (Q.normalizedScale j).disc.natAbs)
  · exact Int.natAbs_pos.mpr (disc_ne_zero_of_irrational_root Q hA hx hroot)
  · exact normalizedScale_abs_discriminant Q

theorem A_ne_zero_of_primitive_irrational_root (Q : Quadratic) {x : ℝ}
    (hx : Irrational x) (hroot : Q.eval x = 0)
    (hp : VV.Problem3.PrimitiveTriple Q.A Q.B Q.C) : Q.A ≠ 0 := by
  intro hA
  have hl : (Q.B : ℝ) * x + Q.C = 0 := by
    simpa [Quadratic.eval, hA] using hroot
  obtain ⟨hB, hC⟩ := VV.Problem3.irrational_linear hx hl
  obtain ⟨u, v, w, hp⟩ := hp
  simp [hA, hB, hC] at hp

/-- Two primitive integer quadratics with the same irrational root have
equal discriminants. Primitive normalization removes the scalar square. -/
theorem primitive_same_root_disc (Q R : Quadratic) {x : ℝ}
    (hx : Irrational x) (hQ : Q.eval x = 0) (hR : R.eval x = 0)
    (pQ : VV.Problem3.PrimitiveTriple Q.A Q.B Q.C)
    (pR : VV.Problem3.PrimitiveTriple R.A R.B R.C) : R.disc = Q.disc := by
  have hA := A_ne_zero_of_primitive_irrational_root Q hx hQ pQ
  obtain ⟨v, ha, hb, hc⟩ := VV.Problem3.relation_multiple hx hA pQ hQ hR
  obtain ⟨u, w, z, hp⟩ := pR
  have hv : v * (u * Q.A + w * Q.B + z * Q.C) = 1 := by
    rw [ha, hb, hc] at hp
    linear_combination hp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hv with hv | hv
  · simp [Quadratic.disc, ha, hb, hc, hv]
  · simp [Quadratic.disc, ha, hb, hc, hv]

end VV.QuadraticScaling
