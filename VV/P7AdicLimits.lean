import VV.Problem7
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Sequences

/-!
# The genuine 2-adic limit steps in the Problem 7 argument

These are ordinary theorems about the actual mathlib p-adic numbers and
integers. They do not assume BBEK, an entropy bound, or a Hausdorff-dimension
conclusion. The arithmetic hypotheses state the precise eventual bounds
needed from convergent denominators; they are not asserted for the CF
sequences until the necessary approximation lemmas have been proved.
-/

open Filter Set
open scoped Topology

namespace VV.P7AdicLimits

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The approximation product of a fixed nonnegative linear combination
of adjacent convergent denominators is bounded by `(a+b)^2`. The algebra
only needs the usual elementary convergent-error inequalities; it does
not need a bound on the continued-fraction alphabet. -/
theorem linear_combination_error_bound
    (a b q r e f : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hr : r ≤ q) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hqe : q * e ≤ 1) (hqf : q * f ≤ 1) :
    (a * q + b * r) * |a * e - b * f| ≤ (a + b) ^ 2 := by
  have herr : |a * e - b * f| ≤ a * e + b * f := by
    simpa only [abs_of_nonneg (mul_nonneg ha he), abs_of_nonneg (mul_nonneg hb hf)] using
      abs_sub (a * e) (b * f)
  have hqerr : q * |a * e - b * f| ≤ a + b := by
    calc
      q * |a * e - b * f| ≤ q * (a * e + b * f) := mul_le_mul_of_nonneg_left herr hq
      _ = a * (q * e) + b * (q * f) := by ring
      _ ≤ a * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hqe ha) (mul_le_mul_of_nonneg_left hqf hb)
      _ = a + b := by ring
  calc
    (a * q + b * r) * |a * e - b * f| ≤
        ((a + b) * q) * |a * e - b * f| :=
      mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
    _ = (a + b) * (q * |a * e - b * f|) := by ring
    _ ≤ (a + b) * (a + b) := mul_le_mul_of_nonneg_left hqerr (add_nonneg ha hb)
    _ = (a + b) ^ 2 := by ring

/-- The uniform *eventual* Diophantine lower bound at each dyadic layer.
The threshold is allowed to depend on the layer. -/
def DyadicEventualLowerBound (α δ : ℝ) : Prop :=
  ∀ h : ℕ, ∃ N : ℕ, ∀ q : ℕ, N ≤ q → ∀ p : ℤ,
    δ ≤ (q : ℝ) * |(q : ℝ) * ((2 : ℝ) ^ h * α) - (p : ℝ)|

/-- A real approximation with denominator divisible by a fixed `2^h`
becomes an approximation at layer `h`. Denominator growth ensures that
the layer-dependent finite exceptional range has actually been passed. -/
theorem layer_lower_bounds_of_diophantine
    (α δ : ℝ) (hα : DyadicEventualLowerBound α δ)
    (q : ℕ → ℕ) (p : ℕ → ℤ) (hq : Tendsto q atTop atTop) :
    ∀ h : ℕ, ∀ᶠ n in atTop, 2 ^ h ∣ q n →
      δ ≤ (q n : ℝ) * |(q n : ℝ) * α - (p n : ℝ)| / (2 : ℝ) ^ h := by
  intro h
  obtain ⟨N, hN⟩ := hα h
  have hlarge : ∀ᶠ n in atTop, 2 ^ h * N ≤ q n :=
    hq.eventually (eventually_ge_atTop (2 ^ h * N))
  filter_upwards [hlarge] with n hn
  rintro ⟨k, hk⟩
  have hNk : N ≤ k := Nat.le_of_mul_le_mul_left (by simpa only [hk] using hn) (by positivity)
  have hcast : (k : ℝ) * (2 : ℝ) ^ h = (q n : ℝ) := by
    rw [hk]
    push_cast
    ring
  have hbase : δ ≤ (k : ℝ) * |(q n : ℝ) * α - (p n : ℝ)| := by
    simpa only [← mul_assoc, hcast] using hN k hNk (p n)
  have hpow : (2 : ℝ) ^ h ≠ 0 := by positivity
  have heq : (k : ℝ) * |(q n : ℝ) * α - (p n : ℝ)| =
      (q n : ℝ) * |(q n : ℝ) * α - (p n : ℝ)| / (2 : ℝ) ^ h := by
    apply (eq_div_iff hpow).mpr
    rw [mul_right_comm, hcast]
  exact heq ▸ hbase

/-- The 2-adic norm is locally constant at each nonzero point. -/
theorem eventually_norm_eq {z : ℕ → ℤ_[2]} {w : ℤ_[2]}
    (hz : Tendsto z atTop (𝓝 w)) (hw : w ≠ 0) :
    ∀ᶠ n in atTop, ‖z n‖ = ‖w‖ := by
  have hnorm : Tendsto (fun n => ‖z n - w‖) atTop (𝓝 0) := by
    simpa using (hz.sub (tendsto_const_nhds (x := w))).norm
  have hclose : ∀ᶠ n in atTop, ‖z n - w‖ < ‖w‖ :=
    hnorm.eventually (gt_mem_nhds (norm_pos_iff.mpr hw))
  filter_upwards [hclose] with n hn
  have h := PadicInt.norm_eq_of_norm_add_lt_right
    (z1 := z n) (z2 := -w) (by simpa only [norm_neg, sub_eq_add_neg] using hn)
  simpa only [norm_neg] using h

/-- Exclusion of one fixed divisibility condition prevents a sequence of
ordinary integer denominators from tending to zero in the 2-adic topology. -/
theorem not_tendsto_zero_of_eventually_not_dvd (q : ℕ → ℕ) (h : ℕ)
    (hq : ∀ᶠ n in atTop, ¬ 2 ^ h ∣ q n) :
    ¬ Tendsto (fun n => (q n : ℤ_[2])) atTop (𝓝 0) := by
  intro ht
  have hnorm : Tendsto (fun n => ‖(q n : ℤ_[2])‖) atTop (𝓝 0) := by
    simpa using ht.norm
  have hp : 0 < (2 : ℝ) ^ (-(h : ℤ)) := by positivity
  have hsmall : ∀ᶠ n in atTop,
      ‖(q n : ℤ_[2])‖ < (2 : ℝ) ^ (-(h : ℤ)) := hnorm.eventually (gt_mem_nhds hp)
  obtain ⟨n, hndvd, hnsmall⟩ := (hq.and hsmall).exists
  have hzdvd : ((2 : ℤ) ^ h) ∣ (q n : ℤ) :=
    PadicInt.norm_int_le_pow_iff_dvd.mp (by simpa using hnsmall.le)
  exact hndvd (by exact_mod_cast hzdvd)

/-- This combines the previously verified fixed-layer inequality argument
with actual 2-adic topology. There is no exchange of `forall h` and
`eventually n`. -/
theorem not_tendsto_zero_of_layer_lower_bounds
    (q : ℕ → ℕ) (err : ℕ → ℝ) (δ M : ℝ) (hδ : 0 < δ)
    (hbounded : ∀ᶠ n in atTop, (q n : ℝ) * err n ≤ M)
    (hlayers : ∀ h : ℕ, ∀ᶠ n in atTop,
      2 ^ h ∣ q n → δ ≤ (q n : ℝ) * err n / (2 : ℝ) ^ h) :
    ¬ Tendsto (fun n => (q n : ℤ_[2])) atTop (𝓝 0) := by
  obtain ⟨h, hh⟩ := VV.Problem7.eventually_not_dvd_of_layer_lower_bounds
    q err δ M hδ hbounded hlayers
  exact not_tendsto_zero_of_eventually_not_dvd q h hh

/-- Once the p-adic limit is nonzero, the dyadic layer becomes constant.
It is then legitimate to use the eventual bound at that one fixed layer
and pass to the real limit. -/
theorem weighted_lower_bound_at_limit
    {z : ℕ → ℤ_[2]} {w : ℤ_[2]} {c : ℕ → ℝ} {c₀ δ : ℝ}
    (hz : Tendsto z atTop (𝓝 w)) (hw : w ≠ 0)
    (hc : Tendsto c atTop (𝓝 c₀))
    (hlayers : ∀ h : ℕ, ∀ᶠ n in atTop,
      ‖z n‖ = (2 : ℝ) ^ (-(h : ℤ)) →
        δ ≤ c n * (2 : ℝ) ^ (-(h : ℤ))) :
    δ ≤ c₀ * ‖w‖ := by
  let h := PadicInt.valuation w
  have hwNorm : ‖w‖ = (2 : ℝ) ^ (-(h : ℤ)) :=
    PadicInt.norm_eq_zpow_neg_valuation hw
  have hbound : ∀ᶠ n in atTop, δ ≤ c n * ‖w‖ := by
    filter_upwards [eventually_norm_eq hz hw, hlayers h] with n hnorm hn
    rw [hwNorm]
    exact hn (hnorm.trans hwNorm)
  exact ge_of_tendsto (hc.mul_const ‖w‖) hbound

/-- The compact real interval and the actual 2-adic integer ring supply a
joint convergent subsequence. -/
theorem joint_compact_subsequence (u : ℕ → ℝ) (v : ℕ → ℤ_[2])
    (hu : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) :
    ∃ w : ℝ × ℤ_[2], w.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => (u (φ n), v (φ n))) atTop (𝓝 w) := by
  obtain ⟨w, hw, φ, hφ, ht⟩ :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set ℤ_[2]))).tendsto_subseq
      (x := fun n => (u n, v n)) (fun n => ⟨hu n, Set.mem_univ _⟩)
  exact ⟨w, hw.1, φ, hφ, ht⟩

/-- The sign of the ratio matters: `v*r=-q` gives the positive denominator
combination `a*q+b*r` appearing in the approximation argument. -/
theorem normalized_combination_norm (q r a b : ℕ) (v : ℤ_[2])
    (hr : ‖(r : ℤ_[2])‖ = 1) (hv : v * (r : ℤ_[2]) = -(q : ℤ_[2])) :
    ‖(a : ℤ_[2]) * v - (b : ℤ_[2])‖ = ‖((a * q + b * r : ℕ) : ℤ_[2])‖ := by
  have hid : ((a : ℤ_[2]) * v - (b : ℤ_[2])) * (r : ℤ_[2]) =
      -((a * q + b * r : ℕ) : ℤ_[2]) := by
    push_cast
    calc
      ((a : ℤ_[2]) * v - (b : ℤ_[2])) * (r : ℤ_[2]) =
          (a : ℤ_[2]) * (v * (r : ℤ_[2])) - (b : ℤ_[2]) * (r : ℤ_[2]) := by ring
      _ = -((a : ℤ_[2]) * (q : ℤ_[2]) + (b : ℤ_[2]) * (r : ℤ_[2])) := by
        rw [hv]
        ring
  have hnorm := congrArg norm hid
  simpa only [norm_mul, hr, mul_one, norm_neg] using hnorm

/-- For a fixed test `(a,b)`, an affine rational 2-adic limit is ruled out
by the true divisibility hypotheses on `a*q_n+b*r_n`. -/
theorem affine_limit_ne_zero
    (q r : ℕ → ℕ) (v : ℕ → ℤ_[2]) (v₀ : ℤ_[2]) (a b : ℕ)
    (hr : ∀ n, ‖(r n : ℤ_[2])‖ = 1)
    (hratio : ∀ n, v n * (r n : ℤ_[2]) = -(q n : ℤ_[2]))
    (hv : Tendsto v atTop (𝓝 v₀))
    (err : ℕ → ℝ) (δ M : ℝ) (hδ : 0 < δ)
    (hbounded : ∀ᶠ n in atTop, ((a * q n + b * r n : ℕ) : ℝ) * err n ≤ M)
    (hlayers : ∀ h : ℕ, ∀ᶠ n in atTop,
      2 ^ h ∣ a * q n + b * r n →
        δ ≤ ((a * q n + b * r n : ℕ) : ℝ) * err n / (2 : ℝ) ^ h) :
    (a : ℤ_[2]) * v₀ - (b : ℤ_[2]) ≠ 0 := by
  intro hzero
  have htest : Tendsto (fun n => (a : ℤ_[2]) * v n - (b : ℤ_[2])) atTop (𝓝 0) := by
    simpa only [hzero] using (hv.const_mul (a : ℤ_[2])).sub_const (b : ℤ_[2])
  have hnorm : Tendsto (fun n => ‖((a * q n + b * r n : ℕ) : ℤ_[2])‖) atTop (𝓝 0) := by
    have ht := htest.norm
    simp only [norm_zero] at ht
    convert ht using 1
    funext n
    exact (normalized_combination_norm (q n) (r n) a b (v n) (hr n) (hratio n)).symm
  have hQ : Tendsto (fun n => ((a * q n + b * r n : ℕ) : ℤ_[2])) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  exact not_tendsto_zero_of_layer_lower_bounds
    (fun n => a * q n + b * r n) err δ M hδ hbounded hlayers hQ

/-- Pass the fixed test inequality to a joint real/2-adic limit once the
preceding theorem has supplied its required nonvanishing hypothesis. -/
theorem joint_test_lower_bound
    {u : ℕ → ℝ} {v : ℕ → ℤ_[2]} {u₀ : ℝ} {v₀ : ℤ_[2]}
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (a b : ℕ) (δ : ℝ)
    (hne : (a : ℤ_[2]) * v₀ - (b : ℤ_[2]) ≠ 0)
    (hlayers : ∀ h : ℕ, ∀ᶠ n in atTop,
      ‖(a : ℤ_[2]) * v n - (b : ℤ_[2])‖ = (2 : ℝ) ^ (-(h : ℤ)) →
        δ ≤ (max a b : ℕ) * |(a : ℝ) * u n - (b : ℝ)| * (2 : ℝ) ^ (-(h : ℤ))) :
    δ ≤ (max a b : ℕ) * |(a : ℝ) * u₀ - (b : ℝ)| *
      ‖(a : ℤ_[2]) * v₀ - (b : ℤ_[2])‖ := by
  apply weighted_lower_bound_at_limit
    ((hv.const_mul (a : ℤ_[2])).sub_const (b : ℤ_[2])) hne
  · exact (((hu.const_mul (a : ℝ)).sub_const (b : ℝ)).abs).const_mul ((max a b : ℕ) : ℝ)
  · exact hlayers

/-- An actual unit-normalized ratio in the 2-adic integer ring. -/
def unitRatio (q r : ℕ) : ℤ_[2] := -(q : ℤ_[2]) * (r : ℤ_[2]).inv

theorem unitRatio_mul (q r : ℕ) (hr : ‖(r : ℤ_[2])‖ = 1) :
    unitRatio q r * (r : ℤ_[2]) = -(q : ℤ_[2]) := by
  rw [unitRatio, mul_assoc, PadicInt.inv_mul hr, mul_one]

/-- The elementary approximation data used by the joint-limit argument.
In the continued-fraction application, `q,r` are adjacent denominators,
`p,s` are their numerators, `f` is the preceding absolute error, and `σ`
is its alternating sign. All bounds refer to these actual real errors. -/
structure AdjacentApproximationData (α : ℝ) where
  q : ℕ → ℕ
  r : ℕ → ℕ
  p : ℕ → ℤ
  s : ℕ → ℤ
  u : ℕ → ℝ
  f : ℕ → ℝ
  σ : ℕ → ℝ
  q_growth : Tendsto q atTop atTop
  r_le_q : ∀ n, r n ≤ q n
  f_nonneg : ∀ n, 0 ≤ f n
  u_interval : ∀ n, u n ∈ Icc (0 : ℝ) 1
  q_mul_f_le_one : ∀ n, (q n : ℝ) * f n ≤ 1
  sign_abs : ∀ n, |σ n| = 1
  error_left : ∀ n, (q n : ℝ) * α - (p n : ℝ) = σ n * f n * u n
  error_right : ∀ n, (r n : ℝ) * α - (s n : ℝ) = -(σ n * f n)
  r_unit : ∀ n, ‖(r n : ℤ_[2])‖ = 1

namespace AdjacentApproximationData

variable {α : ℝ} (D : AdjacentApproximationData α)

def v (n : ℕ) : ℤ_[2] := unitRatio (D.q n) (D.r n)

theorem combination_error (a b n : ℕ) :
    |((a * D.q n + b * D.r n : ℕ) : ℝ) * α -
      ((a : ℤ) * D.p n + (b : ℤ) * D.s n : ℤ)| =
        D.f n * |(a : ℝ) * D.u n - (b : ℝ)| := by
  have hid : ((a * D.q n + b * D.r n : ℕ) : ℝ) * α -
      ((a : ℤ) * D.p n + (b : ℤ) * D.s n : ℤ) =
        D.σ n * D.f n * ((a : ℝ) * D.u n - (b : ℝ)) := by
    push_cast
    calc
      _ = (a : ℝ) * ((D.q n : ℝ) * α - (D.p n : ℝ)) +
          (b : ℝ) * ((D.r n : ℝ) * α - (D.s n : ℝ)) := by ring
      _ = _ := by rw [D.error_left, D.error_right]; ring
  rw [hid, abs_mul, abs_mul, D.sign_abs, one_mul, abs_of_nonneg (D.f_nonneg n)]

theorem combination_error_bound (a b n : ℕ) :
    ((a * D.q n + b * D.r n : ℕ) : ℝ) *
      |((a * D.q n + b * D.r n : ℕ) : ℝ) * α -
        ((a : ℤ) * D.p n + (b : ℤ) * D.s n : ℤ)| ≤ ((a : ℝ) + b) ^ 2 := by
  rw [D.combination_error]
  have h := linear_combination_error_bound (a : ℝ) (b : ℝ) (D.q n) (D.r n)
    (D.f n * D.u n) (D.f n) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast D.r_le_q n)
    (mul_nonneg (D.f_nonneg n) (D.u_interval n).1) (D.f_nonneg n)
    (by nlinarith [D.q_mul_f_le_one n, (D.u_interval n).1, (D.u_interval n).2,
      D.f_nonneg n, Nat.cast_nonneg (α := ℝ) (D.q n)]) (D.q_mul_f_le_one n)
  have heq : |(a : ℝ) * (D.f n * D.u n) - (b : ℝ) * D.f n| =
      D.f n * |(a : ℝ) * D.u n - (b : ℝ)| := by
    rw [show (a : ℝ) * (D.f n * D.u n) - (b : ℝ) * D.f n =
      D.f n * ((a : ℝ) * D.u n - (b : ℝ)) by ring,
      abs_mul, abs_of_nonneg (D.f_nonneg n)]
  simpa only [Nat.cast_add, Nat.cast_mul, heq] using h

/-- Every joint limit satisfies the exact Diophantine inequality needed
as input to BBEK Theorem 4.2. The layer and subsequence quantifiers are
handled here; later `BBEKFinal` constructs the rigidity theorem with its
one explicitly admitted EL low-entropy core. -/
theorem joint_limit_lower_bound
    {δ u₀ : ℝ} {v₀ : ℤ_[2]} (hδ : 0 < δ)
    (hα : DyadicEventualLowerBound α δ)
    (hu : Tendsto D.u atTop (𝓝 u₀)) (hv : Tendsto D.v atTop (𝓝 v₀))
    (a b : ℕ) (ha : 1 ≤ a) :
    δ / 2 ≤ ((max a b : ℕ) : ℝ) * |(a : ℝ) * u₀ - (b : ℝ)| *
      ‖(a : ℤ_[2]) * v₀ - (b : ℤ_[2])‖ := by
  let Q : ℕ → ℕ := fun n => a * D.q n + b * D.r n
  let P : ℕ → ℤ := fun n => (a : ℤ) * D.p n + (b : ℤ) * D.s n
  let err : ℕ → ℝ := fun n => |(Q n : ℝ) * α - (P n : ℝ)|
  have hQ : Tendsto Q atTop atTop := tendsto_atTop_mono (fun n => by
    dsimp [Q]
    calc D.q n = 1 * D.q n := by simp
         _ ≤ a * D.q n := Nat.mul_le_mul_right _ ha
         _ ≤ a * D.q n + b * D.r n := Nat.le_add_right _ _) D.q_growth
  have hlayers := layer_lower_bounds_of_diophantine α δ hα Q P hQ
  have hbounded : ∀ᶠ n in atTop, (Q n : ℝ) * err n ≤ ((a : ℝ) + b) ^ 2 :=
    Eventually.of_forall (D.combination_error_bound a b)
  have hratio : ∀ n, D.v n * (D.r n : ℤ_[2]) = -(D.q n : ℤ_[2]) :=
    fun n => unitRatio_mul _ _ (D.r_unit n)
  have hne := affine_limit_ne_zero D.q D.r D.v v₀ a b D.r_unit hratio hv
    err δ (((a : ℝ) + b) ^ 2) hδ hbounded hlayers
  apply joint_test_lower_bound hu hv a b (δ / 2) hne
  intro h
  filter_upwards [hlayers h] with n hn hnorm
  have hQnorm : ‖(Q n : ℤ_[2])‖ = (2 : ℝ) ^ (-(h : ℤ)) := by
    exact (normalized_combination_norm (D.q n) (D.r n) a b (D.v n)
      (D.r_unit n) (hratio n)).symm.trans hnorm
  have hdivZ : ((2 : ℤ) ^ h) ∣ (Q n : ℤ) :=
    PadicInt.norm_int_le_pow_iff_dvd.mp (by simpa using hQnorm.le)
  have hdiv : 2 ^ h ∣ Q n := by exact_mod_cast hdivZ
  have hlow := hn hdiv
  have hQf : (Q n : ℝ) * D.f n ≤ 2 * ((max a b : ℕ) : ℝ) := by
    have hrf : (D.r n : ℝ) * D.f n ≤ 1 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast D.r_le_q n) (D.f_nonneg n)).trans
        (D.q_mul_f_le_one n)
    have haq : (a : ℝ) * ((D.q n : ℝ) * D.f n) ≤ (a : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left (D.q_mul_f_le_one n) (Nat.cast_nonneg a)
    have hbr : (b : ℝ) * ((D.r n : ℝ) * D.f n) ≤ (b : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hrf (Nat.cast_nonneg b)
    have ham : (a : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast le_max_left a b
    have hbm : (b : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast le_max_right a b
    dsimp [Q]
    simp only [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hupper : (Q n : ℝ) * err n / (2 : ℝ) ^ h ≤
      2 * (((max a b : ℕ) : ℝ) * |(a : ℝ) * D.u n - (b : ℝ)| *
        (2 : ℝ) ^ (-(h : ℤ))) := by
    have herr : err n = D.f n * |(a : ℝ) * D.u n - (b : ℝ)| :=
      D.combination_error a b n
    rw [herr, ← mul_assoc]
    calc
      _ ≤ (2 * ((max a b : ℕ) : ℝ)) * |(a : ℝ) * D.u n - (b : ℝ)| /
          (2 : ℝ) ^ h := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hQf (abs_nonneg _)) (by positivity)
      _ = _ := by rw [zpow_neg, zpow_natCast]; ring
  linarith

end AdjacentApproximationData

/-- The concrete joint real/2-adic exceptional set in the rigidity theorem.
No dimension statement about this set is postulated here. -/
def JointBadlyApproximable (ε : ℝ) : Set (ℝ × ℤ_[2]) :=
  {w | w.1 ∈ Icc (0 : ℝ) 1 ∧ ∀ a b : ℕ, 1 ≤ a →
    ε ≤ ((max a b : ℕ) : ℝ) * |(a : ℝ) * w.1 - (b : ℝ)| *
      ‖(a : ℤ_[2]) * w.2 - (b : ℤ_[2])‖}

theorem jointBadlyApproximable_real_irrational {ε : ℝ} (hε : 0 < ε)
    {w : ℝ × ℤ_[2]} (hw : w ∈ JointBadlyApproximable ε) : Irrational w.1 := by
  rintro ⟨t, ht⟩
  have ht0 : 0 ≤ (t : ℝ) := by rw [ht]; exact hw.1.1
  have hnum : 0 ≤ t.num := Rat.num_nonneg.mpr (by exact_mod_cast ht0)
  have hnumcast : (t.num.toNat : ℝ) = (t.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have heq : (t.den : ℝ) * w.1 - (t.num.toNat : ℝ) = 0 := by
    rw [← ht, Rat.cast_def, hnumcast]
    field_simp
  have hb := hw.2 t.den t.num.toNat (Nat.one_le_iff_ne_zero.mpr t.den_ne_zero)
  rw [heq, abs_zero, mul_zero, zero_mul] at hb
  exact (not_le_of_gt hε) hb

namespace AdjacentApproximationData

variable {α : ℝ} (D : AdjacentApproximationData α)

/-- Restricting to any increasing subsequence preserves all the genuine
approximation identities and denominator-growth hypotheses. -/
def subseq (φ : ℕ → ℕ) (hφ : StrictMono φ) : AdjacentApproximationData α where
  q := D.q ∘ φ
  r := D.r ∘ φ
  p := D.p ∘ φ
  s := D.s ∘ φ
  u := D.u ∘ φ
  f := D.f ∘ φ
  σ := D.σ ∘ φ
  q_growth := D.q_growth.comp hφ.tendsto_atTop
  r_le_q := fun n => D.r_le_q (φ n)
  f_nonneg := fun n => D.f_nonneg (φ n)
  u_interval := fun n => D.u_interval (φ n)
  q_mul_f_le_one := fun n => D.q_mul_f_le_one (φ n)
  sign_abs := fun n => D.sign_abs (φ n)
  error_left := fun n => D.error_left (φ n)
  error_right := fun n => D.error_right (φ n)
  r_unit := fun n => D.r_unit (φ n)

/-- Compactness and the elementary arithmetic argument put a subsequential
limit in the actual joint exceptional set, with the explicit constant δ/2.
The assertion holds simultaneously for every test `(a,b)` because each
test is applied to the same already chosen convergent subsequence. -/
theorem exists_joint_badlyApproximable_limit {δ : ℝ} (hδ : 0 < δ)
    (hα : DyadicEventualLowerBound α δ) :
    ∃ w ∈ JointBadlyApproximable (δ / 2), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun n => (D.u (φ n), D.v (φ n))) atTop (𝓝 w) := by
  obtain ⟨w, hw, φ, hφ, ht⟩ := joint_compact_subsequence D.u D.v D.u_interval
  refine ⟨w, ⟨hw, ?_⟩, φ, hφ, ht⟩
  intro a b ha
  have hu : Tendsto (D.subseq φ hφ).u atTop (𝓝 w.1) := by
    simpa only [subseq, Function.comp_def] using (continuous_fst.tendsto w).comp ht
  have hv : Tendsto (D.subseq φ hφ).v atTop (𝓝 w.2) := by
    simpa only [subseq, v, Function.comp_def] using (continuous_snd.tendsto w).comp ht
  exact (D.subseq φ hφ).joint_limit_lower_bound hδ hα hu hv a b ha

end AdjacentApproximationData

end

end VV.P7AdicLimits
