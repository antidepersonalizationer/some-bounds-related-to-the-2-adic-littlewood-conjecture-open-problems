import VV.P7AdicLimits
import VV.P7Approximation

/-! Construct the arithmetic joint-limit data from actual continued fractions. -/

open Filter Set
open scoped Topology

namespace VV.P7Convergents
open P5Period P7Approximation P7AdicLimits

noncomputable section
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem matrix_append_digit (w : List ℤ) (z : ℤ) :
    matrix (w ++ [z]) =
      ⟨(matrix w).a * z + (matrix w).b, (matrix w).a,
       (matrix w).c * z + (matrix w).d, (matrix w).c⟩ := by
  induction w with
  | nil => simp [matrix, prepend, identity]
  | cons a w ih =>
    simp only [List.cons_append, matrix, ih, prepend]
    congr 1; ring

theorem digitBlock_snoc (x : ℝ) (m n : ℕ) :
    digitBlock x m (n + 1) = digitBlock x m n ++ [partialQuotient x (m + n)] := by
  induction n generalizing m with
  | zero => simp [digitBlock]
  | succ n ih =>
    change partialQuotient x m :: digitBlock x (m + 1) (n + 1) =
      (partialQuotient x m :: digitBlock x (m + 1) n) ++
        [partialQuotient x (m + (n + 1))]
    rw [ih (m + 1)]
    simp only [List.cons_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def prefixMatrix (x : ℝ) (n : ℕ) : PrefixMatrix := matrix (digitBlock x 0 (n + 1))

theorem prefix_succ (x : ℝ) (n : ℕ) :
    prefixMatrix x (n + 1) =
      ⟨(prefixMatrix x n).a * partialQuotient x (n + 1) + (prefixMatrix x n).b,
       (prefixMatrix x n).a,
       (prefixMatrix x n).c * partialQuotient x (n + 1) + (prefixMatrix x n).d,
       (prefixMatrix x n).c⟩ := by
  simp only [prefixMatrix, digitBlock_snoc x 0 (n + 1), Nat.zero_add, matrix_append_digit]

theorem matrix_column_compare (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a) :
    (matrix w).c ≤ (matrix w).a := by
  cases w with
  | nil => norm_num [matrix, identity]
  | cons a w =>
    have ha := hw a (by simp)
    have hpos := matrix_positive w (fun b hb => hw b (by simp [hb]))
    dsimp [matrix, prepend]
    nlinarith [hpos.1, hpos.2.2.1]

theorem matrix_size_lower (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a) :
    (w.length : ℤ) + 1 ≤ (matrix w).a + (matrix w).c := by
  induction w with
  | nil => norm_num [matrix, identity]
  | cons a w ih =>
    have ha := hw a (by simp)
    have htail : ∀ b ∈ w, 1 ≤ b := fun b hb => hw b (by simp [hb])
    have hi := ih htail
    have hA := (matrix_positive w htail).1
    simp only [matrix, prepend, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem prefix_den_growth_bound {x : ℝ} (hx : Irrational x) (n : ℕ) :
    n + 1 ≤ 2 * (prefixMatrix x n).c.toNat := by
  have hpos := digitBlock_positive hx 1 n (by omega)
  have hs := matrix_size_lower (digitBlock x 1 n) hpos
  have hc := matrix_column_compare (digitBlock x 1 n) hpos
  rw [digitBlock_length] at hs
  have hnonneg : 0 ≤ (prefixMatrix x n).c := (prefix_den_positive hx n).le
  have hh : (n : ℤ) + 1 ≤ 2 * (prefixMatrix x n).c := by
    change (n : ℤ) + 1 ≤ 2 * (matrix (digitBlock x 1 n)).a
    omega
  exact_mod_cast (show ((n + 1 : ℕ) : ℤ) ≤ 2 * ((prefixMatrix x n).c.toNat : ℤ) by
    simpa only [Int.toNat_of_nonneg hnonneg, Nat.cast_add, Nat.cast_one] using hh)

theorem prefix_den_tendsto {x : ℝ} (hx : Irrational x) :
    Tendsto (fun n => (prefixMatrix x n).c.toNat) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2 * b)] with n hn
  have hg := prefix_den_growth_bound hx n
  omega

theorem prefix_one_den_odd (x : ℝ) (n : ℕ) :
    ¬ (2 : ℤ) ∣ (prefixMatrix x n).c ∨ ¬ (2 : ℤ) ∣ (prefixMatrix x n).d := by
  by_contra! h
  have hdvd : (2 : ℤ) ∣
      (prefixMatrix x n).a * (prefixMatrix x n).d - (prefixMatrix x n).b * (prefixMatrix x n).c :=
    dvd_sub (dvd_mul_of_dvd_right h.2 _) (dvd_mul_of_dvd_right h.1 _)
  have hdet : (prefixMatrix x n).a * (prefixMatrix x n).d -
      (prefixMatrix x n).b * (prefixMatrix x n).c = (-1 : ℤ) ^ (n + 1) := by
    simpa only [prefixMatrix, digitBlock_length] using matrix_det (digitBlock x 0 (n + 1))
  rw [hdet] at hdvd
  rcases neg_one_pow_eq_or ℤ (n + 1) with he | he <;> rw [he] at hdvd <;> norm_num at hdvd

theorem exists_odd_previous_subsequence (x : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, ¬ (2 : ℤ) ∣ (prefixMatrix x (φ n)).d := by
  apply extraction_of_frequently_atTop (P := fun n => ¬ (2 : ℤ) ∣ (prefixMatrix x n).d)
  rw [frequently_atTop]
  intro N
  by_cases hd : (2 : ℤ) ∣ (prefixMatrix x N).d
  · refine ⟨N + 1, by omega, ?_⟩
    have hc := (prefix_one_den_odd x N).resolve_right (not_not_intro hd)
    simpa only [prefix_succ] using hc
  · exact ⟨N, le_rfl, hd⟩

theorem odd_nat_padic_norm (r : ℤ) (hr0 : 0 ≤ r) (hr : ¬ (2 : ℤ) ∣ r) :
    ‖(r.toNat : ℤ_[2])‖ = 1 := by
  apply le_antisymm (PadicInt.norm_le_one _)
  apply le_of_not_gt
  intro h
  apply hr
  apply (PadicInt.norm_int_lt_one_iff_dvd r).mp
  have hcast : (r.toNat : ℤ_[2]) = (r : ℤ_[2]) := by
    exact_mod_cast Int.toNat_of_nonneg hr0
  rwa [← hcast]

theorem prefix_error_identities {x : ℝ} (hx : Irrational x) (n : ℕ) :
    let M := prefixMatrix x n
    let t := completeQuotient x (n + 1)
    let d := (M.c : ℝ) * t + M.d
    (M.c : ℝ) * x - M.a = -((M.a : ℝ) * M.d - (M.b : ℝ) * M.c) / d ∧
    (M.d : ℝ) * x - M.b = ((M.a : ℝ) * M.d - (M.b : ℝ) * M.c) * t / d := by
  dsimp only
  let M := prefixMatrix x n
  let t := completeQuotient x (n + 1)
  have hc : (0 : ℝ) < M.c := by exact_mod_cast prefix_den_positive hx n
  have hd : (0 : ℝ) ≤ M.d := by exact_mod_cast (prefix_previous_den_bounds hx n).1
  have ht : 0 < t := lt_trans zero_lt_one (one_lt_completeQuotient_succ hx n)
  have hden : (M.c : ℝ) * t + M.d ≠ 0 := (by positivity : 0 < (M.c : ℝ) * t + M.d).ne'
  have hr : x * ((M.c : ℝ) * t + M.d) = (M.a : ℝ) * t + M.b :=
    by simpa only [Nat.zero_add] using
      digitBlock_realizes hx 0 (n + 1)
  constructor
  · apply (eq_div_iff hden).mpr
    linear_combination (M.c : ℝ) * hr
  · apply (eq_div_iff hden).mpr
    linear_combination (M.d : ℝ) * hr

/-- All arithmetic data in the 2-adic limit theorem, now built from the
actual prefixMatrix matrices and complete quotients of `x`. -/
def ofCF {x : ℝ} (hx : Irrational x) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hodd : ∀ n, ¬ (2 : ℤ) ∣ (prefixMatrix x (φ n)).d) : AdjacentApproximationData x := by
  let M : ℕ → PrefixMatrix := fun n => prefixMatrix x (φ n)
  let t : ℕ → ℝ := fun n => completeQuotient x (φ n + 1)
  let den : ℕ → ℝ := fun n => (M n).c * t n + (M n).d
  have hc : ∀ n, (0 : ℝ) < (M n).c := fun n => by
    exact_mod_cast prefix_den_positive hx (φ n)
  have hd : ∀ n, (0 : ℝ) ≤ (M n).d := fun n => by
    exact_mod_cast (prefix_previous_den_bounds hx (φ n)).1
  have ht : ∀ n, 1 < t n := fun n => one_lt_completeQuotient_succ hx (φ n)
  have ht0 : ∀ n, 0 < t n := fun n => lt_trans zero_lt_one (ht n)
  have hden : ∀ n, 0 < den n := fun n => add_pos_of_pos_of_nonneg
    (mul_pos (hc n) (ht0 n)) (hd n)
  have hcCast : ∀ n, ((M n).c.toNat : ℝ) = (M n).c := fun n => by
    exact_mod_cast Int.toNat_of_nonneg (prefix_den_positive hx (φ n)).le
  have hdCast : ∀ n, ((M n).d.toNat : ℝ) = (M n).d := fun n => by
    exact_mod_cast Int.toNat_of_nonneg (prefix_previous_den_bounds hx (φ n)).1
  refine {
    q := fun n => (M n).c.toNat
    r := fun n => (M n).d.toNat
    p := fun n => (M n).a
    s := fun n => (M n).b
    u := fun n => (t n)⁻¹
    f := fun n => t n / den n
    σ := fun n => -((M n).a * (M n).d - (M n).b * (M n).c : ℝ)
    q_growth := (prefix_den_tendsto hx).comp hφ.tendsto_atTop
    r_le_q := fun n => Int.toNat_le_toNat (prefix_previous_den_bounds hx (φ n)).2
    f_nonneg := fun n => (div_pos (ht0 n) (hden n)).le
    u_interval := fun n => ⟨inv_nonneg.mpr (ht0 n).le, (inv_le_one₀ (ht0 n)).mpr (ht n).le⟩
    q_mul_f_le_one := ?_
    sign_abs := ?_
    error_left := ?_
    error_right := ?_
    r_unit := fun n => odd_nat_padic_norm (M n).d
      (prefix_previous_den_bounds hx (φ n)).1 (hodd n)
  }
  · intro n
    rw [hcCast, ← mul_div_assoc]
    apply (div_le_one (hden n)).mpr
    exact le_add_of_nonneg_right (hd n)
  · intro n
    have hdet : ((M n).a : ℝ) * (M n).d - (M n).b * (M n).c =
        (-1 : ℝ) ^ (φ n + 1) := by
      exact_mod_cast (show (M n).a * (M n).d - (M n).b * (M n).c =
          (-1 : ℤ) ^ (φ n + 1) by
        simpa only [M, prefixMatrix, digitBlock_length] using matrix_det (digitBlock x 0 (φ n + 1)))
    rw [abs_neg, hdet, abs_neg_one_pow]
  · intro n
    rw [hcCast]
    have he := (prefix_error_identities hx (φ n)).1
    change ((M n).c : ℝ) * x - (M n).a = _ at he
    rw [he]
    change -((M n).a * (M n).d - (M n).b * (M n).c : ℝ) / den n =
      -((M n).a * (M n).d - (M n).b * (M n).c : ℝ) * (t n / den n) * (t n)⁻¹
    field_simp [(hden n).ne', (ht0 n).ne']
    ring
  · intro n
    rw [hdCast]
    have he := (prefix_error_identities hx (φ n)).2
    change ((M n).d : ℝ) * x - (M n).b = _ at he
    rw [he]
    dsimp only [den, t, M]
    ring

theorem ofCF_u {x : ℝ} (hx : Irrational x) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hodd : ∀ n, ¬ (2 : ℤ) ∣ (prefixMatrix x (φ n)).d) (n : ℕ) :
    (ofCF hx φ hφ hodd).u n = CylinderGeometry.tail x (φ n) := by
  change (completeQuotient x (φ n + 1))⁻¹ = _
  simp only [completeQuotient, inv_inv, CylinderGeometry.tail]

/-- Every irrational input supplies a genuine continued-fraction sequence
to the joint-limit argument; the odd previous-denominator subsequence is
constructed rather than assumed. -/
theorem exists_cf_data {x : ℝ} (hx : Irrational x) :
    ∃ (D : AdjacentApproximationData x) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ n, D.u n = CylinderGeometry.tail x (φ n) := by
  obtain ⟨φ, hφ, hodd⟩ := exists_odd_previous_subsequence x
  exact ⟨ofCF hx φ hφ hodd, φ, hφ, ofCF_u hx φ hφ hodd⟩

theorem dyadicLowerBound_of_orbit {x : ℝ} (hx : Irrational x)
    (C : ℕ) (hC : BOrbitBound x C) :
    DyadicEventualLowerBound x (1 / ((C : ℝ) + 3)) := by
  intro h
  exact eventual_lower_bound_of_digits (irrational_dyadic_mul hx h) C (hC h)

/-- Any joint limit along odd previous denominators of the actual continued
fraction lies in the concrete BBEK test set. This theorem has no approximation
or entropy hypothesis: its only bound is the original `BOrbitBound`. -/
theorem cf_joint_limit_mem {x : ℝ} (hx : Irrational x) (C : ℕ)
    (hC : BOrbitBound x C) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hodd : ∀ n, ¬ (2 : ℤ) ∣ (prefixMatrix x (φ n)).d)
    {w : ℝ × ℤ_[2]}
    (hw : Tendsto (fun n =>
      (CylinderGeometry.tail x (φ n),
       unitRatio (prefixMatrix x (φ n)).c.toNat (prefixMatrix x (φ n)).d.toNat))
      atTop (𝓝 w)) :
    w ∈ JointBadlyApproximable ((1 / ((C : ℝ) + 3)) / 2) := by
  let D := ofCF hx φ hφ hodd
  have hu : Tendsto D.u atTop (𝓝 w.1) := by
    have heq : D.u = fun n => CylinderGeometry.tail x (φ n) :=
      funext (ofCF_u hx φ hφ hodd)
    rw [heq]
    exact (continuous_fst.tendsto w).comp hw
  have hv : Tendsto D.v atTop (𝓝 w.2) :=
    (continuous_snd.tendsto w).comp hw
  refine ⟨?_, fun a b ha => D.joint_limit_lower_bound (by positivity)
    (dyadicLowerBound_of_orbit hx C hC) hu hv a b ha⟩
  exact isClosed_Icc.mem_of_tendsto hu (Eventually.of_forall D.u_interval)

/-- Every point in the original exceptional set has actual tail joint
limits satisfying all BBEK test inequalities with a positive explicit
constant. This completes the arithmetic and 2-adic limit part of the route. -/
theorem exists_cf_joint_limit {x : ℝ} (hx : Irrational x) (C : ℕ)
    (hC : BOrbitBound x C) :
    ∃ w ∈ JointBadlyApproximable ((1 / ((C : ℝ) + 3)) / 2),
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        (∀ n, ¬ (2 : ℤ) ∣ (prefixMatrix x (ψ n)).d) ∧
        Tendsto (fun n =>
          (CylinderGeometry.tail x (ψ n),
           unitRatio (prefixMatrix x (ψ n)).c.toNat (prefixMatrix x (ψ n)).d.toNat))
          atTop (𝓝 w) := by
  obtain ⟨φ, hφ, hodd⟩ := exists_odd_previous_subsequence x
  let D := ofCF hx φ hφ hodd
  obtain ⟨w, hw, θ, hθ, ht⟩ := D.exists_joint_badlyApproximable_limit
    (by positivity : 0 < 1 / ((C : ℝ) + 3)) (dyadicLowerBound_of_orbit hx C hC)
  refine ⟨w, hw, φ ∘ θ, hφ.comp hθ, fun n => hodd (θ n), ?_⟩
  have heq : (fun n => (D.u (θ n), D.v (θ n))) =
      (fun n => (CylinderGeometry.tail x ((φ ∘ θ) n),
       unitRatio (prefixMatrix x ((φ ∘ θ) n)).c.toNat
         (prefixMatrix x ((φ ∘ θ) n)).d.toNat)) := by
    funext n
    exact Prod.ext (ofCF_u hx φ hφ hodd (θ n)) rfl
  rwa [← heq]

end
end VV.P7Convergents
