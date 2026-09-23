import VV.P7AdicLimits
import VV.BBEKDyadic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The short-vector exclusion in BBEK Proposition 5.1 for p=2, including
the original four coordinates, dyadic integrality, and real sign bounds. -/

namespace VV.BBEKShortVector
open P7AdicLimits
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- With integral coordinates, an error smaller than one forces the
numerator to lie between zero and the positive denominator. -/
theorem integer_sign_bounds {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (a b : ℤ) (ha : 0 < a) (herr : |(a : ℝ) * u - (b : ℝ)| < 1) :
    0 ≤ b ∧ b ≤ a := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hau0 : 0 < (a : ℝ) * u := mul_pos har hu0
  have hau1 : (a : ℝ) * u < a := by nlinarith
  obtain ⟨helo,hehi⟩ := abs_lt.mp herr
  constructor
  · by_contra! hb
    have hb' : (b : ℝ) ≤ -1 := by exact_mod_cast (show b ≤ -1 by omega)
    linarith
  · by_contra! hb
    have hb' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    linarith

theorem integer_zero_of_small_error (u : ℝ) (b : ℤ)
    (herr : |(0 : ℝ) * u - (b : ℝ)| < 1) : b = 0 := by
  have habs : |(b : ℝ)| < 1 := by simpa using herr
  have hcast : |b| < (1 : ℤ) := by exact_mod_cast habs
  obtain ⟨_,_⟩ := abs_lt.mp hcast
  omega

/-- Convert the natural-number tests defining the concrete BBEK set to
positive/nonnegative integer tests. -/
theorem integer_test_lower_bound {ε u : ℝ} {v : ℤ_[2]}
    (h : (u,v) ∈ JointBadlyApproximable ε) (a b : ℤ) (ha : 0 < a) (hb : 0 ≤ b) :
    ε ≤ max (a : ℝ) (b : ℝ) * |(a : ℝ) * u - (b : ℝ)| *
      ‖(a : ℤ_[2]) * v - (b : ℤ_[2])‖ := by
  have haa : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha.le
  have hbb : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb
  have hh := h.2 a.toNat b.toNat (by omega)
  have haR : (a.toNat : ℝ) = a := by exact_mod_cast haa
  have hbR : (b.toNat : ℝ) = b := by exact_mod_cast hbb
  have haP : (a.toNat : ℤ_[2]) = a := by exact_mod_cast haa
  have hbP : (b.toNat : ℤ_[2]) = b := by exact_mod_cast hbb
  simpa only [Nat.cast_max, haR, hbR, haP, hbP] using hh

theorem positive_integer_test_lower_bound {ε u : ℝ} {v : ℤ_[2]}
    (h : (u,v) ∈ JointBadlyApproximable ε)
    (hu0 : 0 < u) (hu1 : u < 1) (a b : ℤ) (ha : 0 < a)
    (herr : |(a : ℝ) * u - (b : ℝ)| < 1) :
    ε ≤ |(a : ℝ)| * |(a : ℝ) * u - (b : ℝ)| *
      ‖(a : ℤ_[2]) * v - (b : ℤ_[2])‖ := by
  obtain ⟨hb0,hba⟩ := integer_sign_bounds hu0 hu1 a b ha herr
  have hh := integer_test_lower_bound h a b ha hb0
  rw [max_eq_left (by exact_mod_cast hba)] at hh
  simpa only [abs_of_nonneg (by exact_mod_cast ha.le : (0 : ℝ) ≤ a)] using hh

/-- Normalize the sign of a nonzero integral pair. The strict real error
bound guarantees the nonnegative second coordinate required by BBEK. -/
theorem signed_integer_test_lower_bound {ε u : ℝ} {v : ℤ_[2]}
    (h : (u,v) ∈ JointBadlyApproximable ε)
    (hu0 : 0 < u) (hu1 : u < 1) (a b : ℤ) (ha : a ≠ 0)
    (herr : |(a : ℝ) * u - (b : ℝ)| < 1) :
    ε ≤ |(a : ℝ)| * |(a : ℝ) * u - (b : ℝ)| *
      ‖(a : ℤ_[2]) * v - (b : ℤ_[2])‖ := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have herr' : |((-a : ℤ) : ℝ) * u - ((-b : ℤ) : ℝ)| < 1 := by
      simpa only [Int.cast_neg, neg_mul, neg_sub_neg, abs_sub_comm] using herr
    have hh := positive_integer_test_lower_bound h hu0 hu1 (-a) (-b) (by omega) herr'
    have heqR : ((-a : ℤ) : ℝ) * u - ((-b : ℤ) : ℝ) =
        -((a : ℝ) * u - (b : ℝ)) := by push_cast; ring
    have heqP : ((-a : ℤ) : ℤ_[2]) * v - ((-b : ℤ) : ℤ_[2]) =
        -((a : ℤ_[2]) * v - (b : ℤ_[2])) := by push_cast; ring
    rw [heqR, heqP] at hh
    simpa only [Int.cast_neg, abs_neg, norm_neg] using hh
  · exact positive_integer_test_lower_bound h hu0 hu1 a b ha herr

theorem joint_real_mem_Ioo {ε u : ℝ} {v : ℤ_[2]} (hε : 0 < ε)
    (h : (u,v) ∈ JointBadlyApproximable ε) : u ∈ Set.Ioo (0 : ℝ) 1 := by
  have hi := jointBadlyApproximable_real_irrational hε h
  have h0 : u ≠ 0 := by simpa using hi.ne_int 0
  have h1 : u ≠ 1 := by simpa using hi.ne_int 1
  exact ⟨lt_of_le_of_ne h.1.1 h0.symm, lt_of_le_of_ne h.1.2 h1⟩

/-- Three strictly short normalized coordinates contradict the BBEK test.
The additional p-adic first-coordinate condition is only needed upstream
to establish integrality. Integer sign bounds even yield δ³, rather than
the weaker paper estimate 2δ³. -/
theorem no_integer_short_vector {ε u : ℝ} {v : ℤ_[2]}
    (h : (u,v) ∈ JointBadlyApproximable ε) (hu0 : 0 < u) (hu1 : u < 1)
    (A B P δ : ℝ) (hA : 0 < A) (hB : 1 ≤ B) (hP : 0 < P)
    (hscale : A * B * P = 1) (_hδ0 : 0 < δ) (hδ1 : δ < 1) (hδε : δ ^ 3 ≤ ε)
    (a b : ℤ) (hne : a ≠ 0 ∨ b ≠ 0)
    (hshortA : A * |(a : ℝ)| < δ)
    (hshortB : B * |(a : ℝ) * u - (b : ℝ)| < δ)
    (hshortP : P * ‖(a : ℤ_[2]) * v - (b : ℤ_[2])‖ < δ) : False := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have herr : |(a : ℝ) * u - (b : ℝ)| < 1 := by
    have hh := mul_le_mul_of_nonneg_right hB (abs_nonneg ((a : ℝ) * u - (b : ℝ)))
    nlinarith
  have ha : a ≠ 0 := by
    intro ha
    subst a
    have hb := integer_zero_of_small_error u b (by simpa using herr)
    exact hne.elim (fun h => h rfl) (fun h => h hb)
  have hlower := signed_integer_test_lower_bound h hu0 hu1 a b ha herr
  have hpair : (A * |(a : ℝ)|) * (B * |(a : ℝ) * u - (b : ℝ)|) < δ * δ :=
    mul_lt_mul'' hshortA hshortB (mul_nonneg hA.le (abs_nonneg _))
      (mul_nonneg hB0.le (abs_nonneg _))
  have htriple : ((A * |(a : ℝ)|) * (B * |(a : ℝ) * u - (b : ℝ)|)) *
      (P * ‖(a : ℤ_[2]) * v - (b : ℤ_[2])‖) < (δ * δ) * δ :=
    mul_lt_mul'' hpair hshortP
      (mul_nonneg (mul_nonneg hA.le (abs_nonneg _)) (mul_nonneg hB0.le (abs_nonneg _)))
      (mul_nonneg hP.le (norm_nonneg _))
  have hid : ((A * |(a : ℝ)|) * (B * |(a : ℝ) * u - (b : ℝ)|)) *
      (P * ‖(a : ℤ_[2]) * v - (b : ℤ_[2])‖) =
      |(a : ℝ)| * |(a : ℝ) * u - (b : ℝ)| * ‖(a : ℤ_[2]) * v - (b : ℤ_[2])‖ := by
    calc
      _ = (A * B * P) * (|(a : ℝ)| * |(a : ℝ) * u - (b : ℝ)| *
          ‖(a : ℤ_[2]) * v - (b : ℤ_[2])‖) := by ring
      _ = _ := by rw [hscale, one_mul]
  rw [hid] at htriple
  nlinarith

noncomputable def shortRadius (ε : ℝ) : ℝ := (ε / 2) ^ (1 / 3 : ℝ)

theorem shortRadius_pos {ε : ℝ} (hε : 0 < ε) : 0 < shortRadius ε := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem shortRadius_lt_one {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) : shortRadius ε < 1 := by
  exact Real.rpow_lt_one (by positivity) (by linarith) (by norm_num)

theorem shortRadius_cube {ε : ℝ} (hε : 0 ≤ ε) : (shortRadius ε) ^ 3 = ε / 2 := by
  unfold shortRadius
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num

theorem normalized_scales (t : ℝ) (n : ℕ) (hcone : (2 : ℝ) ^ n ≤ Real.exp t) :
    let A := Real.exp (-t) / (2 : ℝ) ^ n
    let B := Real.exp t / (2 : ℝ) ^ n
    let P := (2 : ℝ) ^ (2 * n)
    0 < A ∧ 1 ≤ B ∧ 1 ≤ P ∧ A ≤ B ∧ A * B * P = 1 := by
  dsimp only
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hp1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have he1 : 1 ≤ Real.exp t := hp1.trans hcone
  have ht : 0 ≤ t := Real.one_le_exp_iff.mp he1
  refine ⟨by positivity, (one_le_div hp).mpr hcone, one_le_pow₀ (by norm_num), ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hp.le
  · rw [Real.exp_neg, Nat.mul_comm 2 n, pow_mul]
    have he : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
    field_simp
    ring

/-- Norm of the actual normalized p-adic fourth coordinate. -/
theorem normalized_padic_norm (n : ℕ) (z : ℚ_[2]) :
    ‖(2 : ℚ_[2]) ^ (-((2 * n : ℕ) : ℤ)) * z‖ = (2 : ℝ) ^ (2 * n) * ‖z‖ := by
  have hn : ‖(2 : ℚ_[2]) ^ (-((2 * n : ℕ) : ℤ))‖ = (2 : ℝ) ^ (2 * n) := by
    simpa using padicNormE.norm_p_zpow (p := 2) (-((2 * n : ℕ) : ℤ))
  rw [norm_mul, hn]

/-- The actual exponential/dyadic normalization excludes all integral
coefficient pairs, including the real endpoint cases through the BBEK
test-set hypothesis itself. -/
theorem no_normalized_integer_short_vector {ε u : ℝ} {v : ℤ_[2]}
    (hε0 : 0 < ε) (hε1 : ε < 1) (h : (u,v) ∈ JointBadlyApproximable ε)
    (t : ℝ) (n : ℕ) (hcone : (2 : ℝ) ^ n ≤ Real.exp t)
    (a b : ℤ) (hne : a ≠ 0 ∨ b ≠ 0)
    (hfirst : |(Real.exp (-t) / (2 : ℝ) ^ n) * (a : ℝ)| < shortRadius ε)
    (hsecond : |(Real.exp t / (2 : ℝ) ^ n) * ((a : ℝ) * u - (b : ℝ))| < shortRadius ε)
    (hfourth : ‖(2 : ℚ_[2]) ^ (-((2 * n : ℕ) : ℤ)) *
      ((a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2]))‖ < shortRadius ε) : False := by
  obtain ⟨hA,hB,hP,_,hscale⟩ := normalized_scales t n hcone
  obtain ⟨hu0,hu1⟩ := joint_real_mem_Ioo hε0 h
  apply no_integer_short_vector h hu0 hu1
    (Real.exp (-t) / (2 : ℝ) ^ n) (Real.exp t / (2 : ℝ) ^ n)
    ((2 : ℝ) ^ (2 * n)) (shortRadius ε)
    hA hB (by positivity) hscale (shortRadius_pos hε0)
    (shortRadius_lt_one hε0 hε1) (by rw [shortRadius_cube hε0.le]; linarith)
    a b hne
  · simpa only [abs_mul, abs_of_pos hA] using hfirst
  · simpa only [abs_mul, abs_of_pos (lt_of_lt_of_le zero_lt_one hB)] using hsecond
  · rw [normalized_padic_norm] at hfourth
    simpa only [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_intCast] using hfourth

/-- The complete normalized short-vector exclusion from Proposition 5.1.
The two coefficients start in the actual dyadic subring of Q. Their
integrality is derived from the two p-adic short-coordinate inequalities,
then the integer theorem supplies the contradiction. -/
theorem no_normalized_dyadic_short_vector {ε u : ℝ} {v : ℤ_[2]}
    (hε0 : 0 < ε) (hε1 : ε < 1) (h : (u,v) ∈ JointBadlyApproximable ε)
    (t : ℝ) (n : ℕ) (hcone : (2 : ℝ) ^ n ≤ Real.exp t)
    (a b : ℚ) (ha : a ∈ BBEKDyadic.dyadic) (hb : b ∈ BBEKDyadic.dyadic)
    (hne : a ≠ 0 ∨ b ≠ 0)
    (hfirst : |(Real.exp (-t) / (2 : ℝ) ^ n) * (a : ℝ)| < shortRadius ε)
    (hsecond : |(Real.exp t / (2 : ℝ) ^ n) * ((a : ℝ) * u - (b : ℝ))| < shortRadius ε)
    (hthird : ‖(a : ℚ_[2])‖ < shortRadius ε)
    (hfourth : ‖(2 : ℚ_[2]) ^ (-((2 * n : ℕ) : ℤ)) *
      ((a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2]))‖ < shortRadius ε) : False := by
  have hδ1 := shortRadius_lt_one hε0 hε1
  have haNorm : ‖(a : ℚ_[2])‖ ≤ 1 := hthird.le.trans hδ1.le
  have hresidual : ‖(a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2])‖ ≤ 1 := by
    have hp : (1 : ℝ) ≤ 2 ^ (2 * n) := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hp
      (norm_nonneg ((a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2])))
    have hf := hfourth
    rw [normalized_padic_norm] at hf
    calc
      _ ≤ (2 : ℝ) ^ (2 * n) * ‖(a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2])‖ := by simpa using hh
      _ ≤ shortRadius ε := hf.le
      _ ≤ 1 := hδ1.le
  obtain ⟨m,k,rfl,rfl⟩ := BBEKDyadic.dyadic_pair_integral ha hb v haNorm hresidual
  apply no_normalized_integer_short_vector hε0 hε1 h t n hcone m k
  · exact_mod_cast hne
  · simpa only [Rat.cast_intCast] using hfirst
  · simpa only [Rat.cast_intCast] using hsecond
  · simpa only [Rat.cast_intCast] using hfourth

/-- The same result with the paper's integer cone coordinate and zpow
normalization, ready to connect to the actual homogeneous action. -/
theorem no_normalized_dyadic_short_vector_zpow {ε u : ℝ} {v : ℤ_[2]}
    (hε0 : 0 < ε) (hε1 : ε < 1) (h : (u,v) ∈ JointBadlyApproximable ε)
    (t : ℝ) (n : ℤ) (hn : 0 ≤ n) (hcone : (2 : ℝ) ^ n ≤ Real.exp t)
    (a b : ℚ) (ha : a ∈ BBEKDyadic.dyadic) (hb : b ∈ BBEKDyadic.dyadic)
    (hne : a ≠ 0 ∨ b ≠ 0)
    (hfirst : |Real.exp (-t) * (2 : ℝ) ^ (-n) * (a : ℝ)| < shortRadius ε)
    (hsecond : |Real.exp t * (2 : ℝ) ^ (-n) * ((a : ℝ) * u - (b : ℝ))| < shortRadius ε)
    (hthird : ‖(a : ℚ_[2])‖ < shortRadius ε)
    (hfourth : ‖(2 : ℚ_[2]) ^ (-(2 * n)) *
      ((a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2]))‖ < shortRadius ε) : False := by
  have hnat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ n.toNat := by
    conv_lhs => rw [← hnat]
    rw [zpow_natCast]
  have hneg : (2 : ℝ) ^ (-n) = ((2 : ℝ) ^ n.toNat)⁻¹ := by rw [zpow_neg, hpow]
  have hdouble : ((2 * n.toNat : ℕ) : ℤ) = 2 * n := by push_cast; rw [hnat]
  apply no_normalized_dyadic_short_vector hε0 hε1 h t n.toNat
    (by rwa [← hpow]) a b ha hb hne
  · simpa only [hneg, div_eq_mul_inv] using hfirst
  · simpa only [hneg, div_eq_mul_inv] using hsecond
  · exact hthird
  · simpa only [hdouble] using hfourth

/-- A nonempty positive-parameter BBEK test set forces its parameter
strictly below one; this is not an additional hypothesis of Proposition 5.1. -/
theorem joint_parameter_lt_one {ε u : ℝ} {v : ℤ_[2]} (hε : 0 < ε)
    (h : (u,v) ∈ JointBadlyApproximable ε) : ε < 1 := by
  obtain ⟨hu0,hu1⟩ := joint_real_mem_Ioo hε h
  have ht := h.2 1 0 (by norm_num)
  have hlower : ε ≤ u * ‖v‖ := by
    simpa [abs_of_pos hu0] using ht
  have hupper : u * ‖v‖ ≤ u := by
    simpa using mul_le_mul_of_nonneg_left (PadicInt.norm_le_one v) hu0.le
  exact (hlower.trans hupper).trans_lt hu1

/-- Proposition 5.1 in the original, unnormalized lattice coordinates.
Multiplying both dyadic coefficients by 2^n gives the previously proved
normalization. All four short-coordinate inequalities are used. -/
theorem no_dyadic_short_vector {ε u : ℝ} {v : ℤ_[2]}
    (hε : 0 < ε) (h : (u,v) ∈ JointBadlyApproximable ε)
    (t : ℝ) (n : ℕ) (hcone : (2 : ℝ) ^ n ≤ Real.exp t)
    (a b : ℚ) (ha : a ∈ BBEKDyadic.dyadic) (hb : b ∈ BBEKDyadic.dyadic)
    (hne : a ≠ 0 ∨ b ≠ 0)
    (hfirst : |Real.exp (-t) * (a : ℝ)| < shortRadius ε)
    (hsecond : |Real.exp t * ((a : ℝ) * u - (b : ℝ))| < shortRadius ε)
    (hthird : ‖(2 : ℚ_[2]) ^ n * (a : ℚ_[2])‖ < shortRadius ε)
    (hfourth : ‖(2 : ℚ_[2]) ^ (-(n : ℤ)) *
      ((a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2]))‖ < shortRadius ε) : False := by
  have h2 : (2 : ℚ) ∈ BBEKDyadic.dyadic := by
    simpa using BBEKDyadic.int_mem_dyadic 2
  have hpow : (2 : ℚ) ^ n ∈ BBEKDyadic.dyadic := BBEKDyadic.dyadic.pow_mem h2 n
  have hnonzero : (2 : ℚ) ^ n * a ≠ 0 ∨ (2 : ℚ) ^ n * b ≠ 0 := by
    rcases hne with ha | hb
    · exact Or.inl (mul_ne_zero (pow_ne_zero n (by norm_num)) ha)
    · exact Or.inr (mul_ne_zero (pow_ne_zero n (by norm_num)) hb)
  apply no_normalized_dyadic_short_vector hε (joint_parameter_lt_one hε h) h t n hcone
    ((2 : ℚ) ^ n * a) ((2 : ℚ) ^ n * b)
    (BBEKDyadic.dyadic.mul_mem hpow ha) (BBEKDyadic.dyadic.mul_mem hpow hb) hnonzero
  · convert hfirst using 1
    push_cast
    congr 1
    field_simp
    ring
  · convert hsecond using 1
    push_cast
    congr 1
    field_simp
    ring
  · simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using hthird
  · have hp : (2 : ℚ_[2]) ^ (-((2 * n : ℕ) : ℤ)) * (2 : ℚ_[2]) ^ n =
        (2 : ℚ_[2]) ^ (-(n : ℤ)) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      push_cast
      ring
    have heq : (2 : ℚ_[2]) ^ (-((2 * n : ℕ) : ℤ)) *
        (((2 : ℚ_[2]) ^ n * (a : ℚ_[2])) * (v : ℚ_[2]) -
          (2 : ℚ_[2]) ^ n * (b : ℚ_[2])) =
        (2 : ℚ_[2]) ^ (-(n : ℤ)) * ((a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2])) := by
      calc
        _ = ((2 : ℚ_[2]) ^ (-((2 * n : ℕ) : ℤ)) * (2 : ℚ_[2]) ^ n) *
            ((a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2])) := by ring
        _ = _ := by rw [hp]
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, heq] using hfourth

/-- The original lattice-coordinate statement with the integer parameter
used by the diagonal action and its positive cone. -/
theorem no_dyadic_short_vector_zpow {ε u : ℝ} {v : ℤ_[2]}
    (hε : 0 < ε) (h : (u,v) ∈ JointBadlyApproximable ε)
    (t : ℝ) (n : ℤ) (hn : 0 ≤ n) (hcone : (2 : ℝ) ^ n ≤ Real.exp t)
    (a b : ℚ) (ha : a ∈ BBEKDyadic.dyadic) (hb : b ∈ BBEKDyadic.dyadic)
    (hne : a ≠ 0 ∨ b ≠ 0)
    (hfirst : |Real.exp (-t) * (a : ℝ)| < shortRadius ε)
    (hsecond : |Real.exp t * ((a : ℝ) * u - (b : ℝ))| < shortRadius ε)
    (hthird : ‖(2 : ℚ_[2]) ^ n * (a : ℚ_[2])‖ < shortRadius ε)
    (hfourth : ‖(2 : ℚ_[2]) ^ (-n) *
      ((a : ℚ_[2]) * (v : ℚ_[2]) - (b : ℚ_[2]))‖ < shortRadius ε) : False := by
  have hnat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  have hpowR : (2 : ℝ) ^ n = (2 : ℝ) ^ n.toNat := by
    conv_lhs => rw [← hnat]
    rw [zpow_natCast]
  have hpowP : (2 : ℚ_[2]) ^ n = (2 : ℚ_[2]) ^ n.toNat := by
    conv_lhs => rw [← hnat]
    rw [zpow_natCast]
  apply no_dyadic_short_vector hε h t n.toNat (by rwa [← hpowR]) a b ha hb hne
    hfirst hsecond
  · simpa only [hpowP] using hthird
  · simpa only [hnat] using hfourth

end VV.BBEKShortVector
