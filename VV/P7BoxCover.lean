import VV.P7RigidityReduction

/-!
The elementary quantitative conversion from zero upper box dimension,
expressed by its geometric covering characterization, to the specific
continued-fraction scales. No rigidity theorem is admitted in this file.
-/

open Set Filter
open scoped Topology NNReal ENNReal

namespace VV.P7BoxCover
open P7AdicLimits P7TailLimits P7RigidityReduction

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The geometric covering formulation of zero upper box dimension:
at any fixed exponentially shrinking scale, the covering number grows
more slowly than every prescribed exponential rate greater than one. -/
def GeometricZeroUpperBox {X : Type*} [PseudoMetricSpace X] (S : Set X) : Prop :=
  ∀ ρ t : ℝ, 0 < ρ → ρ < 1 → 1 < t → ∀ᶠ n : ℕ in atTop,
    ∃ (m : ℕ) (U : Fin m → Set X),
      (∀ x ∈ S, ∃ i, x ∈ U i) ∧
      (∀ i x, x ∈ U i → ∀ y, y ∈ U i → dist x y < ρ ^ n) ∧
      (m : ℝ) ≤ t ^ n

theorem geometricZeroUpperBox_image {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] {S : Set X}
    (hS : GeometricZeroUpperBox S) (f : X → Y)
    (hf : ∀ x y, dist (f x) (f y) ≤ dist x y) :
    GeometricZeroUpperBox (f '' S) := by
  intro ρ t hρ0 hρ1 ht
  filter_upwards [hS ρ t hρ0 hρ1 ht] with n hn
  obtain ⟨m,U,hcover,hsmall,hcard⟩ := hn
  refine ⟨m,fun i => f '' U i,?_,?_,hcard⟩
  · rintro y ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := hcover x hx
    exact ⟨i,x,hi,rfl⟩
  · rintro i x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩
    exact (hf u v).trans_lt (hsmall i u hu v hv)

/-- BBEK Theorem 4.2 in the standard metric covering formulation for the
actual real/2-adic product set, for every fixed positive ε. The internal
theorem `VV.bbekTheorem42` in `BBEKFinal` constructs this proposition,
with the single admitted EL low-entropy core as its theoretical dependency. -/
def BBEKTheorem42 : Prop :=
  ∀ ε : ℝ, 0 < ε → GeometricZeroUpperBox (JointBadlyApproximable ε)

theorem real_projection_zero_box_of_BBEK (h : BBEKTheorem42) (C : ℕ) :
    GeometricZeroUpperBox (realRigiditySet C) := by
  have hh := geometricZeroUpperBox_image
    (h ((1 / ((C : ℝ) + 3)) / 2) (by positivity)) Prod.fst
    (fun x y => by simpa only [Prod.dist_eq] using le_max_left (dist x.1 y.1) (dist x.2 y.2))
  have heq : Prod.fst '' JointBadlyApproximable ((1 / ((C : ℝ) + 3)) / 2) =
      realRigiditySet C := by
    ext y
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.2,hw⟩
    · rintro ⟨v,hv⟩
      exact ⟨(y,v),hv,rfl⟩
  rwa [heq] at hh

theorem rigidityCoverInput_of_zero_box
    (h : ∀ C : ℕ, GeometricZeroUpperBox (realRigiditySet C)) :
    RigidityCoverInput := by
  intro C s hs
  have hsR : (0 : ℝ) < s := hs
  let ρ : ℝ := 1 / ((C : ℝ) + 2) ^ 5
  let t : ℝ := (4 : ℝ) ^ ((s : ℝ) / 2)
  let q : ℝ := t * (1 / 4 : ℝ) ^ (s : ℝ)
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hC2 : (1 : ℝ) < (C : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) C; linarith
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    exact (div_lt_one (by positivity)).mpr (one_lt_pow₀ hC2 (by omega))
  have ht : 1 < t := Real.one_lt_rpow (by norm_num) (by linarith)
  have hqform : q = (4 : ℝ) ^ (-((s : ℝ) / 2)) := by
    dsimp [q,t]
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hq0 : 0 ≤ q := by rw [hqform]; positivity
  have hq1 : q < 1 := by
    rw [hqform]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlim : Tendsto (fun n : ℕ => ((C : ℝ) + 1) * q ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul ((C : ℝ) + 1)
  have hsmall : ∀ᶠ n : ℕ in atTop, ((C : ℝ) + 1) * q ^ n < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨L,hL,hLm,hcover⟩ := ((eventually_ge_atTop 1).and
    (hsmall.and (h C ρ t hρ0 hρ1 ht))).exists
  obtain ⟨m,U,hU,hdiam,hcount⟩ := hcover
  refine ⟨L,m,U,by omega,hU,?_,?_⟩
  · have hscale : ρ ^ L ≤ 1 / ((C : ℝ) + 1) ^ (4 * L + 1) := by
      have hC1 : (0 : ℝ) ≤ (C : ℝ) + 1 := by positivity
      have hexp : 4 * L + 1 ≤ 5 * L := by omega
      have hp : ((C : ℝ) + 1) ^ (4 * L + 1) ≤ ((C : ℝ) + 2) ^ (5 * L) :=
        (pow_le_pow_left₀ hC1 (show (C : ℝ) + 1 ≤ (C : ℝ) + 2 by linarith)
          (4 * L + 1)).trans (pow_le_pow_right₀ hC2.le hexp)
      dsimp [ρ]
      rw [div_pow, one_pow, ← pow_mul]
      exact one_div_le_one_div_of_le (by positivity) hp
    intro i x hx y hy
    exact (hdiam i x hx y hy).trans_le hscale
  · have hreal : (((C + 1) * m : ℕ) : ℝ) *
        ((1 / 4 : ℝ) ^ L) ^ (s : ℝ) < 1 := by
      have hnonneg : 0 ≤ ((C : ℝ) + 1) * ((1 / 4 : ℝ) ^ L) ^ (s : ℝ) := by positivity
      have hh := mul_le_mul_of_nonneg_left hcount hnonneg
      have heq : ((C : ℝ) + 1) * q ^ L =
          (((C : ℝ) + 1) * ((1 / 4 : ℝ) ^ L) ^ (s : ℝ)) * t ^ L := by
        dsimp [q]
        rw [mul_pow, Real.rpow_pow_comm (x := (1 / 4 : ℝ)) (by norm_num)]
        ring
      rw [heq] at hLm
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc,
        mul_comm, mul_left_comm] using hh.trans_lt hLm
    have hh := ENNReal.ofReal_lt_one.mpr hreal
    rw [ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by exact s.2),
      ENNReal.ofReal_pow (by norm_num)] at hh
    norm_num only [ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos,
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hh
    exact hh

/-- Everything after the explicitly isolated BBEK theorem is now proved,
including projection, constants, scale conversion and the final CF cover. -/
theorem problem7_of_BBEK (h : BBEKTheorem42) : Problem7.Statement :=
  problem7_of_rigidity_cover (rigidityCoverInput_of_zero_box (real_projection_zero_box_of_BBEK h))

end VV.P7BoxCover
