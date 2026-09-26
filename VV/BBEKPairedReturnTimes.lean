import VV.BBEKPairedReturnMaximal

/-! The bounded-multiplicity time change for a quadratic rank-one shear.
The two nonconstant coefficients give slopes `0` and `-1/2` for the additional
normalization time, hence slopes `1` and `1/2` for the total return time.
This file proves the time-selection step, not the assertion that an arbitrary
leafwise family satisfies the low-entropy nontransience conclusion. -/
noncomputable section
open Set MeasureTheory Finset
namespace VV.BBEKPairedReturnTimes
open BBEKPairedReturnMaximal

/-- Total time after balancing the linear and quadratic shearing terms. -/
def shearTime (s t k : ℕ) : ℕ := min (k + s) ((k + t) / 2)

/-- On the admissible range the extra time has slopes zero and minus one half. -/
theorem shearTime_eq_add (s t k : ℕ) (hk : k ≤ t) :
    shearTime s t k = k + min s ((t - k) / 2) := by
  unfold shearTime
  omega

theorem shearTime_le (s t k : ℕ) (hk : k ≤ t) : shearTime s t k ≤ t := by
  unfold shearTime
  omega

theorem shearTime_fiber_mod_injective (s t k l : ℕ)
    (h : shearTime s t k = shearTime s t l) (hp : k % 2 = l % 2) : k = l := by
  unfold shearTime at h
  omega

/-- Every target time has at most two preimages, independently of all cutoffs. -/
theorem shearTime_fiber_card_le (s t K j : ℕ) :
    ((range K).filter fun k => shearTime s t k = j).card ≤ 2 := by
  classical
  let A := (range K).filter fun k => shearTime s t k = j
  have hi : Set.InjOn (fun k : ℕ => k % 2) A := by
    intro k hk l hl hkl
    exact shearTime_fiber_mod_injective s t k l
      ((mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm) hkl
  have hs : A.image (fun k => k % 2) ⊆ range 2 := by
    rintro q hq
    rcases mem_image.mp hq with ⟨k, _, rfl⟩
    exact mem_range.mpr (Nat.mod_lt _ (by decide))
  calc
    A.card = (A.image (fun k => k % 2)).card := (card_image_of_injOn hi).symm
    _ ≤ (range 2).card := card_le_card hs
    _ = 2 := card_range _

/-- Pulling bad times back through the actual quadratic time change loses at
most a factor of two. -/
theorem shearTime_bad_card_le (s t K N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (horizon : ∀ k < K, shearTime s t k < N) :
    ((range K).filter fun k => P (shearTime s t k)).card ≤
      2 * ((range N).filter P).card := by
  classical
  let A := (range K).filter fun k => P (shearTime s t k)
  let B := (range N).filter P
  have hmap : ∀ k ∈ A, shearTime s t k ∈ B := by
    intro k hk
    rcases mem_filter.mp hk with ⟨hk, hp⟩
    exact mem_filter.mpr ⟨mem_range.mpr (horizon k (mem_range.mp hk)), hp⟩
  calc
    A.card = ∑ j ∈ B, (A.filter fun k => shearTime s t k = j).card :=
      card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ j ∈ B, 2 := by
      apply sum_le_sum
      intro j _
      exact (Finset.card_le_card (by
        intro k hk
        exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hk).1).1,
          (mem_filter.mp hk).2⟩)).trans (shearTime_fiber_card_le s t K j)
    _ = 2 * B.card := by simp [mul_comm]

/-- A uniform horizon determined by the original normalization scale. -/
theorem shearTime_le_initial_add (s t k : ℕ) :
    shearTime s t k ≤ min s (t / 2) + k := by
  unfold shearTime
  omega

variable {X : Type*} {T : X → X}

/-- Two points with uniformly few bad visits admit one common initial time
and one common normalization time at which both are good. -/
theorem exists_paired_good_shearTime (s t K N : ℕ) (B : Set X)
    (x y : X) {ε : ℝ}
    (hx : ∀ n, (badVisits T B n x : ℝ) ≤ ε * n)
    (hy : ∀ n, (badVisits T B n y : ℝ) ≤ ε * n)
    (horizon : ∀ k < K, shearTime s t k < N)
    (hroom : 2 * ε * K + 4 * ε * N < K) :
    ∃ k < K, T^[k] x ∉ B ∧ T^[k] y ∉ B ∧
      T^[shearTime s t k] x ∉ B ∧ T^[shearTime s t k] y ∉ B := by
  classical
  by_contra h
  push_neg at h
  have hp : ∀ k ∈ range K,
      1 ≤ (if T^[k] x ∈ B then 1 else 0) +
        (if T^[k] y ∈ B then 1 else 0) +
        (if T^[shearTime s t k] x ∈ B then 1 else 0) +
        (if T^[shearTime s t k] y ∈ B then 1 else 0 : ℕ) := by
    intro k hk
    have hh := h k (mem_range.mp hk)
    split_ifs <;> simp_all
  have hsum := sum_le_sum hp
  simp only [sum_const, card_range, smul_eq_mul, mul_one, sum_add_distrib,
    sum_boole] at hsum
  have htx := shearTime_bad_card_le s t K N (fun j => T^[j] x ∈ B) horizon
  have hty := shearTime_bad_card_le s t K N (fun j => T^[j] y ∈ B) horizon
  dsimp only at htx hty
  norm_cast at hsum
  have hnat : K ≤ badVisits T B K x + badVisits T B K y +
      2 * badVisits T B N x + 2 * badVisits T B N y := by
    unfold badVisits
    omega
  have hreal := Nat.cast_le (α := ℝ).mpr hnat
  push_cast at hreal
  have hxK := hx K
  have hyK := hy K
  have hxN := hx N
  have hyN := hy N
  nlinarith




/-- With tolerance `1/100` one gets a paired good time within one quarter of
the original normalization scale. Both normalized return times stay below
five times this search length. -/
theorem exists_paired_good_shearTime_one_hundredth (s t : ℕ) (B : Set X)
    (x y : X)
    (hx : ∀ n, (badVisits T B n x : ℝ) ≤ (1 / 100 : ℝ) * n)
    (hy : ∀ n, (badVisits T B n y : ℝ) ≤ (1 / 100 : ℝ) * n) :
    ∃ k < min s (t / 2) / 4 + 1,
      T^[k] x ∉ B ∧ T^[k] y ∉ B ∧
      T^[shearTime s t k] x ∉ B ∧ T^[shearTime s t k] y ∉ B := by
  let n₀ := min s (t / 2)
  let K := n₀ / 4 + 1
  let N := n₀ + K
  have hK : 0 < K := by dsimp [K]; omega
  have hN : N ≤ 5 * K := by dsimp [N, K]; omega
  apply exists_paired_good_shearTime s t K N B x y hx hy
  · intro k hk
    exact lt_of_le_of_lt (shearTime_le_initial_add s t k)
      (Nat.add_lt_add_left hk n₀)
  · have hrK : (0 : ℝ) < K := Nat.cast_pos.mpr hK
    have hrN : (N : ℝ) ≤ 5 * K := by exact_mod_cast hN
    nlinarith




/-- A single measurable set of mass greater than `99/100` supplies the
simultaneous return time for every two of its points and every quadratic
normalization scale. Only invariance and the bad-set mass bound are assumed. -/
theorem exists_uniform_paired_return_set [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {B : Set X} (hB : MeasurableSet B) (hsmall : μ.real B < (1 / 100 : ℝ) ^ 2) :
    ∃ G : Set X, MeasurableSet G ∧ (99 / 100 : ℝ) < μ.real G ∧
      ∀ x ∈ G, ∀ y ∈ G, ∀ s t : ℕ,
        ∃ k < min s (t / 2) / 4 + 1,
          T^[k] x ∉ B ∧ T^[k] y ∉ B ∧
          T^[shearTime s t k] x ∉ B ∧ T^[shearTime s t k] y ∉ B := by
  obtain ⟨G, hG, hmass, hgood⟩ :=
    exists_all_lengths_good_set_of_small_bad hT hB (by norm_num : (0 : ℝ) < 1 / 100) hsmall
  refine ⟨G, hG, ?_, ?_⟩
  · norm_num at hmass ⊢
    exact hmass
  · intro x hx y hy s t
    exact exists_paired_good_shearTime_one_hundredth s t B x y (hgood x hx) (hgood y hy)

end VV.BBEKPairedReturnTimes

