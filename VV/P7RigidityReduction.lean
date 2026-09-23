import VV.P7TailLimits

/-!
This module reduces Problem 7 to a metric covering estimate for the actual
BBEK exceptional set. The conversions to CF word complexity and Hausdorff
dimension are proved here. Later modules supply the estimate from the
internal BBEK theorem, whose sole admitted theoretical input is the named
EL core in `BBEKLowEntropyCore`.
-/

open Set
open scoped NNReal ENNReal Topology

namespace VV.P7RigidityReduction
open CylinderGeometry P7TailLimits P7AdicLimits Problem7

noncomputable section
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Compactness is elementary and is proved independently of the deep
covering-rate estimate below. -/
theorem isCompact_jointBadlyApproximable (ε : ℝ) :
    IsCompact (JointBadlyApproximable ε) := by
  let tests : Set (ℝ × ℤ_[2]) :=
    ⋂ a : ℕ, ⋂ b : ℕ, ⋂ (_h : 1 ≤ a),
      {w | ε ≤ ((max a b : ℕ) : ℝ) * |(a : ℝ) * w.1 - (b : ℝ)| *
        ‖(a : ℤ_[2]) * w.2 - (b : ℤ_[2])‖}
  have htests : IsClosed tests := by
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro b
    apply isClosed_iInter
    intro _ha
    apply isClosed_le continuous_const
    fun_prop
  have heq : JointBadlyApproximable ε = ((Icc (0 : ℝ) 1) ×ˢ univ) ∩ tests := by
    ext w
    simp only [JointBadlyApproximable, tests, mem_setOf_eq, mem_inter_iff,
      mem_prod, mem_univ, and_true, mem_iInter]
  rw [heq]
  exact (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set ℤ_[2]))).inter_right htests

theorem isCompact_realRigiditySet (C : ℕ) : IsCompact (realRigiditySet C) := by
  have heq : realRigiditySet C = Prod.fst ''
      JointBadlyApproximable ((1 / ((C : ℝ) + 3)) / 2) := by
    ext y
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨(y, v), hv, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
  rw [heq]
  exact (isCompact_jointBadlyApproximable _).image continuous_fst

theorem branch_nonexpansive (a u v : ℝ) (ha : 1 ≤ a) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    dist (branch a u) (branch a v) ≤ dist u v := by
  have hpu : 0 < a + u := by linarith
  have hpv : 0 < a + v := by linarith
  have hp : 1 ≤ (a + u) * (a + v) := by nlinarith
  rw [Real.dist_eq, Real.dist_eq, branch_difference a u v hpu.ne' hpv.ne',
    abs_div, abs_of_pos (mul_pos hpu hpv), abs_sub_comm v u]
  exact (div_le_self (abs_nonneg _) hp)

def expandedCover (C m : ℕ) (U : Fin m → Set ℝ) :
    Fin (C + 1) × Fin m → Set ℝ := fun i =>
  if i.1.val = 0 then U i.2 ∩ Icc 0 1
  else branch (i.1.val : ℝ) '' (U i.2 ∩ Icc 0 1)

theorem expandedCover_covers (C m : ℕ) (U : Fin m → Set ℝ)
    (hcover : ∀ y ∈ realRigiditySet C, ∃ i, y ∈ U i) :
    ∀ y ∈ tailRigiditySet C, ∃ i, y ∈ expandedCover C m U i := by
  intro y hy
  rcases hy with hy | ⟨a, ha1, haC, z, hz, rfl⟩
  · obtain ⟨i, hi⟩ := hcover y hy
    obtain ⟨v, hv⟩ := hy
    exact ⟨(⟨0, by omega⟩, i), by simpa only [expandedCover, if_pos rfl] using And.intro hi hv.1⟩
  · obtain ⟨i, hi⟩ := hcover z hz
    obtain ⟨v, hv⟩ := hz
    have ha0 : 0 ≤ a := by omega
    have hnat : a.toNat ≤ C := by exact_mod_cast (show (a.toNat : ℤ) ≤ (C : ℤ) by simpa using haC)
    have hpos : 0 < a.toNat := by omega
    let j : Fin (C + 1) := ⟨a.toNat, by omega⟩
    refine ⟨(j, i), ?_⟩
    rw [expandedCover, if_neg (show j.val ≠ 0 from by dsimp [j]; omega)]
    refine ⟨z, ⟨hi, hv.1⟩, ?_⟩
    have heq : (j.val : ℝ) = a := by dsimp [j]; exact_mod_cast Int.toNat_of_nonneg ha0
    rw [heq]

theorem expandedCover_small (C m : ℕ) (U : Fin m → Set ℝ) (r : ℝ)
    (hsmall : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → dist x y < r) :
    ∀ i x, x ∈ expandedCover C m U i → ∀ y, y ∈ expandedCover C m U i → dist x y < r := by
  intro i x hx y hy
  by_cases hi : i.1.val = 0
  · simp only [expandedCover, if_pos hi] at hx hy
    exact hsmall i.2 x hx.1 y hy.1
  · simp only [expandedCover, if_neg hi] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    have hpos : (1 : ℝ) ≤ i.1.val := by exact_mod_cast (show 1 ≤ i.1.val by omega)
    exact (branch_nonexpansive i.1.val u v hpos hu.2.1 hv.2.1).trans_lt
      (hsmall i.2 u hu.1 v hv.1)

theorem recurrentWordSet_finite {x : ℝ} (hx : Irrational x) {C : ℕ}
    (hC : EventualBound x C) (L : ℕ) :
    {w : Fin L → ℤ | RecurrentValue (wordAt (fun n => partialQuotient x (n + 1)) L) w}.Finite := by
  classical
  let stream : ℕ → ℤ := fun n => partialQuotient x (n + 1)
  have hf := finite_range_cf_digits hx hC
  letI : Fintype (Set.range stream) := hf.fintype
  let down : (Fin L → Set.range stream) → (Fin L → ℤ) := fun w k => (w k).val
  apply (Set.finite_range down).subset
  intro w hw
  obtain ⟨n, _, hn⟩ := hw 0
  refine ⟨fun k => ⟨stream (n + k.val), ⟨n + k.val, rfl⟩⟩, ?_⟩
  exact hn

/-- The quantitative consequence of BBEK's zero upper box dimension
theorem used below. It asks for covers only of its concrete real
projection, at explicit exponential scales, and contains no CF words or
Hausdorff-dimension conclusion. -/
def RigidityCoverInput : Prop :=
  ∀ (C : ℕ) (s : ℝ≥0), 0 < s → ∃ (L m : ℕ) (U : Fin m → Set ℝ),
    0 < L ∧
    (∀ y ∈ realRigiditySet C, ∃ i, y ∈ U i) ∧
    (∀ i x, x ∈ U i → ∀ y, y ∈ U i →
      dist x y < 1 / ((C : ℝ) + 1) ^ (4 * L + 1)) ∧
    (((C + 1) * m : ℕ) : ℝ≥0∞) * ((1 / 4 : ℝ≥0∞) ^ L) ^ (s : ℝ) < 1

theorem recurrentDictionaryInput_of_rigidityCoverInput (h : RigidityCoverInput) :
    RecurrentDictionaryInput := by
  classical
  intro s hs x hx
  obtain ⟨C, hC⟩ := hx.2
  have hbound : EventualBound x C := by simpa using hC 0
  obtain ⟨L, m, U, hL, hcover, hsmall, hcard⟩ := h C s hs
  let W := (recurrentWordSet_finite hx.1 hbound (2 * L)).toFinset
  have hW : ∀ w : Fin (2 * L) → ℤ,
      RecurrentValue (wordAt (fun n => partialQuotient x (n + 1)) (2 * L)) w ↔ w ∈ W := by
    intro w
    change w ∈ {w : Fin (2 * L) → ℤ |
      RecurrentValue (wordAt (fun n => partialQuotient x (n + 1)) (2 * L)) w} ↔ _
    exact (Set.Finite.mem_toFinset (recurrentWordSet_finite hx.1 hbound (2 * L))).symm
  have hreps : ∀ w : W, ∃ y ∈ tailRigiditySet C, Irrational y ∧
      partialQuotient y 0 = 0 ∧
      (∀ k : ℕ, partialQuotient y (k + 1) ≤ (C : ℤ)) ∧
      ∀ k : Fin (2 * L), partialQuotient y (k.val + 1) = w.val k := by
    intro w
    exact recurrent_word_representative hx.1 C (2 * L) hC (by omega)
      w.val ((hW w.val).mpr w.property)
  choose point hmem hirr hzero hboundall hword using hreps
  have hcount : W.card ≤ (C + 1) * m := by
    have hh := word_count_le_cover_card C (2 * L) 0 W
      (expandedCover C m U) point hirr hboundall hzero hword
      (fun w => expandedCover_covers C m U hcover (point w) (hmem w))
      (by simpa only [show 2 * (2 * L) + 1 = 4 * L + 1 by omega] using
        expandedCover_small C m U _ hsmall)
    simpa only [Fintype.card_prod, Fintype.card_fin] using hh
  refine ⟨L, W, hL, fun w hw => (hW w).mp hw, ?_⟩
  exact (mul_le_mul_right' (by exact_mod_cast hcount)
    (((1 / 4 : ℝ≥0∞) ^ L) ^ (s : ℝ))).trans_lt hcard

/-- A fully proved reduction to the single explicitly stated deep
arithmetic covering theorem. The covering premise has not been proved
or replaced by an axiom. -/
theorem problem7_of_rigidity_cover (h : RigidityCoverInput) : Problem7.Statement :=
  problem7_of_recurrent_dictionary (recurrentDictionaryInput_of_rigidityCoverInput h)

end
end VV.P7RigidityReduction
