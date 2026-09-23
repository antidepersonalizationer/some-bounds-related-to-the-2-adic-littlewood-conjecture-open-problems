import VV.P5RealCursor

namespace VV.P5Stream
open Hurwitz P5Buffer P5Cursor P5RealCursor P5Period

noncomputable def trajectory (c : Cursor) (x : ℝ) (n p : ℕ) :=
  walk c (digitBlock x n p)

noncomputable def position (c : Cursor) (x : ℝ) (n p : ℕ) : ℕ :=
  (trajectory c x n p).1.length

theorem trajectory_add (c : Cursor) (x : ℝ) (n p q : ℕ) :
    trajectory c x n (p + q) =
      ((trajectory c x n p).1 ++
        (trajectory (trajectory c x n p).2 x (n + p) q).1,
       (trajectory (trajectory c x n p).2 x (n + p) q).2) := by
  exact (congrArg (walk c) (digitBlock_append x n p q)).trans (walk_append _ _ _)

theorem position_mono (c : Cursor) (x : ℝ) (n : ℕ) :
    Monotone (position c x n) := by
  intro p q hpq
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hpq
  simp only [position, trajectory_add, List.length_append]
  omega

theorem position_three_pos (c : Cursor) {x : ℝ} (hx : Irrational x)
    (n : ℕ) (hn : 0 < n) : 0 < position c x n 3 := by
  have hp := digitBlock_positive hx n 3 hn
  have hne : (trajectory c x n 3).1 ≠ [] := by
    apply walk_three_nonempty
    · exact hp _ (by simp [digitBlock])
    · exact hp _ (by simp [digitBlock])
    · exact hp _ (by simp [digitBlock])
  exact List.length_pos_iff.mpr hne

theorem position_growth (c : Cursor) {x : ℝ} (hx : Irrational x)
    (n k : ℕ) (hn : 0 < n) : k ≤ position c x n (3 * k) := by
  induction k generalizing c n with
  | zero => omega
  | succ k ih =>
      rw [Nat.mul_succ, Nat.add_comm (3 * k) 3]
      simp only [position, trajectory_add, List.length_append]
      have h3 := position_three_pos c hx n hn
      have hk := ih (trajectory c x n 3).2 (n + 3) (by omega)
      change k ≤ (trajectory (trajectory c x n 3).2 x (n + 3) (3 * k)).1.length at hk
      change 0 < (trajectory c x n 3).1.length at h3
      omega

theorem position_eventually_ge (c : Cursor) {x : ℝ} (hx : Irrational x)
    (n : ℕ) (hn : 0 < n) (K : ℕ) :
    ∀ p, 3 * K ≤ p → K ≤ position c x n p := by
  intro p hp
  exact (position_growth c hx n K hn).trans (position_mono c x n hp)

theorem buffer_le_partialQuotient (c : Cursor) {x : ℝ} (hx : 1 < x) :
    c.buffer.last ≤ partialQuotient (cursorValue c x) 0 := by
  apply Int.le_floor.mpr
  have hs := stateValue_pos c.state hx
  rcases c with ⟨s, b, z⟩
  cases z <;> simp only [cursorValue, Buffer.suffix, value, Bool.false_eq_true,
    if_false, if_true, Int.cast_zero, zero_add, inv_inv]
  · exact le_add_of_nonneg_right (le_of_lt (inv_pos.mpr hs))
  · exact le_add_of_nonneg_right (le_of_lt hs)

theorem actual_residual (c : Cursor) (hc : 0 < c.buffer.last)
    {x : ℝ} (hx : Irrational x) (n p : ℕ) (hn : 0 < n) :
    completeQuotient (cursorValue c (completeQuotient x n)) (position c x n p) =
      cursorValue (trajectory c x n p).2 (completeQuotient x (n + p)) :=
  (walk_actual_digits c hc hx n p hn).1

theorem partialQuotient_residual (c : Cursor) (hc : 0 < c.buffer.last)
    {x : ℝ} (hx : Irrational x) (n p k : ℕ) (hn : 0 < n) :
    partialQuotient (cursorValue c (completeQuotient x n)) (position c x n p + k) =
      partialQuotient (cursorValue (trajectory c x n p).2
        (completeQuotient x (n + p))) k := by
  change Int.floor (completeQuotient _ _) = Int.floor (completeQuotient _ _)
  rw [← completeQuotient_add, actual_residual c hc hx n p hn]

/-- Bounded output tails force the entire pending buffer into the same finite
alphabet. No finite enumeration or boundedness hypothesis on the buffer is used. -/
theorem eventual_buffer_bounded (c : Cursor) (hc : 0 < c.buffer.last)
    {x : ℝ} (hx : Irrational x) (n : ℕ) (hn : 0 < n) (C : ℕ)
    (hb : EventualBound (cursorValue c (completeQuotient x n)) C) :
    ∃ P : ℕ, ∀ p, P ≤ p →
      0 < (trajectory c x n p).2.buffer.last ∧
      (trajectory c x n p).2.buffer.last ≤ C := by
  obtain ⟨K, hK⟩ := hb
  refine ⟨3 * (K + 1), ?_⟩
  intro p hp
  have hpos := (walk_positive c hc _ (digitBlock_positive hx n p hn)).2
  refine ⟨hpos, ?_⟩
  have hlen := position_eventually_ge c hx n hn (K + 1) p hp
  have hfirst : partialQuotient (cursorValue c (completeQuotient x n))
      (position c x n p) ≤ C := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position c x n p ≠ 0)
    rw [hq]
    exact hK q (by omega)
  have hxq : 1 < completeQuotient x (n + p) := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n + p ≠ 0)
    rw [hq]
    exact one_lt_completeQuotient_succ hx q
  have hlast := buffer_le_partialQuotient (trajectory c x n p).2 hxq
  have he := partialQuotient_residual c hc hx n p 0 hn
  simp only [Nat.add_zero] at he
  rw [he] at hfirst
  exact hlast.trans hfirst

theorem trajectory_succ (c : Cursor) (x : ℝ) (n p : ℕ) :
    trajectory c x n (p + 1) =
      ((trajectory c x n p).1 ++
        (tick (trajectory c x n p).2 (partialQuotient x (n + p))).1,
       (tick (trajectory c x n p).2 (partialQuotient x (n + p))).2) := by
  simpa only [trajectory, digitBlock, walk, List.append_nil] using trajectory_add c x n p 1

theorem position_succ (c : Cursor) (x : ℝ) (n p : ℕ) :
    position c x n (p + 1) = position c x n p +
      (tick (trajectory c x n p).2 (partialQuotient x (n + p))).1.length := by
  simp only [position, trajectory_succ, List.length_append]

theorem digitBlock_residual (c : Cursor) (hc : 0 < c.buffer.last)
    {x : ℝ} (hx : Irrational x) (n p k : ℕ) (hn : 0 < n) :
    digitBlock (P5RealCursor.cursorValue c (completeQuotient x n)) (position c x n p) k =
      digitBlock (P5RealCursor.cursorValue (trajectory c x n p).2
        (completeQuotient x (n + p))) 0 k := by
  rw [digitBlock_eq_ofFn, digitBlock_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  simpa only [Nat.zero_add] using partialQuotient_residual c hc hx n p i.val hn

theorem emitted_actual (c : Cursor) (hc : 0 < c.buffer.last)
    {x : ℝ} (hx : Irrational x) (n p : ℕ) (hn : 0 < n) :
    let w := (tick (trajectory c x n p).2 (partialQuotient x (n + p))).1
    digitBlock (P5RealCursor.cursorValue c (completeQuotient x n)) (position c x n p) w.length = w := by
  have hpos := (walk_positive c hc _ (digitBlock_positive hx n p hn)).2
  dsimp only
  rw [digitBlock_residual c hc hx n p _ hn]
  simpa only [digitBlock, walk, List.append_nil] using
    (walk_actual_digits (trajectory c x n p).2 hpos hx (n + p) 1 (by omega)).2

theorem digitBlock_bounded {x : ℝ} {C : ℕ} (n p : ℕ)
    (h : ∀ i, partialQuotient x (n + i) ≤ C) :
    ∀ a ∈ digitBlock x n p, a ≤ (C : ℤ) := by
  rw [digitBlock_eq_ofFn]
  intro a ha
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
  simpa only [← hi] using h i.val

theorem eventual_emitted_bounded (c : Cursor) (hc : 0 < c.buffer.last)
    {x : ℝ} (hx : Irrational x) (n : ℕ) (hn : 0 < n) (C : ℕ)
    (hb : EventualBound (P5RealCursor.cursorValue c (completeQuotient x n)) C) :
    ∃ P : ℕ, ∀ p, P ≤ p → ∀ a ∈
      (tick (trajectory c x n p).2 (partialQuotient x (n + p))).1,
      1 ≤ a ∧ a ≤ (C : ℤ) := by
  obtain ⟨K,hK⟩ := hb
  refine ⟨3 * (K + 1), ?_⟩
  intro p hp a ha
  have hpos := (walk_positive c hc _ (digitBlock_positive hx n p hn)).2
  have hinput : 1 ≤ partialQuotient x (n + p) := by
    obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n + p ≠ 0)
    rw [hq]
    exact one_le_partialQuotient_succ hx q
  refine ⟨(tick_positive _ hpos _ hinput).1 a ha, ?_⟩
  have hlen := position_eventually_ge c hx n hn (K + 1) p hp
  have hb' : ∀ i, partialQuotient (P5RealCursor.cursorValue c (completeQuotient x n))
      (position c x n p + i) ≤ C := by
    intro i
    obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position c x n p + i ≠ 0)
    rw [hq]
    exact hK q (by omega)
  have ht := digitBlock_bounded (position c x n p)
    (tick (trajectory c x n p).2 (partialQuotient x (n + p))).1.length hb'
  rw [emitted_actual c hc hx n p hn] at ht
  exact ht a ha

end VV.P5Stream


