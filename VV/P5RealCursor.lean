import VV.P5Cursor
import VV.HurwitzValue

namespace VV.P5RealCursor
open Hurwitz P5Buffer P5Cursor

def Rel (M : Mat) (x y : ℝ) : Prop :=
  y * ((M.c : ℝ) * x + M.d) = (M.a : ℝ) * x + M.b

theorem Rel.comp {M N : Mat} {x y z : ℝ}
    (hM : Rel M x y) (hN : Rel N y z) : Rel (mul N M) x z := by
  dsimp [Rel, mul] at *
  push_cast
  linear_combination ((M.c : ℝ) * x + M.d) * hN + ((N.a : ℝ) - z * N.c) * hM

theorem Rel.denominator_ne_zero {M : Mat} {x y : ℝ}
    (hdet : det M ≠ 0) (h : Rel M x y) : (M.c : ℝ) * x + M.d ≠ 0 := by
  intro hz
  have hn : (M.a : ℝ) * x + M.b = 0 := by
    dsimp [Rel] at h
    rw [hz, mul_zero] at h
    exact h.symm
  have he : ((det M : ℤ) : ℝ) = 0 := by
    dsimp [det]
    push_cast
    linear_combination (M.a : ℝ) * hz - (M.c : ℝ) * hn
  exact hdet (by exact_mod_cast he)

theorem Rel.unique {M : Mat} {x y z : ℝ}
    (hdet : det M ≠ 0) (hy : Rel M x y) (hz : Rel M x z) : y = z :=
  mul_right_cancel₀ (hy.denominator_ne_zero hdet) (hy.trans hz.symm)

noncomputable def stateValue : State → ℝ → ℝ
  | .D, x => 2 * x
  | .H0, x => x / 2
  | .H1, x => (x - 1) / 2

theorem stateValue_rel (s : State) (x : ℝ) : Rel (stateMatrix s) x (stateValue s x) := by
  cases s <;> dsimp [stateMatrix, stateValue, Rel] <;> push_cast <;> ring

theorem stateValue_irrational (s : State) {x : ℝ} (hx : Irrational x) :
    Irrational (stateValue s x) := by
  cases s with
  | D => simpa only [stateValue, Nat.cast_ofNat] using hx.natCast_mul (by decide : (2 : ℕ) ≠ 0)
  | H0 => exact hx.div_natCast (by decide : (2 : ℕ) ≠ 0)
  | H1 => simpa [stateValue] using (hx.sub_intCast 1).div_natCast (by decide : (2 : ℕ) ≠ 0)

theorem stateValue_pos (s : State) {x : ℝ} (hx : 1 < x) : 0 < stateValue s x := by
  cases s <;> dsimp [stateValue] <;> linarith

noncomputable def cursorValue (c : Cursor) (x : ℝ) : ℝ :=
  value c.buffer.suffix (stateValue c.state x)

theorem cursorValue_irrational (c : Cursor) {x : ℝ} (hx : Irrational x) :
    Irrational (cursorValue c x) := value_irrational _ (stateValue_irrational c.state hx)

theorem cursorValue_gt_one (c : Cursor) {x : ℝ} (hx : 1 < x)
    (hc : 0 < c.buffer.last) : 1 < cursorValue c x := by
  have hs := stateValue_pos c.state hx
  have hb : (1 : ℝ) ≤ c.buffer.last := by exact_mod_cast hc
  rcases c with ⟨s, b, z⟩
  cases z <;> simp only [cursorValue, Buffer.suffix, value, Bool.false_eq_true,
    if_false, if_true, Int.cast_zero, zero_add, inv_inv]
  · linarith [inv_pos.mpr hs]
  · linarith

theorem cursorValue_rel (c : Cursor) {x : ℝ} (hx : Irrational x) :
    Rel (residual c) x (cursorValue c x) := by
  exact (stateValue_rel c.state x).comp (value_matrix c.buffer.suffix (stateValue_irrational c.state hx))

theorem residual_det_ne_zero (c : Cursor) : det (residual c) ≠ 0 := by
  have hs : det (stateMatrix c.state) = 2 := by cases c.state <;> rfl
  dsimp [P5Cursor.residual]
  rw [det_mul, hs]
  rcases word_det_unit c.buffer.suffix with h | h <;> rw [h] <;> norm_num

theorem word_eq_prefixMatrix (w : List ℤ) :
    word w = ⟨(P5Period.matrix w).a, (P5Period.matrix w).b,
      (P5Period.matrix w).c, (P5Period.matrix w).d⟩ := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [word, ih]
      ext <;> simp [mul, digit, P5Period.matrix, P5Period.prepend]

theorem digitBlock_relation {x : ℝ} (hx : Irrational x) (n p : ℕ) :
    Rel (word (P5Period.digitBlock x n p))
      (completeQuotient x (n + p)) (completeQuotient x n) := by
  rw [word_eq_prefixMatrix]
  exact P5Period.digitBlock_realizes hx n p

/-- Exact finite-prefix semantics for the normalized streaming machine. -/
theorem walk_realizes (c : Cursor) {x : ℝ} (hx : Irrational x) (n p : ℕ) :
    cursorValue c (completeQuotient x n) =
      value (walk c (P5Period.digitBlock x n p)).1
        (cursorValue (walk c (P5Period.digitBlock x n p)).2
          (completeQuotient x (n + p))) := by
  have hleft := (digitBlock_relation hx n p).comp
    (cursorValue_rel c (completeQuotient_irrational hx n))
  have hright := (cursorValue_rel (walk c (P5Period.digitBlock x n p)).2
      (completeQuotient_irrational hx (n + p))).comp
    (value_matrix (walk c (P5Period.digitBlock x n p)).1
      (cursorValue_irrational _ (completeQuotient_irrational hx (n + p))))
  rw [walk_matrix] at hleft
  apply hleft.unique ?_ hright
  rw [det_mul]
  apply mul_ne_zero
  · rcases word_det_unit (walk c (P5Period.digitBlock x n p)).1 with h | h <;>
      rw [h] <;> norm_num
  · exact residual_det_ne_zero _

/-- Every emitted digit is an actual partial quotient. The pending buffer
keeps the residual complete quotient above one even when the arithmetic
state itself has a value between zero and one. -/
theorem walk_actual_digits (c : Cursor) (hc : 0 < c.buffer.last)
    {x : ℝ} (hx : Irrational x) (n p : ℕ) (hn : 0 < n) :
    let r := walk c (P5Period.digitBlock x n p)
    completeQuotient (cursorValue c (completeQuotient x n)) r.1.length =
        cursorValue r.2 (completeQuotient x (n + p)) ∧
      P5Period.digitBlock (cursorValue c (completeQuotient x n)) 0 r.1.length = r.1 := by
  let r := walk c (P5Period.digitBlock x n p)
  obtain ⟨hpos, hlast⟩ := walk_positive c hc _ (P5Period.digitBlock_positive hx n p hn)
  have htail : 1 < completeQuotient x (n + p) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n + p ≠ 0)
    rw [hm]
    exact one_lt_completeQuotient_succ hx m
  have hrem := cursorValue_gt_one r.2 htail hlast
  have hout : ∀ a ∈ r.1, 1 ≤ a := fun a ha => hpos a ha
  have heq := walk_realizes c hx n p
  change completeQuotient (cursorValue c (completeQuotient x n)) r.1.length = _ ∧
    P5Period.digitBlock (cursorValue c (completeQuotient x n)) 0 r.1.length = r.1
  rw [heq]
  exact ⟨value_complete_length r.1 hrem hout, value_digitBlock r.1 hrem hout⟩

theorem stateValue_run (s : State) {x : ℝ} (hx : Irrational x) (n : ℕ) :
    stateValue s x = value (run s (P5Period.digitBlock x 0 n)).1
      (stateValue (run s (P5Period.digitBlock x 0 n)).2 (completeQuotient x n)) := by
  have hleft := (digitBlock_relation hx 0 n).comp (stateValue_rel s x)
  have hright := (stateValue_rel (run s (P5Period.digitBlock x 0 n)).2
    (completeQuotient x n)).comp
    (value_matrix (run s (P5Period.digitBlock x 0 n)).1
      (stateValue_irrational _ (completeQuotient_irrational hx n)))
  rw [run_matrix] at hleft
  simp only [Nat.zero_add, completeQuotient] at hleft
  apply hleft.unique ?_ hright
  rw [det_mul]
  apply mul_ne_zero
  · rcases word_det_unit (run s (P5Period.digitBlock x 0 n)).1 with h | h <;>
      rw [h] <;> norm_num
  · cases (run s (P5Period.digitBlock x 0 n)).2 <;> norm_num [det, stateMatrix]

theorem stateValue_run_tailEquivalent (s : State) {x : ℝ} (hx : Irrational x) (n : ℕ) :
    TailEquivalent (stateValue s x)
      (stateValue (run s (P5Period.digitBlock x 0 n)).2 (completeQuotient x n)) := by
  rw [stateValue_run s hx n]
  exact (value_tailEquivalent _ (stateValue_irrational _ (completeQuotient_irrational hx n))).symm

theorem cursorValue_tailEquivalent (c : Cursor) {x : ℝ} (hx : Irrational x) :
    TailEquivalent (stateValue c.state x) (cursorValue c x) :=
  value_tailEquivalent _ (stateValue_irrational _ hx)

end VV.P5RealCursor



