import VV.Hurwitz
import VV.P5Period
import VV.TailGenerators

/-!
# Exact real semantics for finite continued-fraction words

Words may contain zero in the algebraic lemmas. Positive words with a tail
greater than one are then identified with the project's actual floor-based
partial quotients and complete quotients. No semantic bridge is postulated.
-/

namespace VV.Hurwitz

noncomputable def value : List ℤ → ℝ → ℝ
  | [], x => x
  | a :: w, x => (a : ℝ) + (value w x)⁻¹

theorem value_append (u v : List ℤ) (x : ℝ) : value (u ++ v) x = value u (value v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, value, ih]

theorem value_irrational (w : List ℤ) {x : ℝ} (hx : Irrational x) : Irrational (value w x) := by
  induction w with
  | nil => exact hx
  | cons a w ih => exact ih.inv.intCast_add a

theorem value_tailEquivalent (w : List ℤ) {x : ℝ} (hx : Irrational x) :
    TailEquivalent x (value w x) := by
  induction w with
  | nil => exact TailEquivalent.refl x
  | cons a w ih =>
      have h := ih.trans (tailEquivalent_inv (value_irrational w hx))
      have h := h.trans (tailEquivalent_add_int (value w x)⁻¹ a)
      simpa [value, add_comm] using h

theorem value_pos (w : List ℤ) {x : ℝ} (hx : 0 < x)
    (hw : ∀ a ∈ w, 0 ≤ a) : 0 < value w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
      have ha : (0:ℝ) ≤ a := by exact_mod_cast hw a (by simp)
      have hy := ih (fun a ha => hw a (by simp [ha]))
      exact add_pos_of_nonneg_of_pos ha (inv_pos.mpr hy)

theorem value_gt_one (w : List ℤ) {x : ℝ} (hx : 1 < x)
    (hw : ∀ a ∈ w, 1 ≤ a) : 1 < value w x := by
  cases w with
  | nil => exact hx
  | cons a w =>
      have ha : (1:ℝ) ≤ a := by exact_mod_cast hw a (by simp)
      have hy := value_pos w (lt_trans zero_lt_one hx)
        (fun a ha => le_trans (by omega : (0:ℤ) ≤ 1) (hw a (by simp [ha])))
      exact lt_of_le_of_lt ha (lt_add_of_pos_right _ (inv_pos.mpr hy))

theorem value_matrix (w : List ℤ) {x : ℝ} (hx : Irrational x) :
    value w x * (((word w).c : ℝ)*x+(word w).d) = ((word w).a:ℝ)*x+(word w).b := by
  induction w with
  | nil => simp [value, word, one]
  | cons a w ih =>
      have hy := (value_irrational w hx).ne_zero
      simp only [word, digit, mul, value]
      push_cast
      simp only [_root_.one_mul, zero_mul, add_zero, zero_add]
      calc
        ((a:ℝ)+(value w x)⁻¹) * ((word w).a*x+(word w).b) =
            ((a:ℝ)+(value w x)⁻¹) * (value w x * ((word w).c*x+(word w).d)) := by rw [ih]
        _ = ((a:ℝ)*(word w).a+(word w).c)*x+((a:ℝ)*(word w).b+(word w).d) := by
          rw [add_mul, ← _root_.mul_assoc (value w x)⁻¹, inv_mul_cancel₀ hy, _root_.one_mul]
          linear_combination (a:ℝ) * ih

theorem value_eq_of_matrix_fixed (w : List ℤ) {x : ℝ} (hx : Irrational x)
    (hfix : x * (((word w).c:ℝ)*x+(word w).d) = ((word w).a:ℝ)*x+(word w).b) :
    value w x = x := by
  have hv := value_matrix w hx
  have hden := Problem3.mobius_denominator_ne_zero (word_det_unit w) hv
  exact mul_right_cancel₀ hden (hv.trans hfix.symm)

theorem value_first_digit {a : ℤ} {w : List ℤ} {x : ℝ} (hx : 1 < x)
    (hw : ∀ b ∈ w, 1 ≤ b) : partialQuotient (value (a::w) x) 0 = a := by
  have hy : 1 < value w x := value_gt_one w hx hw
  change ⌊(a:ℝ)+(value w x)⁻¹⌋ = a
  apply Int.floor_eq_iff.mpr
  constructor
  · linarith [inv_pos.mpr (lt_trans zero_lt_one hy)]
  · linarith [inv_lt_one_of_one_lt₀ hy]

theorem value_complete_step {a : ℤ} {w : List ℤ} {x : ℝ} (hx : 1 < x)
    (hw : ∀ b ∈ w, 1 ≤ b) : completeQuotient (value (a::w) x) 1 = value w x := by
  have hf := value_first_digit (a := a) hx hw
  change ⌊value (a::w) x⌋ = a at hf
  change (value (a::w) x - (⌊value (a::w) x⌋ : ℝ))⁻¹ = value w x
  rw [hf]
  simp [value]

theorem value_complete_length (w : List ℤ) {x : ℝ} (hx : 1 < x)
    (hw : ∀ a ∈ w, 1 ≤ a) : completeQuotient (value w x) w.length = x := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      have htail : ∀ b ∈ w, 1 ≤ b := fun b hb => hw b (by simp [hb])
      rw [List.length_cons, show w.length+1=1+w.length by omega, ← completeQuotient_add]
      rw [value_complete_step hx htail]
      exact ih htail

theorem digitBlock_completeQuotient (x : ℝ) (n m p : ℕ) :
    P5Period.digitBlock (completeQuotient x n) m p = P5Period.digitBlock x (n+m) p := by
  induction p generalizing m with
  | zero => rfl
  | succ p ih =>
      simp only [P5Period.digitBlock, partialQuotient, completeQuotient_add, ih, Nat.add_assoc]

theorem value_digitBlock (w : List ℤ) {x : ℝ} (hx : 1 < x)
    (hw : ∀ a ∈ w, 1 ≤ a) : P5Period.digitBlock (value w x) 0 w.length = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      have htail : ∀ b ∈ w, 1 ≤ b := fun b hb => hw b (by simp [hb])
      simp only [List.length_cons, P5Period.digitBlock, zero_add]
      rw [value_first_digit hx htail]
      have he : P5Period.digitBlock (value (a::w) x) 1 w.length =
          P5Period.digitBlock (value w x) 0 w.length := by
        rw [← value_complete_step (a := a) hx htail, digitBlock_completeQuotient]
      rw [he, ih htail]

end VV.Hurwitz
