import VV.P4Cyclic

namespace VV.Hurwitz

theorem positive_word_bounds (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a) :
    1 ≤ (word w).a ∧ 0 ≤ (word w).b ∧ 0 ≤ (word w).c ∧ 0 ≤ (word w).d := by
  induction w with
  | nil => norm_num [word, one]
  | cons a w ih =>
    have ha := hw a (by simp)
    obtain ⟨hA,hB,hC,hD⟩ := ih (fun b hb => hw b (by simp [hb]))
    simp only [word, digit, mul, _root_.one_mul, zero_mul, add_zero]
    refine ⟨?_, ?_, by omega, hB⟩
    · nlinarith
    · exact add_nonneg (mul_nonneg (by omega) hB) hD

theorem positive_nonempty_word_bounds (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a)
    (hne : w ≠ []) : 1 ≤ (word w).b ∧ 1 ≤ (word w).c := by
  induction w with
  | nil => exact False.elim (hne rfl)
  | cons a w ih =>
    have ha := hw a (by simp)
    have htail : ∀ b ∈ w, 1 ≤ b := fun b hb => hw b (by simp [hb])
    obtain ⟨hA,hB,hC,hD⟩ := positive_word_bounds w htail
    simp only [word, digit, mul, _root_.one_mul, zero_mul, add_zero]
    refine ⟨?_, hA⟩
    cases w with
    | nil => norm_num [word, one]
    | cons b w =>
      have hb := (ih htail (by simp)).1
      nlinarith

theorem positive_long_word_bounds (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a)
    (hlen : 2 ≤ w.length) :
    2 ≤ (word w).a ∧ 1 ≤ (word w).b ∧ 1 ≤ (word w).c ∧ 1 ≤ (word w).d := by
  cases w with
  | nil => simp at hlen
  | cons a w =>
    have ha := hw a (by simp)
    have htail : ∀ b ∈ w, 1 ≤ b := fun b hb => hw b (by simp [hb])
    have hne : w ≠ [] := by intro h; simp [h] at hlen
    obtain ⟨hA,hB,hC,hD⟩ := positive_word_bounds w htail
    obtain ⟨hB1,hC1⟩ := positive_nonempty_word_bounds w htail hne
    simp only [word, digit, mul, _root_.one_mul, zero_mul, add_zero]
    exact ⟨by nlinarith, by nlinarith, hA, hB1⟩

theorem trace_append_strict (u w : List ℤ)
    (hu : ∀ a ∈ u, 1 ≤ a) (hw : ∀ a ∈ w, 1 ≤ a) (hlen : 2 ≤ w.length) :
    trace (word u) < trace (word (u ++ w)) := by
  obtain ⟨uA,uB,uC,uD⟩ := positive_word_bounds u hu
  obtain ⟨wA,wB,wC,wD⟩ := positive_long_word_bounds w hw hlen
  rw [word_append]
  simp only [trace, mul]
  nlinarith [mul_nonneg uB (show 0 ≤ (word w).c by omega),
    mul_nonneg uC (show 0 ≤ (word w).b by omega)]

theorem repeat_word_positive (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a) (k : ℕ) :
    ∀ a ∈ (List.replicate k w).flatten, 1 ≤ a := by
  intro a ha
  obtain ⟨u, hu, hau⟩ := List.mem_flatten.mp ha
  have heq : u = w := (List.mem_replicate.mp hu).2
  exact hw a (heq ▸ hau)

theorem trace_repeat_strictMono (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a)
    (hlen : 2 ≤ w.length) :
    StrictMono (fun k : ℕ => trace (word (List.replicate k w).flatten)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h := trace_append_strict (List.replicate k w).flatten w
    (repeat_word_positive w hw k) hw hlen
  simpa only [List.replicate_succ, List.flatten_cons, trace_word_rotate] using h

/-- Equal trace forbids an output cycle from being several copies of the
original positive cycle. Together with `trace_similar`, this closes the
matrix part of the exact-period-length argument. -/
theorem trace_repeat_eq_iff (w : List ℤ) (hw : ∀ a ∈ w, 1 ≤ a)
    (hlen : 2 ≤ w.length) (k : ℕ) :
    trace (word (List.replicate k w).flatten) = trace (word w) ↔ k = 1 := by
  have h := (trace_repeat_strictMono w hw hlen).injective.eq_iff (a := k) (b := 1)
  simpa using h

end VV.Hurwitz
