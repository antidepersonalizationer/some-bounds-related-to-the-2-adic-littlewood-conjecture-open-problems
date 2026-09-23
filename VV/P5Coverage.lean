import VV.P5Machine

namespace VV.P5Coverage
open Hurwitz P5Buffer P5Cursor P5Period P5Stream P5Synchronize P5Machine

structure RealTrace (C : ℕ) (V : Type) (s : Step V (Fin C)) (x y z : ℝ) where
  start : ℕ
  start_pos : 0 < start
  input : ℕ → Fin C
  state : ℕ → V
  left : ℕ → List (Fin C)
  right : ℕ → List (Fin C)
  L : ℕ → ℕ
  R : ℕ → ℕ
  trace : Trace s input state left right
  input_digits : ∀ n, digitValue (input n) = partialQuotient x (start + n)
  left_digits : ∀ n, (left n).map digitValue = digitBlock y (L n) (left n).length
  right_digits : ∀ n, (right n).map digitValue = digitBlock z (R n) (right n).length
  L_succ : ∀ n, L (n + 1) = L n + (left n).length
  R_succ : ∀ n, R (n + 1) = R n + (right n).length
  L_cofinal : ∀ K, ∃ N, ∀ n, N ≤ n → K ≤ L n
  R_cofinal : ∀ K, ∃ N, ∀ n, N ≤ n → K ≤ R n

variable {C : ℕ}

theorem from_cursors (c d : Cursor) (hc : 0 < c.buffer.last) (hd : 0 < d.buffer.last)
    (hdis : c.state ≠ d.state) {x : ℝ} (hx : Irrational x) (n : ℕ) (hn : 0 < n)
    (hin : EventualBound x C)
    (hl : EventualBound (P5RealCursor.cursorValue c (completeQuotient x n)) C)
    (hr : EventualBound (P5RealCursor.cursorValue d (completeQuotient x n)) C) :
    Nonempty (RealTrace C (Pair C) (step C) x
      (P5RealCursor.cursorValue c (completeQuotient x n))
      (P5RealCursor.cursorValue d (completeQuotient x n))) := by
  classical
  obtain ⟨Kl,hKl⟩ := eventual_buffer_bounded c hc hx n hn C hl
  obtain ⟨Kr,hKr⟩ := eventual_buffer_bounded d hd hx n hn C hr
  obtain ⟨Wl,hWl⟩ := eventual_emitted_bounded c hc hx n hn C hl
  obtain ⟨Wr,hWr⟩ := eventual_emitted_bounded d hd hx n hn C hr
  obtain ⟨Ki,hKi⟩ := hin
  let P := Kl + Kr + Wl + Wr + Ki + 1
  have hcB (i : ℕ) := hKl (P + i) (by dsimp [P]; omega)
  have hdB (i : ℕ) := hKr (P + i) (by dsimp [P]; omega)
  have hwc (i : ℕ) : BoundedWord C
      (tick (trajectory c x n (P + i)).2 (partialQuotient x (n + (P + i)))).1 :=
    hWl (P + i) (by dsimp [P]; omega)
  have hwd (i : ℕ) : BoundedWord C
      (tick (trajectory d x n (P + i)).2 (partialQuotient x (n + (P + i)))).1 :=
    hWr (P + i) (by dsimp [P]; omega)
  have hi (i : ℕ) : 1 ≤ partialQuotient x (n + (P + i)) ∧
      partialQuotient x (n + (P + i)) ≤ (C : ℤ) := by
    obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n + (P + i) ≠ 0)
    rw [hq]
    exact ⟨one_le_partialQuotient_succ hx q,hKi q (by dsimp [P] at hq; omega)⟩
  have hdif (i : ℕ) : (trajectory c x n (P + i)).2.state ≠
      (trajectory d x n (P + i)).2.state := walk_states_distinct c d _ hdis
  let input := fun i => encodeDigit (partialQuotient x (n + (P + i))) (hi i)
  let state := fun i => encodePair (trajectory c x n (P + i)).2
    (trajectory d x n (P + i)).2 (hdif i) (hcB i) (hdB i)
  let left := fun i => encodeWord
    (tick (trajectory c x n (P + i)).2 (partialQuotient x (n + (P + i)))).1 (hwc i)
  let right := fun i => encodeWord
    (tick (trajectory d x n (P + i)).2 (partialQuotient x (n + (P + i)))).1 (hwd i)
  have hleft (i : ℕ) : (left i).length =
      (tick (trajectory c x n (P + i)).2 (partialQuotient x (n + (P + i)))).1.length := by
    simp [left,encodeWord]
  have hright (i : ℕ) : (right i).length =
      (tick (trajectory d x n (P + i)).2 (partialQuotient x (n + (P + i)))).1.length := by
    simp [right,encodeWord]
  refine ⟨{
    start := n + P
    start_pos := by omega
    input := input
    state := state
    left := left
    right := right
    L := fun i => position c x n (P + i)
    R := fun i => position d x n (P + i)
    trace := ?_
    input_digits := ?_
    left_digits := ?_
    right_digits := ?_
    L_succ := ?_
    R_succ := ?_
    L_cofinal := ?_
    R_cofinal := ?_ }⟩
  · intro i
    have hcn : 0 < (tick (trajectory c x n (P + i)).2
        (partialQuotient x (n + (P + i)))).2.buffer.last ∧
        (tick (trajectory c x n (P + i)).2
        (partialQuotient x (n + (P + i)))).2.buffer.last ≤ (C : ℤ) := by
      simpa only [← Nat.add_assoc,trajectory_succ] using hcB (i + 1)
    have hdn : 0 < (tick (trajectory d x n (P + i)).2
        (partialQuotient x (n + (P + i)))).2.buffer.last ∧
        (tick (trajectory d x n (P + i)).2
        (partialQuotient x (n + (P + i)))).2.buffer.last ≤ (C : ℤ) := by
      simpa only [← Nat.add_assoc,trajectory_succ] using hdB (i + 1)
    have hs := step_encode (trajectory c x n (P + i)).2 (trajectory d x n (P + i)).2
      (partialQuotient x (n + (P + i))) (hdif i) (hcB i) (hdB i) (hi i) hcn hdn (hwc i) (hwd i)
    simpa only [input,state,left,right,← Nat.add_assoc,trajectory_succ] using hs
  · intro i
    simp only [input,digitValue_encode,Nat.add_assoc]
  · intro i
    rw [hleft]
    simpa only [left,decode_encodeWord] using (emitted_actual c hc hx n (P + i) hn).symm
  · intro i
    rw [hright]
    simpa only [right,decode_encodeWord] using (emitted_actual d hd hx n (P + i) hn).symm
  · intro i
    rw [hleft,← Nat.add_assoc,position_succ]
  · intro i
    rw [hright,← Nat.add_assoc,position_succ]
  · intro K
    exact ⟨3*K,fun i hi => position_eventually_ge c hx n hn K (P+i) (by omega)⟩
  · intro K
    exact ⟨3*K,fun i hi => position_eventually_ge d hx n hn K (P+i) (by omega)⟩

/-- Every genuine bounded three-layer orbit has a trace in the explicit
24 C²-state streaming machine. The two output streams are actual CF tails
of x/2 and 2x, not merely formal transducer labels. -/
theorem base_coverage {x : ℝ} (hx : Irrational x)
    (h0 : EventualBound x C) (hl : EventualBound (x / 2) C)
    (hr : EventualBound (2 * x) C) :
    ∃ y z : ℝ, TailEquivalent y (x / 2) ∧ TailEquivalent z (2 * x) ∧
      Nonempty (RealTrace C (Pair C) (step C) x y z) := by
  let c : Cursor := ⟨(run .H0 (digitBlock x 0 1)).2,⟨1,false⟩⟩
  let d : Cursor := ⟨(run .D (digitBlock x 0 1)).2,⟨1,false⟩⟩
  have hcl : TailEquivalent (x / 2) (P5RealCursor.cursorValue c (completeQuotient x 1)) :=
    (P5RealCursor.stateValue_run_tailEquivalent .H0 hx 1).trans
      (P5RealCursor.cursorValue_tailEquivalent c (completeQuotient_irrational hx 1))
  have hdr : TailEquivalent (2 * x) (P5RealCursor.cursorValue d (completeQuotient x 1)) :=
    (P5RealCursor.stateValue_run_tailEquivalent .D hx 1).trans
      (P5RealCursor.cursorValue_tailEquivalent d (completeQuotient_irrational hx 1))
  have hdis : c.state ≠ d.state := by
    intro he
    have hf := run_state_injective (digitBlock x 0 1) (show (run .H0 (digitBlock x 0 1)).2 = (run .D (digitBlock x 0 1)).2 from he)
    cases hf
  exact ⟨_,_,hcl.symm,hdr.symm,from_cursors c d (by norm_num [c]) (by norm_num [d])
    hdis hx 1 (by omega) h0 ((hcl.eventualBound_iff C).mp hl) ((hdr.eventualBound_iff C).mp hr)⟩

end VV.P5Coverage




