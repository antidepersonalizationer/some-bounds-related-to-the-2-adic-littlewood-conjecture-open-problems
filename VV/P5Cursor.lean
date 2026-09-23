import VV.P5Buffer

namespace VV.P5Cursor
open Hurwitz P5Buffer

structure Cursor where
  state : State
  buffer : Buffer
  deriving DecidableEq

def tick (c : Cursor) (a : ℤ) : List ℤ × Cursor :=
  let r := feed c.buffer (emit c.state a)
  (r.1, ⟨next c.state a, r.2⟩)

def walk (c : Cursor) : List ℤ → List ℤ × Cursor
  | [] => ([], c)
  | a :: w => let r := tick c a; let t := walk r.2 w; (r.1 ++ t.1, t.2)

def residual (c : Cursor) : Mat := mul (word c.buffer.suffix) (stateMatrix c.state)

theorem tick_matrix (c : Cursor) (a : ℤ) :
    mul (residual c) (digit a) = mul (word (tick c a).1) (residual (tick c a).2) := by
  have h := feed_matrix c.buffer (emit c.state a)
  calc
    mul (residual c) (digit a) =
        mul (word c.buffer.suffix) (mul (stateMatrix c.state) (digit a)) := by
      exact mul_assoc _ _ _
    _ = mul (word c.buffer.suffix) (mul (word (emit c.state a)) (stateMatrix (next c.state a))) := by
      rw [step_matrix]
    _ = mul (word (c.buffer.suffix ++ emit c.state a)) (stateMatrix (next c.state a)) := by
      rw [word_append, mul_assoc]
    _ = mul (mul (word (tick c a).1) (word (tick c a).2.buffer.suffix))
        (stateMatrix (next c.state a)) := by rw [h]; rfl
    _ = mul (word (tick c a).1) (residual (tick c a).2) := mul_assoc _ _ _

theorem walk_append (c : Cursor) (u v : List ℤ) :
    walk c (u ++ v) =
      ((walk c u).1 ++ (walk (walk c u).2 v).1, (walk (walk c u).2 v).2) := by
  induction u generalizing c with
  | nil => simp [walk]
  | cons a u ih => simp [walk, ih, List.append_assoc]

theorem walk_matrix (c : Cursor) (w : List ℤ) :
    mul (residual c) (word w) = mul (word (walk c w).1) (residual (walk c w).2) := by
  induction w generalizing c with
  | nil => simp [walk, word]
  | cons a w ih =>
      simp only [walk, word, word_append]
      rw [← mul_assoc, tick_matrix, mul_assoc, ih, ← mul_assoc]

theorem tick_positive (c : Cursor) (hc : 0 < c.buffer.last) (a : ℤ) (ha : 1 ≤ a) :
    (∀ d ∈ (tick c a).1, 0 < d) ∧ 0 < (tick c a).2.buffer.last :=
  feed_positive c.buffer hc (emit c.state a) (emit_nonnegative c.state ha)

theorem walk_positive (c : Cursor) (hc : 0 < c.buffer.last) (w : List ℤ)
    (hw : ∀ a ∈ w, 1 ≤ a) :
    (∀ d ∈ (walk c w).1, 0 < d) ∧ 0 < (walk c w).2.buffer.last := by
  induction w generalizing c with
  | nil => simpa [walk] using hc
  | cons a w ih =>
      obtain ⟨h1, hc'⟩ := tick_positive c hc a (hw a (by simp))
      obtain ⟨h2, hc''⟩ := ih (tick c a).2 hc' (fun a ha => hw a (by simp [ha]))
      refine ⟨?_, hc''⟩
      intro d hd
      simp only [walk, List.mem_append] at hd
      exact hd.elim (h1 d) (h2 d)

theorem walk_state (c : Cursor) (w : List ℤ) :
    (walk c w).2.state = (run c.state w).2 := by
  induction w generalizing c with
  | nil => rfl
  | cons a w ih => simpa only [walk, run, tick] using ih (tick c a).2

theorem walk_states_distinct (c d : Cursor) (w : List ℤ) (h : c.state ≠ d.state) :
    (walk c w).2.state ≠ (walk d w).2.state := by
  rw [walk_state, walk_state]
  exact fun heq => h (run_state_injective w heq)

theorem feed_triplet_nonempty (b : Buffer) (a : ℤ) :
    (feed b [a, 1, 1]).1 ≠ [] := by
  rcases b with ⟨b, z⟩
  cases z <;> by_cases ha : a = 0 <;> simp [feed, push, ha]

theorem tick_D_ready (b : Buffer) (a : ℤ) (ha : 1 ≤ a) :
    (tick ⟨.D, b⟩ a).2.buffer.zero = false := by
  have hn : 2 * a ≠ 0 := by omega
  rcases b with ⟨b, z⟩
  cases z <;> simp [tick, emit, feed, push, hn]

theorem tick_D_nonempty (b : Buffer) (hz : b.zero = false) (a : ℤ) (ha : 1 ≤ a) :
    (tick ⟨.D, b⟩ a).1 ≠ [] := by
  have hn : 2 * a ≠ 0 := by omega
  simp [tick, emit, feed, push, hn, hz]

theorem tick_H0_odd_nonempty (b : Buffer) (a : ℤ) (ha : a % 2 ≠ 0) :
    (tick ⟨.H0, b⟩ a).1 ≠ [] := by
  simpa only [tick, emit, if_neg ha] using feed_triplet_nonempty b (a / 2)

theorem tick_H0_even_ready (b : Buffer) (a : ℤ) (ha : 1 ≤ a) (he : a % 2 = 0) :
    (tick ⟨.H0, b⟩ a).2.buffer.zero = false := by
  have hn : a / 2 ≠ 0 := by have := Int.ediv_add_emod a 2; omega
  rcases b with ⟨b, z⟩
  cases z <;> simp [tick, emit, feed, push, hn, he]

theorem tick_H0_nonempty (b : Buffer) (hz : b.zero = false) (a : ℤ) (ha : 1 ≤ a) :
    (tick ⟨.H0, b⟩ a).1 ≠ [] := by
  by_cases he : a % 2 = 0
  · have hn : a / 2 ≠ 0 := by have := Int.ediv_add_emod a 2; omega
    simp [tick, emit, feed, push, hz, hn, he]
  · exact tick_H0_odd_nonempty b a he

theorem tick_H1_even_nonempty (b : Buffer) (a : ℤ) (he : a % 2 = 0) :
    (tick ⟨.H1, b⟩ a).1 ≠ [] := by
  simpa only [tick, emit, if_pos he] using feed_triplet_nonempty b (a / 2 - 1)

/-- A uniform delay bound. Every three positive input digits emit at least
one finalized positive output digit. This is a symbolic proof, not an
enumeration of bounded inputs. -/
theorem walk_three_nonempty (c : Cursor) (a b d : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 1 ≤ d) : (walk c [a, b, d]).1 ≠ [] := by
  intro h
  simp only [walk, List.append_nil, List.append_eq_nil_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  rcases c with ⟨s, buf⟩
  cases s with
  | D =>
      have hh := tick_H0_nonempty (tick ⟨.D, buf⟩ a).2.buffer (tick_D_ready buf a ha) b hb
      exact hh (by simpa only [tick, next] using h2)
  | H0 =>
      by_cases he : a % 2 = 0
      · have hh := tick_D_nonempty (tick ⟨.H0, buf⟩ a).2.buffer
          (tick_H0_even_ready buf a ha he) b hb
        exact hh (by simpa only [tick, next, if_pos he] using h2)
      · exact tick_H0_odd_nonempty buf a he h1
  | H1 =>
      by_cases he : a % 2 = 0
      · exact tick_H1_even_nonempty buf a he h1
      · have hready := tick_D_ready (tick ⟨.H1, buf⟩ a).2.buffer b hb
        have hh := tick_H0_nonempty
          (tick ⟨.D, (tick ⟨.H1, buf⟩ a).2.buffer⟩ b).2.buffer hready d hd
        exact hh (by simpa only [tick, next, if_neg he] using h3)

end VV.P5Cursor
