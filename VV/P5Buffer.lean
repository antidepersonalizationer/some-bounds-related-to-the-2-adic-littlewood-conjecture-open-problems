import VV.Hurwitz

/-!
Streaming removal of the Hurwitz transducer's zero digits.  One pending
positive digit and one zero flag suffice.  These are exact matrix identities
over arbitrary integer input; positivity is proved separately.
-/

namespace VV.P5Buffer
open Hurwitz

structure Buffer where
  last : ℤ
  zero : Bool
  deriving DecidableEq

def Buffer.suffix (b : Buffer) : List ℤ := if b.zero then [b.last, 0] else [b.last]

def push (b : Buffer) (a : ℤ) : List ℤ × Buffer :=
  if b.zero then ([], ⟨b.last + a, false⟩)
  else if a = 0 then ([], ⟨b.last, true⟩)
  else ([b.last], ⟨a, false⟩)

def feed (b : Buffer) : List ℤ → List ℤ × Buffer
  | [] => ([], b)
  | a :: w =>
      let r := push b a
      let t := feed r.2 w
      (r.1 ++ t.1, t.2)

theorem push_matrix (b : Buffer) (a : ℤ) :
    word (b.suffix ++ [a]) = mul (word (push b a).1) (word (push b a).2.suffix) := by
  rcases b with ⟨b, z⟩
  cases z <;> by_cases ha : a = 0
  · simp [push, Buffer.suffix, ha, word, digit, mul, one]
  · simp [push, Buffer.suffix, ha, word, digit, mul, one]
  · simp [push, Buffer.suffix, ha, word, digit, mul, one]
  · simpa [push, Buffer.suffix, ha, word] using zero_cleanup b a

theorem feed_append (b : Buffer) (u v : List ℤ) :
    feed b (u ++ v) =
      ((feed b u).1 ++ (feed (feed b u).2 v).1, (feed (feed b u).2 v).2) := by
  induction u generalizing b with
  | nil => simp [feed]
  | cons a u ih => simp [feed, ih, List.append_assoc]

theorem feed_matrix (b : Buffer) (w : List ℤ) :
    word (b.suffix ++ w) = mul (word (feed b w).1) (word (feed b w).2.suffix) := by
  induction w generalizing b with
  | nil => simp [feed, word]
  | cons a w ih =>
      have hp := push_matrix b a
      have ht := ih (push b a).2
      calc
        word (b.suffix ++ (a :: w)) = mul (word (b.suffix ++ [a])) (word w) := by
          rw [← word_append]
          simp
        _ = mul (mul (word (push b a).1) (word (push b a).2.suffix)) (word w) := by rw [hp]
        _ = mul (word (push b a).1) (word ((push b a).2.suffix ++ w)) := by
          rw [mul_assoc, word_append]
        _ = mul (word (push b a).1)
            (mul (word (feed (push b a).2 w).1) (word (feed (push b a).2 w).2.suffix)) := by rw [ht]
        _ = mul (word (feed b (a :: w)).1) (word (feed b (a :: w)).2.suffix) := by
          simp only [feed, word_append, mul_assoc]

theorem push_positive (b : Buffer) (hb : 0 < b.last) (a : ℤ) (ha : 0 ≤ a) :
    (∀ d ∈ (push b a).1, 0 < d) ∧ 0 < (push b a).2.last := by
  rcases b with ⟨b, z⟩
  cases z <;> by_cases hz : a = 0 <;> simp_all [push] <;> omega

theorem feed_positive (b : Buffer) (hb : 0 < b.last) (w : List ℤ)
    (hw : ∀ a ∈ w, 0 ≤ a) :
    (∀ d ∈ (feed b w).1, 0 < d) ∧ 0 < (feed b w).2.last := by
  induction w generalizing b with
  | nil => simpa [feed] using hb
  | cons a w ih =>
      obtain ⟨hout, hb'⟩ := push_positive b hb a (hw a (by simp))
      obtain ⟨htail, hlast⟩ := ih (push b a).2 hb' (fun a ha => hw a (by simp [ha]))
      refine ⟨?_, hlast⟩
      intro d hd
      simp only [feed, List.mem_append] at hd
      exact hd.elim (hout d) (htail d)

/-- The pending digit can only increase until it is emitted. -/
theorem push_initial_le_first (b : Buffer) (a : ℤ) (ha : 0 ≤ a) :
    b.last ≤ (push b a).1.headD (push b a).2.last := by
  rcases b with ⟨b, z⟩
  cases z <;> by_cases hz : a = 0 <;> simp [push, hz] <;> omega

theorem feed_initial_le_first (b : Buffer) (w : List ℤ)
    (hw : ∀ a ∈ w, 0 ≤ a) :
    b.last ≤ (feed b w).1.headD (feed b w).2.last := by
  induction w generalizing b with
  | nil => simp [feed]
  | cons a w ih =>
      have hp := push_initial_le_first b a (hw a (by simp))
      have ht := ih (push b a).2 (fun a ha => hw a (by simp [ha]))
      cases heq : (push b a).1 with
      | nil =>
          simp only [heq, List.headD_nil] at hp
          simpa only [feed, heq, List.nil_append, List.headD_nil] using hp.trans ht
      | cons c cs => simpa only [feed, heq, List.cons_append, List.headD_cons] using hp

end VV.P5Buffer
