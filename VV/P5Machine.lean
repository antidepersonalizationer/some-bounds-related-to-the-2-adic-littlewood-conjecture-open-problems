import VV.P5Stream
import VV.P5Synchronize

namespace VV.P5Machine
open Hurwitz P5Buffer P5Cursor P5RealCursor P5Period P5Stream
variable {C : ℕ}

abbrev Alphabet (C : ℕ) := Fin C
abbrev BCursor (C : ℕ) := State × Fin C × Bool
abbrev Pair (C : ℕ) := {p : BCursor C × BCursor C // p.1.1 ≠ p.2.1}

def digitValue {C : ℕ} (a : Alphabet C) : ℤ := a.val + 1

def cursorValue (c : BCursor C) : Cursor := ⟨c.1, ⟨digitValue c.2.1, c.2.2⟩⟩

def encodeDigit (d : ℤ) (h : 1 ≤ d ∧ d ≤ (C : ℤ)) : Alphabet C :=
  ⟨(d - 1).toNat, by omega⟩

@[simp] theorem digitValue_encode (d : ℤ) (h : 1 ≤ d ∧ d ≤ (C : ℤ)) :
    digitValue (encodeDigit d h) = d := by
  dsimp [digitValue, encodeDigit]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

@[simp] theorem digitValue_pos (d : Alphabet C) : 0 < digitValue d := by
  dsimp [digitValue]
  omega

@[simp] theorem digitValue_le (d : Alphabet C) : digitValue d ≤ C := by
  dsimp [digitValue]
  have := d.isLt
  omega

def encodeCursor (c : Cursor) (h : 0 < c.buffer.last ∧ c.buffer.last ≤ (C : ℤ)) : BCursor C :=
  (c.state, encodeDigit c.buffer.last ⟨h.1,h.2⟩,c.buffer.zero)

@[simp] theorem cursorValue_encode (c : Cursor)
    (h : 0 < c.buffer.last ∧ c.buffer.last ≤ (C : ℤ)) :
    cursorValue (encodeCursor c h) = c := by
  cases c
  simp [cursorValue, encodeCursor]

@[simp] theorem cursorValue_positive (c : BCursor C) : 0 < (cursorValue c).buffer.last :=
  digitValue_pos c.2.1

@[simp] theorem cursorValue_bounded (c : BCursor C) : (cursorValue c).buffer.last ≤ C :=
  digitValue_le c.2.1

def BoundedWord (C : ℕ) (w : List ℤ) := ∀ a ∈ w, 1 ≤ a ∧ a ≤ (C : ℤ)

instance (C : ℕ) (w : List ℤ) : Decidable (BoundedWord C w) := by
  unfold BoundedWord
  infer_instance

def encodeWord (w : List ℤ) (h : BoundedWord C w) : List (Alphabet C) :=
  w.attach.map fun a => encodeDigit a.val (h a.val a.property)

@[simp] theorem decode_encodeWord (w : List ℤ) (h : BoundedWord C w) :
    (encodeWord w h).map digitValue = w := by
  simp [encodeWord, List.map_map]


def step (C : ℕ) : P5Synchronize.Step (Pair C) (Alphabet C) := fun v a =>
  let l := tick (cursorValue v.val.1) (digitValue a)
  let r := tick (cursorValue v.val.2) (digitValue a)
  if h : 0 < l.2.buffer.last ∧ l.2.buffer.last ≤ (C : ℤ) ∧
      0 < r.2.buffer.last ∧ r.2.buffer.last ≤ (C : ℤ) ∧
      BoundedWord C l.1 ∧ BoundedWord C r.1 then
    some (⟨(encodeCursor l.2 ⟨h.1,h.2.1⟩,
      encodeCursor r.2 ⟨h.2.2.1,h.2.2.2.1⟩),
      by
        change next v.val.1.1 (digitValue a) ≠ next v.val.2.1 (digitValue a)
        exact fun he => v.property (next_injective _ he)⟩,
      encodeWord l.1 h.2.2.2.2.1,encodeWord r.1 h.2.2.2.2.2)
  else none

/-- The only rejection conditions are explicit bounds on two finite words
and two pending digits. Every successful transition is the real machine. -/
theorem step_of_bounds (v : Pair C) (a : Alphabet C)
    (hl : (tick (cursorValue v.val.1) (digitValue a)).2.buffer.last ≤ C)
    (hr : (tick (cursorValue v.val.2) (digitValue a)).2.buffer.last ≤ C)
    (hlw : BoundedWord C (tick (cursorValue v.val.1) (digitValue a)).1)
    (hrw : BoundedWord C (tick (cursorValue v.val.2) (digitValue a)).1) :
    ∃ t : Pair C × List (Alphabet C) × List (Alphabet C), step C v a = some t ∧
      cursorValue t.1.val.1 = (tick (cursorValue v.val.1) (digitValue a)).2 ∧
      cursorValue t.1.val.2 = (tick (cursorValue v.val.2) (digitValue a)).2 ∧
      t.2.1.map digitValue = (tick (cursorValue v.val.1) (digitValue a)).1 ∧
      t.2.2.map digitValue = (tick (cursorValue v.val.2) (digitValue a)).1 := by
  have hpl := (tick_positive (cursorValue v.val.1) (cursorValue_positive _)
    (digitValue a) (digitValue_pos a)).2
  have hpr := (tick_positive (cursorValue v.val.2) (cursorValue_positive _)
    (digitValue a) (digitValue_pos a)).2
  unfold step
  dsimp only
  rw [dif_pos (And.intro hpl (And.intro hl (And.intro hpr (And.intro hr (And.intro hlw hrw)))))]
  exact ⟨_,rfl,by simp,by simp,by simp,by simp⟩

def encodePair (c d : Cursor) (hd : c.state ≠ d.state)
    (hc : 0 < c.buffer.last ∧ c.buffer.last ≤ (C : ℤ))
    (hd' : 0 < d.buffer.last ∧ d.buffer.last ≤ (C : ℤ)) : Pair C :=
  ⟨(encodeCursor c hc, encodeCursor d hd'),hd⟩

@[simp] theorem encodePair_left (c d : Cursor) (hd : c.state ≠ d.state)
    (hc : 0 < c.buffer.last ∧ c.buffer.last ≤ (C : ℤ))
    (hd' : 0 < d.buffer.last ∧ d.buffer.last ≤ (C : ℤ)) :
    cursorValue (encodePair c d hd hc hd').val.1 = c := cursorValue_encode c hc

@[simp] theorem encodePair_right (c d : Cursor) (hd : c.state ≠ d.state)
    (hc : 0 < c.buffer.last ∧ c.buffer.last ≤ (C : ℤ))
    (hd' : 0 < d.buffer.last ∧ d.buffer.last ≤ (C : ℤ)) :
    cursorValue (encodePair c d hd hc hd').val.2 = d := cursorValue_encode d hd'

theorem step_encode (c d : Cursor) (a : ℤ) (hdis : c.state ≠ d.state)
    (hc : 0 < c.buffer.last ∧ c.buffer.last ≤ (C : ℤ))
    (hd : 0 < d.buffer.last ∧ d.buffer.last ≤ (C : ℤ))
    (ha : 1 ≤ a ∧ a ≤ (C : ℤ))
    (hc' : 0 < (tick c a).2.buffer.last ∧ (tick c a).2.buffer.last ≤ (C : ℤ))
    (hd' : 0 < (tick d a).2.buffer.last ∧ (tick d a).2.buffer.last ≤ (C : ℤ))
    (hwc : BoundedWord C (tick c a).1) (hwd : BoundedWord C (tick d a).1) :
    step C (encodePair c d hdis hc hd) (encodeDigit a ha) =
      some (encodePair (tick c a).2 (tick d a).2
        (fun he => hdis (next_injective a he)) hc' hd',
        encodeWord (tick c a).1 hwc, encodeWord (tick d a).1 hwd) := by
  unfold step
  simp only [encodePair_left, encodePair_right, digitValue_encode]
  rw [dif_pos ⟨hc'.1,hc'.2,hd'.1,hd'.2,hwc,hwd⟩]
  rfl

def pairEquiv (C : ℕ) : Pair C ≃
    {p : State × State // p.1 ≠ p.2} × (Fin C × Bool) × (Fin C × Bool) where
  toFun p := (⟨(p.val.1.1,p.val.2.1),p.property⟩,p.val.1.2,p.val.2.2)
  invFun p := ⟨((p.1.val.1,p.2.1),(p.1.val.2,p.2.2)),p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The reconstructed base automaton has exactly the original 24 C² formal
states: six ordered unequal arithmetic states and two 2C-state buffers. -/
theorem card_pair (C : ℕ) : Fintype.card (Pair C) = 24 * C ^ 2 := by
  have hs : Fintype.card {p : State × State // p.1 ≠ p.2} = 6 := by decide
  rw [Fintype.card_congr (pairEquiv C)]
  simp only [Fintype.card_prod,hs,Fintype.card_fin,Fintype.card_bool]
  ring

theorem card_pair_ten : Fintype.card (Pair 10) = 2400 := by
  exact (card_pair 10).trans (by norm_num)

end VV.P5Machine






