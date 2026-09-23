import VV.P5Synchronize
import VV.P5Period

/-! Synchronization after the independent finite prefixes of neighboring
continued-fraction tails have been removed. -/

open Filter

namespace VV.P5TailAlignment
open P5Synchronize P5Period

theorem alignment_of_tailEquivalent {A : Type} (value : A → ℤ)
    {y z : ℝ} (h : TailEquivalent y z) (input : ℕ → A) (M : ℕ)
    (hdigits : ∀ n, partialQuotient z (M + n) = value (input n)) :
    ∃ a b : ℕ, ∀ k, partialQuotient y (a + k) = value (input (b + k)) := by
  obtain ⟨m,n,h⟩ := h
  refine ⟨m + M + 1,n + 1,fun k => ?_⟩
  have he := h (M + k)
  calc
    partialQuotient y (m + M + 1 + k) = partialQuotient z (M + (n + 1 + k)) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
    _ = _ := hdigits (n + 1 + k)

theorem digitBlock_eq_map_inputBlock {A : Type} (value : A → ℤ)
    (y : ℝ) (input : ℕ → A) (a b : ℕ)
    (halign : ∀ k, partialQuotient y (a + k) = value (input (b + k))) (k len : ℕ) :
    digitBlock y (a + k) len = (inputBlock input (b + k) len).map value := by
  induction len generalizing k with
  | zero => rfl
  | succ len ih =>
    simp only [digitBlock, inputBlock, List.map_cons, halign k]
    have h := ih (k + 1)
    simpa only [Nat.add_assoc] using congrArg (List.cons (value (input (b + k)))) h

theorem emitted_word_eq_inputBlock {A : Type} (value : A → ℤ)
    (hinj : Function.Injective value) (y : ℝ) (input : ℕ → A) (a b pos : ℕ)
    (halign : ∀ k, partialQuotient y (a + k) = value (input (b + k)))
    (hpos : a ≤ pos) (w : List A)
    (hw : w.map value = digitBlock y pos w.length) :
    w = inputBlock input (b + (pos - a)) w.length := by
  apply List.map_injective_iff.mpr hinj
  rw [hw]
  have h := digitBlock_eq_map_inputBlock value y input a b halign (pos - a) w.length
  simpa only [Nat.add_sub_of_le hpos] using h

/-- Independent tail cutoffs can be aligned before taking a synchronized
lift. Only cofinality of the two cumulative output positions is required;
there is no assumption of a common cutoff for all dyadic layers. -/
theorem eventually_trace_lift {V A : Type} (s : Step V A)
    (value : A → ℤ) (hinj : Function.Injective value)
    (input li ri : ℕ → A) (state ls rs : ℕ → V)
    (left right ll lr rl rr : ℕ → List A)
    (ht : Trace s input state left right)
    (hlt : Trace s li ls ll lr) (hrt : Trace s ri rs rl rr)
    (y z : ℝ) (L R : ℕ → ℕ) (a b c d : ℕ)
    (hal : ∀ k, partialQuotient y (a + k) = value (li (b + k)))
    (har : ∀ k, partialQuotient z (c + k) = value (ri (d + k)))
    (hL : ∀ n, L (n + 1) = L n + (left n).length)
    (hR : ∀ n, R (n + 1) = R n + (right n).length)
    (hLc : Tendsto L atTop atTop) (hRc : Tendsto R atTop atTop)
    (hleft : ∀ n, (left n).map value = digitBlock y (L n) (left n).length)
    (hright : ∀ n, (right n).map value = digitBlock z (R n) (right n).length) :
    ∃ N : ℕ, ∃ combined : ℕ → V × V × V,
      Trace (lift s) (fun n => input (N + n)) combined
        (fun n => left (N + n)) (fun n => right (N + n)) := by
  have hlEventually : ∀ᶠ n in atTop, a ≤ L n := hLc.eventually (eventually_ge_atTop a)
  have hrEventually : ∀ᶠ n in atTop, c ≤ R n := hRc.eventually (eventually_ge_atTop c)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlEventually.and hrEventually)
  let L' := fun n => b + (L (N + n) - a)
  let R' := fun n => d + (R (N + n) - c)
  have hshift : Trace s (fun n => input (N + n)) (fun n => state (N + n))
      (fun n => left (N + n)) (fun n => right (N + n)) := by
    intro n
    simpa only [Nat.add_assoc] using ht (N + n)
  have hL' : ∀ n, L' (n + 1) = L' n + (left (N + n)).length := by
    intro n
    have h := hL (N + n)
    simp only [Nat.add_assoc] at h
    have hb := (hN (N + n) (by omega)).1
    dsimp [L']
    omega
  have hR' : ∀ n, R' (n + 1) = R' n + (right (N + n)).length := by
    intro n
    have h := hR (N + n)
    simp only [Nat.add_assoc] at h
    have hb := (hN (N + n) (by omega)).2
    dsimp [R']
    omega
  have hleft' : ∀ n, left (N + n) = inputBlock li (L' n) (left (N + n)).length := by
    intro n
    exact emitted_word_eq_inputBlock value hinj y li a b (L (N + n)) hal
      (hN (N + n) (by omega)).1 _ (hleft (N + n))
  have hright' : ∀ n, right (N + n) = inputBlock ri (R' n) (right (N + n)).length := by
    intro n
    exact emitted_word_eq_inputBlock value hinj z ri c d (R (N + n)) har
      (hN (N + n) (by omega)).2 _ (hright (N + n))
  refine ⟨N,fun n => (state (N + n),ls (L' n),rs (R' n)),?_⟩
  exact trace_lift s _ li ri _ ls rs _ _ ll lr rl rr hshift hlt hrt L' R'
    hL' hR' hleft' hright'

end VV.P5TailAlignment
